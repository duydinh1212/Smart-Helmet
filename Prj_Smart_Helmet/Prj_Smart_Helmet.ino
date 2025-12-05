//////////// CONTACT EMAIL:" duydinh1204@gmail.com" ////
#include <WiFi.h>
#include <FirebaseESP32.h>
#include <Wire.h>
#include <HardwareSerial.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <TinyGPS++.h>
#include <cmath>
#include <Adafruit_Sensor.h>
#include <DHT.h>
#include <Preferences.h>
// ---DEFINE wifi your name----
#define WIFI_SSID "Helmet_Smart"
//---- define firebase -------
#define API_KEY "*****"
#define USER_EMAIL "*****"
#define USER_PASSWORD "*****"
#define DATABASE_URL "*****"
// ---- define LCD ----
#define SCREEN_WIDTH 128
#define SCREEN_HEIGHT 64
// ---define MPU--
#define MPU6500_ADDR 0x68
#define ACCEL_XOUT_H 0x3B
#define GYRO_XOUT_H 0x43
#define ACCEL_SENSITIVITY 16384.0
#define GYRO_SENSITIVITY 131.0
// Chân I2C cho OLED và MPU6500
#define SDA_PIN 23
#define SCL_PIN 25
// Chân cho TTP229
#define TTP_SCL 18  // Clock do ESP32 tạo
#define TTP_SDO 19  // Data từ TTP229
// Chân cho module sim
#define SIM_RX 16  // ESP32 nhận dữ liệu từ SIM (TX SIM)
#define SIM_TX 17  // ESP32 gửi dữ liệu tới SIM (RX SIM)
// --- Cấu hình chân GPS ---
#define GPS_RX 26  // ESP32 nhận dữ liệu từ TX của GPS
#define GPS_TX 27  // ESP32 gửi dữ liệu (nếu cần) tới RX của GPS
// Chân cảm hồng ngoại
#define IR_PIN 15
// Chân cảm biến SR-04
#define TRIG_PIN 14
#define ECHO_PIN 13
// Chân led cảnh báo vật cản
#define LED_PIN 2
// Chân Buzzer
#define buzz 21
// CAU HINH DHT22
#define DHTPIN 4
#define DHTTYPE DHT22
DHT dht(DHTPIN, DHTTYPE);
// CAU HINH MQ-3
#define MQ3_PIN 34
// ================== NGƯỠNG PHÁT HIỆN HIC15 ==================
#define HIC_THRESHOLD 100    // Ngưỡng HIC báo động Tương đương với mức AIS+3
#define TRIGGER_G_FORCE 20   // Ngưỡng 5G~~50m/s^2 để bắt đầu ghi
#define SAMPLE_RATE_HZ 1000  // Lấy mẫu x00Hz
#define SAMPLE_INTERVAL_US (1000000 / SAMPLE_RATE_HZ)
#define HIC_WINDOW_MS 15
#define EVENT_BUFFER_MS 200

#define HIC_WINDOW_SIZE (SAMPLE_RATE_HZ * HIC_WINDOW_MS / 1000)
#define EVENT_BUFFER_SIZE (SAMPLE_RATE_HZ * EVENT_BUFFER_MS / 1000)

Preferences preferences;
FirebaseData fbdo;
FirebaseData stream;
FirebaseAuth auth;
FirebaseConfig config;

// Biến Firebase cũ để so sánh thay đổi
String fb_phone_old = "";
bool fb_accident_old = false;
bool fb_gps_request_old = false;
// Biến Firebase mới
String fb_phone_new = "";
bool fb_accident_new = false;
bool fb_gps_request_new = false;
TinyGPSPlus gps;                // Tạo đối tượng GPS
HardwareSerial gpsSerial(2);    // Sử dụng UART2 cho GPS (Serial2)
const float G_ACCEL = 9.80665;  // m/s²
// Biến MPU6500
int16_t ax, ay, az, gx, gy, gz;
// ============= NGƯỠNG PHÁT HIỆN TAI NẠN =============
const float IMPACT_ACCEL_THRESHOLD_G = 3;  // 3g ~29.4 m/s²
const float TILT_ANGLE_THRESHOLD_DEG = 75.0;
const int TILT_DURATION_MS = 5000;  // Thời gian mà xe phải nghiêng quá lâu (5 giây).
float eventBuffer[EVENT_BUFFER_SIZE];
int eventBufferIndex = 0;
bool isRecording = false;
unsigned long lastSampleTime = 0;
float maxHIC = 0.0;
float currentVelocity = 0;
bool lock_key = false;  //Biến lock phím
bool tt_doi = false;
// Biến được chia sẻ giữa Task (Lõi 0) và Loop (Lõi 1)
volatile float absoluteRoll = 0.0;
volatile float pitch = 0.0;
volatile unsigned long tiltStartTime = 0;  //Biến lưu trữ thời gian bắt đầu khi xe nghiêng quá mức
volatile bool accidentDetected = false;    //Biến phát hiện tai nạn
Adafruit_SSD1306 display(SCREEN_WIDTH, SCREEN_HEIGHT, &Wire, -1);
HardwareSerial sim(1);    // UART1
String phoneNumber = "";  // Biến lưu số điện thoại nhập từ bàn phím
const int MAX_LENGTH = 11;
bool wifiConnected = false;
unsigned long lastSend = 0;
unsigned long lastSend_sdt = 0;
bool accidentDetected_fb = false;
// SR-04
long distanceCm;
volatile long g_pulseStartTime = 0;            // Thời điểm bắt đầu xung ECHO (us)
volatile long g_pulseDuration = 0;             // Thời gian của xung ECHO (us)
volatile bool g_newDistanceAvailable = false;  // Cờ báo có dữ liệu mới
// Biến cho bộ đếm thời gian (trigger)
unsigned long g_lastTriggerTime = 0;
const long TRIGGER_INTERVAL_MS = 100;  // Trigger cảm biến mỗi 100ms
// ==========  KÍCH HOẠT THỔI CỒN ==========
const float NGUONG_DO_AM = 85.0;
const int THOI_GIAN_KHOI_DONG_MS = 5000;  // giây
// Tinh Chỉnh giá trị MQ-3
float mgL_global = 0;
const float R_L_LOAD = 1000.0;
const float R0_CLEAN_AIR = 8700.0;   // giá trị R được đo ở môi trường không có cồn
const float R1_DIVIDER = 2200.0;     // 2.2k
const float R2_DIVIDER = 3300.0;     // 3.3k
const float LOG_CURVE_SLOPE = -0.7;  //Hằng số được tính toán từ datasheet
const float LOG_CURVE_INTERCEPT = -0.301;
// Biến phục vụ nhấp nháy LED không dùng delay()
unsigned long previousMillis = 0;
const unsigned long blinkInterval = 500;  // 500ms
bool ledState = LOW;
bool buzzer = HIGH;
// Biến lưu dữ pass wi-fi và sdt sos
String giaTriHienTai = "";  // Biến toàn cục để giữ giá trị ĐANG NHẬP
uint16_t lastKeyState = 0;  // Biến trạng thái để chống dội phím/nhấn giữ
const char* KEY_LUU_TRU = "gia_tri_phim";
// Tạo khóa cho I2C tránh xung đột
SemaphoreHandle_t i2cMutex;  // Tạo khóa cho I2C
// Hàm xử lý ngắt SR-04
void IRAM_ATTR echo_isr() {
  // Đọc trạng thái của chân ECHO
  if (digitalRead(ECHO_PIN) == HIGH) {
    // Xung ECHO vừa bắt đầu (cạnh lên)
    g_pulseStartTime = micros();
  } else {
    // Xung ECHO vừa kết thúc (cạnh xuống)
    g_pulseDuration = micros() - g_pulseStartTime;
    g_newDistanceAvailable = true;  // Báo cho vòng lặp chính là đã có dữ liệu
  }
}

void setup() {
  Serial.begin(115200);
  sim.begin(115200, SERIAL_8N1, SIM_RX, SIM_TX);
  gpsSerial.begin(9600, SERIAL_8N1, GPS_RX, GPS_TX);
  i2cMutex = xSemaphoreCreateMutex();  // Khởi tạo Mutex
  // --- Cấu hình I2C cho OLED và MPU6500 ---
  Wire.begin(SDA_PIN, SCL_PIN);
  Wire.setClock(400000);  // set tốc độ đọc I2c lên 400khz
  // Bật MPU6500 (thoát sleep mode)
  Wire.beginTransmission(MPU6500_ADDR);
  Wire.write(0x6B);
  Wire.write(0);
  Wire.endTransmission(true);
  // --- Cấu hình TTP229 ---
  pinMode(TTP_SCL, OUTPUT);
  pinMode(TTP_SDO, INPUT);
  digitalWrite(TTP_SCL, HIGH);  // Mặc định SCL ở mức HIGH
  dht.begin();                  // Cấu hình DHT22
  // --- Khởi động OLED ---
  if (!display.begin(SSD1306_SWITCHCAPVCC, 0x3C)) {
    Serial.println("Lỗi OLED!");
    for (;;)
      ;
  }
  lcd_default();
  // Đọc giá trị ĐÃ LƯU lần trước
  phoneNumber = docGiaTriTuFlash();
  //thiết lập sim
  sim.println("AT");
  delay(500);
  sim.println("AT+CMGF=1");  // SMS text mode
  delay(500);
  sim.println("AT+CSCLK=1");  // SIM sẽ tự ngủ sau khoảng 5-10 giây không có dữ liệu qua cổng UART
  delay(500);
  pinMode(TRIG_PIN, OUTPUT);
  pinMode(ECHO_PIN, INPUT);
  pinMode(LED_PIN, OUTPUT);
  pinMode(buzz, OUTPUT);
  pinMode(IR_PIN, INPUT);
  digitalWrite(buzz, HIGH);
  attachInterrupt(digitalPinToInterrupt(ECHO_PIN), echo_isr, CHANGE);
  setCpuFrequencyMhz(160);  // set tần số MPU hoạt động ở tần số 160Mhz
  // Tạo FreeRTOS task
  xTaskCreatePinnedToCore(TaskDetectAccident, "DetectAccident", 2048, NULL, 1, NULL, 0);
}
void TaskDetectAccident(void* parameter) {
  float ax_g, ay_g, az_g;
  float totalG, totalm2s, roll;
  for (;;) {
    if (micros() - lastSampleTime >= SAMPLE_INTERVAL_US) {
      lastSampleTime = micros();
      readMPU();
      // Tính gia tốc tổng hợp (theo G)
      ax_g = ax / ACCEL_SENSITIVITY;
      ay_g = ay / ACCEL_SENSITIVITY;
      az_g = az / ACCEL_SENSITIVITY;
      totalG = sqrt(ax_g * ax_g + ay_g * ay_g + az_g * az_g);
      totalm2s = totalG * G_ACCEL;
      roll = atan2(ay_g, az_g) * 180.0 / M_PI;  // Góc nghiêng trái phải 
      absoluteRoll = abs(roll);
      pitch = atan2(-ax_g,az_g)* 180.0 / M_PI;  // Góc nghiêng trước sau
      // Ghi dữ liệu hoặc trigger
      if (isRecording) {
        recordEvent(totalm2s);
      } else if (totalm2s > TRIGGER_G_FORCE) {
        startRecording(totalm2s);
      }
    }
    vTaskDelay(1);
  }
}
// ================== FREE RTOS TASK ==================

void lcd_default() {
  if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
    display.clearDisplay();
    display.setTextSize(1);
    display.setTextColor(SSD1306_WHITE);
    display.setCursor(0, 0);
    display.println("-------- MENU -------");
    display.setCursor(0, 9);
    display.println("Nhap passwifi_sdt<11>");
    display.setCursor(0, 17);
    display.println("Xoa 1 ki tu      <12>");
    display.setCursor(0, 25);
    display.println("Xac Nhan SDT_SMS <13>");
    display.setCursor(0, 33);
    display.println("Dang nhap Wifi   <14>");
    display.setCursor(0, 41);
    display.println("Kiem Tra Con     <15>");
    display.display();
    xSemaphoreGive(i2cMutex);
  }
}

void readMPU() {
  if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {  // Chờ để lấy khóa
    Wire.beginTransmission(MPU6500_ADDR);
    Wire.write(ACCEL_XOUT_H);
    Wire.endTransmission(false);

    // Yêu cầu 14 thanh ghi liên tiếp (Accel 6 + Temp 2 + Gyro 6)
    // MPU6500 sắp xếp bộ nhớ: Accel -> Temp -> Gyro
    Wire.requestFrom(MPU6500_ADDR, 14, true);

    ax = (Wire.read() << 8) | Wire.read();
    ay = (Wire.read() << 8) | Wire.read();
    az = (Wire.read() << 8) | Wire.read();

    int16_t temp = (Wire.read() << 8) | Wire.read();  // Đọc bỏ qua hoặc dùng nếu cần

    gx = (Wire.read() << 8) | Wire.read();
    gy = (Wire.read() << 8) | Wire.read();
    gz = (Wire.read() << 8) | Wire.read();

    xSemaphoreGive(i2cMutex);  // Trả khóa sau khi dùng xong
  }
}
// ================== HÀM XỬ LÝ TAI NẠN CORE1 ==================
void startRecording(float firstG) {
  isRecording = true;
  eventBufferIndex = 0;
  memset(eventBuffer, 0, sizeof(eventBuffer));
  eventBuffer[eventBufferIndex++] = firstG;
}

void recordEvent(float gValue) {
  if (eventBufferIndex < EVENT_BUFFER_SIZE) {
    eventBuffer[eventBufferIndex++] = gValue;
  } else {
    isRecording = false;
    processHIC();
  }
}

void processHIC() {
  maxHIC = 0.0;
  float dt = (float)HIC_WINDOW_MS / 1000.0;

  for (int i = 0; i <= EVENT_BUFFER_SIZE - HIC_WINDOW_SIZE; i++) {
    float avgA = 0.0;
    for (int j = 0; j < HIC_WINDOW_SIZE; j++) avgA += eventBuffer[i + j];
    avgA /= HIC_WINDOW_SIZE;

    // HIC = Δt * a_avg^2.5 (đơn giản hóa)
    float hic = dt * pow(avgA, 2.5);
    if (hic > maxHIC) maxHIC = hic;
  }

  detectAccident();
}

void detectAccident() {
  if (maxHIC > HIC_THRESHOLD) {
    // Phát hiện tai nạn
    accidentDetected = true;
    updateVelocity();
    if (currentVelocity < 2.0) {
      Serial.println("Tai nạn xác nhận: Xe đã dừng hẳn!");
      // TODO: Gửi thông báo hoặc thực hiện hành động SOS khẩn
    } else {
      Serial.println("Va chạm nhưng xe vẫn di chuyển.");  /// cân nhắc tắt trạng thái accidentDetected
    }
  } else {
    Serial.println("Không có sự kiện nguy hiểm.");
  }
}

void updateVelocity() {
  if (gps.speed.isValid()) {
    // Lấy tốc độ theo km/h (TinyGPS++ cung cấp sẵn)
    currentVelocity = gps.speed.kmph();

    // Giới hạn để tránh nhiễu
    if (currentVelocity < 0.3) currentVelocity = 0.0;
  } else {
    // Nếu GPS chưa fix, giữ nguyên hoặc cho bằng 0
    currentVelocity = 0.0;
  }
}

// hàm con đọc data mpu và phát hiện tai nạn khi nón bị đổ
void DetectAccident_1() {
  // ==== PHÁT HIỆN TAI NẠN ====
  if (absoluteRoll >= TILT_ANGLE_THRESHOLD_DEG|| pitch >= 70 || pitch <= -55) {
    if (tiltStartTime == 0) {
      tiltStartTime = millis();
      Serial.print("-> Cảnh báo nghiêng: ");
      Serial.print(absoluteRoll);
      Serial.println(" deg");
    } else if (millis() - tiltStartTime >= TILT_DURATION_MS) {
      Serial.println("!!! TAI NẠN PHÁT HIỆN: NÓN NGHIÊNG QUÁ LÂU !!!");
      Serial.print("Góc nghiêng duy trì: ");
      Serial.print(absoluteRoll);
      Serial.println(" deg");
      accidentDetected = true;
    }
  } else {
    tiltStartTime = 0;
  }
}

//==================================================================================================//////
//====================================== VOID MAIN()=================================================//////
//====================================================================================================//////
void loop() {
  readGPS();
  if (tt_doi == true) {
    xulytainan();
    DetectAccident_1();
  }
  // ---Xử lý nút nhấn-----
  xulynutnhan1();
  // ---Xử lý tin nhắn-----
  nhantinnhan();
  // --- ktr đội nón /Đo khoảng cách và xử lý  -----
  xulykhoangcach();
}



// ==== HÀM CON  ====
// Hàm lưu giá trị vào bộ nhớ
void luuGiaTriVaoFlash(String value) {
  preferences.begin("my-app", false);
  preferences.putString(KEY_LUU_TRU, value);
  preferences.end();
  Serial.print("Da luu '");
  Serial.print(value);
  Serial.println("' vao flash!");
}
String docGiaTriTuFlash() {
  preferences.begin("my-app", false);
  String value = preferences.getString(KEY_LUU_TRU, "");
  preferences.end();
  return value;
}

// hàm con quét phím
uint16_t readKeypad() {
  uint16_t keyData = 0;
  for (int i = 0; i < 16; i++) {
    digitalWrite(TTP_SCL, LOW);
    delayMicroseconds(2);
    int bitValue = digitalRead(TTP_SDO);
    if (bitValue == 0) {
      keyData |= (1 << i);
    }
    digitalWrite(TTP_SCL, HIGH);
    delayMicroseconds(2);
  }
  return keyData;
}
// hàm con đọc trạng thái firebase

void streamCallback(StreamData data) {
  String path = data.dataPath();

  if (path == "/phonenum") {
    fb_phone_new = data.stringData();
    if (fb_phone_new != fb_phone_old) {  // So sánh SDT nếu giá trị khác sẽ cập nhật
      fb_phone_old = fb_phone_new;
      if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
        display.clearDisplay();
        display.setCursor(0, 0);
        display.println("Cap nhat sdt!");
        display.println(fb_phone_new);
        display.display();
        xSemaphoreGive(i2cMutex);
      }
      phoneNumber = fb_phone_new;
      luuGiaTriVaoFlash(phoneNumber);  // lưu số điện thoại vào bộ nhớ flash
    }
  }

  if (path == "/accidentDetected") {
    fb_accident_new = data.boolData();
    if (fb_accident_new != fb_accident_old) {
      fb_accident_old = fb_accident_new;
      Serial.print("Accident updated: ");
      Serial.println(fb_accident_new ? "TRUE" : "FALSE");
      accidentDetected = fb_accident_new;
    }
  }

  if (path == "/GPS_REQUEST") {
    fb_gps_request_new = data.boolData();
    if (fb_gps_request_new && fb_gps_request_old == false) {
      sendfb_GPS();
      Firebase.setBool(fbdo, "/Device/GPS_REQUEST", false);
    }
    fb_gps_request_old = fb_gps_request_new;
  }
}

void streamTimeoutCallback(bool timeout) {
  if (timeout) Serial.println("Stream timed out!");
}

// Đọc DATA từ Module Neo 6
void readGPS() {
  while (gpsSerial.available() > 0) {
    gps.encode(gpsSerial.read());
  }
}

// hàm con gửi GPS lên firebase
void sendfb_GPS() {
  if (gps.location.isValid()) {
    if (gps.location.isUpdated()) {
      float latitude = gps.location.lat();
      float longitude = gps.location.lng();
      float speed = gps.speed.kmph();  // tốc độ km/h
      // Gửi lên Firebase
      if (WiFi.status() == WL_CONNECTED) {
        if (Firebase.ready()) {
          Firebase.setFloat(fbdo, "/GPS/latitude", latitude);
          Firebase.setFloat(fbdo, "/GPS/longitude", longitude);
          Firebase.setFloat(fbdo, "/GPS/speed", speed);
          if (fbdo.httpCode() == 200)
            Serial.println("Gửi thành công!");
          else
            Serial.printf("Lỗi gửi: %s\n", fbdo.errorReason().c_str());
        }
      }
      delay(3000);  // gửi mỗi 3 giây
    }
  }
}

// hàm con gửi tin nhắn sms
void sendSMS(String number) {
  String message = "So dien thoai vua nhap: " + number;
  sim.println("AT");  // Đánh thức sim khi ngủ sâu
  delay(100);
  Serial.println("Dang gui SMS...");
  sim.println("AT+CMGS=\"" + number + "\"");
  delay(1000);
  sim.print(message);
  delay(500);
  sim.write(26);  // Ctrl+Z để gửi
  Serial.println("Da gui tin nhan!");
}

void nhantinnhan() {
  // đọc sms gửi tới
  if (sim.available()) {
    String sms = sim.readString();
    sms.toUpperCase();  // Viết hoa để dễ so sánh
    Serial.println("Tin nhắn nhận được:");
    Serial.println(sms);
    // Khi tin nhắn chứa "GPS"
    if (sms.indexOf("GPS") >= 0) {
      if (gps.location.isValid()) {
        String latitude = String(gps.location.lat(), 6);
        String longitude = String(gps.location.lng(), 6);
        String googleMapLink = "https://maps.google.com/?q=" + latitude + "," + longitude;
        sendSMS_GPS(phoneNumber, "Toa do hien tai:\n" + googleMapLink);
      } else {
        sendSMS_GPS(phoneNumber, "Khong co tin hieu GPS!");
      }
    }
  }
}

void call_sos(String cmd) {
  sim.println("AT");  // Đánh thức sim khi ngủ sâu
  delay(100);
  sim.println("AT");  // Gửi lại lần nữa cho chắc
  sim.println(cmd);
  Serial.println(">> " + cmd);
  if (sim.available()) Serial.write(sim.read());
  Serial.println();
}

void sendSMS_GPS(String phone, String msg) {
  sim.println("AT");  // Kích hoạt sim
  delay(100);
  sim.println("AT+CMGF=1");
  delay(500);
  sim.print("AT+CMGS=\"");
  sim.print(phone);
  sim.println("\"");
  delay(500);
  sim.print(msg);
  delay(500);
  sim.write(26);  // Ctrl+Z (kết thúc tin nhắn)
  delay(1000);
  Serial.println("Đã gửi tin nhắn phản hồi.");
}

void xulytainan() {
  int8_t tn = 0;
  while (accidentDetected) {
    accidentDetected_fb = true;
    if (WiFi.status() == WL_CONNECTED) {
      if (Firebase.ready()) {
        Firebase.setBool(fbdo, "/Device/accidentDetected", accidentDetected_fb);  // Cập nhật lại trạng thái trên firebase
      } else {
        Serial.println("Loi ket noi Firebase! không thể gửi TT tai nạn");
      }
    }
    // Gửi tin nhắn 2 lần để thông báo
    if (tn < 2) {
      tn++;
      Serial.println(">>> ĐÃ PHÁT HIỆN TAI NẠN. <<<");
      digitalWrite(buzzer, LOW);
      if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
        display.clearDisplay();
        display.setCursor(0, 0);
        display.println("CALL SOS:");
        display.setCursor(0, 16);
        display.println(phoneNumber);
        display.display();
        xSemaphoreGive(i2cMutex);  // Trả khóa ngay sau khi vẽ xong
      }
      //gửi GPS đến SDT đã nhập
      if (gps.location.isValid()) {
        String latitude = String(gps.location.lat(), 6);
        String longitude = String(gps.location.lng(), 6);
        String googleMapLink = "https://maps.google.com/?q=" + latitude + "," + longitude;
        sendSMS_GPS(phoneNumber, "SOS PHAT HIEN TAI NAN Toa do hien tai:\n" + googleMapLink);
      } else {
        sendSMS_GPS(phoneNumber, "Khong co tin hieu GPS!");
      }
    }
    call_sos("ATD" + phoneNumber + ";");  // gọi điện cảnh báo tai nạn
    ledState = !ledState;
    buzzer = !buzzer;
    digitalWrite(buzz, buzzer);
    digitalWrite(LED_PIN, ledState);
    if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
      display.clearDisplay();
      display.setCursor(0, 0);
      display.println("CALL SOS:");
      display.setCursor(0, 16);
      display.println(phoneNumber);
      display.setCursor(0, 30);
      display.println("NHAN PHIM 11 TRONG 5SNEU KHONG PHAI TAI NAN");
      display.display();
      xSemaphoreGive(i2cMutex);
    }
    // Kiểm tra nếu phát hiện tai nạn giả thì nhấn phím 11 để tắt
    uint16_t keys = readKeypad();
    if (keys == 1024)  //nhấn phím số 11 lock
    {
      delay(5000);
      keys = 0;
      uint16_t keys = readKeypad();
      if (keys == 1024) {
        call_sos("AT+CHUP");  // cúp máy
        accidentDetected_fb = false;
        if (WiFi.status() == WL_CONNECTED) {
          if (Firebase.ready()) {
            Firebase.setBool(fbdo, "/Device/accidentDetected", accidentDetected_fb);  // Cập nhật lại trạng thái trên firebase
          } else {
            Serial.println("Loi ket noi Firebase! không thể gửi TT tai nạn");
          }
        }
        accidentDetected = false;
        ledState = LOW;
        buzzer = HIGH;
        digitalWrite(buzz, buzzer);
        digitalWrite(LED_PIN, ledState);
        if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
          display.clearDisplay();
          display.setCursor(0, 0);
          display.println("QUAY LAI TRANG THAI BINH THUONG");
          display.display();
          xSemaphoreGive(i2cMutex);
        }
        delay(5000);
        display.clearDisplay();
        display.setCursor(0, 16);
        display.println("SMART HELMET");
        display.display();
      }
    }
    delay(300);
  }
}
// --- Hàm gửi xung Trigger ---
void trigger_sensor() {
  // Gửi một xung 10us để kích hoạt cảm biến
  digitalWrite(TRIG_PIN, LOW);
  delayMicroseconds(2);
  digitalWrite(TRIG_PIN, HIGH);
  delayMicroseconds(10);  // Xung 10us
  digitalWrite(TRIG_PIN, LOW);
}
void xulykhoangcach() {
  unsigned long currentMillis = millis();
  int value = digitalRead(IR_PIN);
  // Kiểm tra tt đội nón
  if (value == HIGH) {
    digitalWrite(LED_PIN, LOW);
    Serial.println("Phat hien Khong co doi non ");
    tt_doi = false;
    if (currentMillis - lastSend >= 1000) {
      lastSend = currentMillis;
      Firebase.setBool(fbdo, "/Device/helmet", tt_doi);
      if (WiFi.status() == WL_CONNECTED) {
        if (Firebase.ready()) {
          Firebase.setBool(fbdo, "/Device/helmet", tt_doi);  // gửi Trạng thái đội nón lên firebase
        } else {
          Serial.println("Loi ket noi Firebase! không thể gửi data TT_non");
        }
      }
    }
  } else {
    digitalWrite(LED_PIN, LOW);
    Serial.println("Da doi non");
    tt_doi = true;
    if (currentMillis - lastSend >= 1000) {
      lastSend = currentMillis;
      if (WiFi.status() == WL_CONNECTED) {
        if (Firebase.ready()) {
          Firebase.setBool(fbdo, "/Device/helmet", tt_doi);  // gửi Trạng thái đội nón lên firebase
        } else {
          Serial.println("Loi ket noi Firebase! không thể gửi data TT_non");
        }
      }
    }
    if (millis() - g_lastTriggerTime >= TRIGGER_INTERVAL_MS) {
      g_lastTriggerTime = millis();  // Đặt lại thời gian
      trigger_sensor();              // Gửi xung kích hoạt
    }
    if (g_newDistanceAvailable) {
      long duration_copy;  // Biến tạm để sao chép dữ liệu
      noInterrupts();
      duration_copy = g_pulseDuration;
      g_newDistanceAvailable = false;  // Đặt lại cờ
      interrupts();
      distanceCm = (duration_copy * 0.0343) / 2;
      Serial.print("Khoang cach: ");
      Serial.print(distanceCm);
      Serial.println(" cm");
    }
    // --- Kiểm tra điều kiện ---
    if (distanceCm > 0 && distanceCm < 10) {
      // Nếu khoảng cách < 10cm → nhấp nháy LED mỗi 500ms
      if (currentMillis - previousMillis >= blinkInterval) {
        previousMillis = currentMillis;
        ledState = !ledState;  // đảo trạng thái LED
        digitalWrite(LED_PIN, ledState);
      } else {
        digitalWrite(LED_PIN, ledState);
      }
    } else {
      // Nếu >= 10cm → tắt LED
      digitalWrite(LED_PIN, LOW);
    }
  }
}

void xulynutnhan1() {
  uint16_t keys = readKeypad();
  if (keys == 1024)  //nhấn phím số 11 lock- xác nhận SDT_SoS
  {
    lock_key = !lock_key;
    if (lock_key == false) {
      if (phoneNumber.length() >= 9) {
        if (millis() - lastSend_sdt >= 1000) {
          lastSend_sdt = millis();
          if (WiFi.status() == WL_CONNECTED) {
            if (Firebase.ready()) {
              Firebase.setString(fbdo, "/Device/phonenum", phoneNumber);  // gửi SDT_SOS lên firebase
            } else {
              Serial.println("Loi ket noi Firebase! không thể gửi data phone");
            }
          }
        }
        luuGiaTriVaoFlash(phoneNumber);  // lưu lại SDT_SOS khi nhấn xác nhận phím 11
        if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
          display.clearDisplay();
          display.setCursor(0, 0);
          display.println("Hoan tat nhap sdt!\n");
          display.println(phoneNumber);
          display.setCursor(0, 56);
          display.println("back menu <16>");
          display.display();
          xSemaphoreGive(i2cMutex);
        }
        delay(1000);
      } else {
        if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
          display.clearDisplay();
          display.setCursor(0, 0);
          display.println("So khong hop le!");
          display.display();
          xSemaphoreGive(i2cMutex);
        }
        lock_key = true;
        if (millis() - lastSend_sdt >= 1000) {
          lastSend_sdt = millis();
          if (WiFi.status() == WL_CONNECTED) {
            if (Firebase.ready()) {
              Firebase.setString(fbdo, "/Device/phonenum", "errol");  //
            } else {
              Serial.println("Loi ket noi Firebase! không thể gửi data phone");
            }
          }
        }
      }
    }
  }
  if (lock_key == true) {  // Nhập số điện thoại or pass_wifi
    if (keys > 0) {
      for (int i = 0; i < 16; i++) {
        if (keys & (1 << i)) {
          Serial.print("Phím: ");
          Serial.println(i + 1);
          if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
            display.clearDisplay();
            display.setCursor(0, 0);
            display.println("Nhap SDT or passWifi:");
            display.display();
            xSemaphoreGive(i2cMutex);
          }
          // xử lý từng phím
          if (i < 9) {  // Phím 1–9
            if (phoneNumber.length() < MAX_LENGTH) {
              phoneNumber += String(i + 1);
            }
          } else if (i == 9) {  // Phím 10 = số 0
            if (phoneNumber.length() < MAX_LENGTH) {
              phoneNumber += "0";
            }
          } else if (i == 11) {  // Phím 12 = xóa 1 ký tự
            if (phoneNumber.length() > 0) {
              phoneNumber.remove(phoneNumber.length() - 1);
            }
          } else if (i == 12) {  // phím 13 = GỬI SMS
            if (phoneNumber.length() >= 9) {
              sendSMS(phoneNumber);
              if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
                display.clearDisplay();
                display.setCursor(0, 0);
                display.println("Da gui SMS toi:");
                display.println(phoneNumber);
                display.display();
                xSemaphoreGive(i2cMutex);
              }
              delay(2000);
              display.clearDisplay();
            } else {
              if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
                display.clearDisplay();
                display.setCursor(0, 0);
                display.println("So khong hop le!");
                display.display();
                xSemaphoreGive(i2cMutex);
              }
              delay(2000);
            }
          }
          Serial.println("So dien thoai: " + phoneNumber);
          display.setCursor(0, 16);
          display.println(phoneNumber);
          display.setCursor(0, 56);
          display.println("back menu <16>");
          display.display();
          delay(200);  // Tránh đọc lặp khi giữ phím
        }
      }
    }
  }
  if (keys == 8192) {  //nhấn phím 14 để đổi pass wifi là SDT_SOS
    if (wifiConnected == false) {
      WiFi.begin(WIFI_SSID, phoneNumber.c_str());
      unsigned long start = millis();
      while (WiFi.status() != WL_CONNECTED && millis() - start < 15000) {
        Serial.print(".");
        delay(500);
        if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
          display.clearDisplay();
          display.setCursor(0, 0);
          display.println("...Connecting....");
          display.display();
          xSemaphoreGive(i2cMutex);
        }
      }
      if (WiFi.status() == WL_CONNECTED) {
        Serial.println("Da ket noi WiFi!");
        Serial.println("Connected to Wi-Fi");
        if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
          display.clearDisplay();
          display.setCursor(0, 0);
          display.println("CONNECT WIFI SUCCESS!");
          display.setCursor(0, 56);
          display.println("back menu <16>");
          display.display();
          xSemaphoreGive(i2cMutex);
        }
        wifiConnected = true;  // Đặt cờ báo đã kết nối thành công
        config.api_key = API_KEY;
        config.database_url = DATABASE_URL;
        auth.user.email = USER_EMAIL;
        auth.user.password = USER_PASSWORD;
        Firebase.begin(&config, &auth);
        Firebase.reconnectWiFi(true);
        if (!Firebase.beginStream(stream, "/Device")) {
          Serial.println("Loi stream Firebase!");
        }
        Firebase.setStreamCallback(stream, streamCallback, streamTimeoutCallback);
      } else {
        Serial.println("Ket noi that bai! Vui long nhap lai.");
        if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
          display.clearDisplay();
          display.setCursor(0, 0);
          display.println("Ket noi that bai! Vui long nhap lai.");
          display.setCursor(0, 56);
          display.println("back menu <16>");
          display.display();
          xSemaphoreGive(i2cMutex);
        }
      }
    }
  }
  if (keys == 16384) {  //nhấn phím 15 để test cồn_gửi data lên firebase
    kiemtraDocon();
    if (WiFi.status() == WL_CONNECTED) {
      if (Firebase.ready()) {
        Firebase.setFloat(fbdo, "/MQ3/mgL_global", mgL_global);  // gửi data MQ3 lên firebase
      } else {
        Serial.println("Loi ket noi Firebase! không thể gửi data mq3");
      }
    }
  }
  if (keys == 32768) {
    lcd_default();
    delay(500);
  }
}

void kiemtraDocon() {
  // 1. Doc do am tu DHT22
  float h = dht.readHumidity();
  if (isnan(h)) {
    Serial.println("Loi doc tu cam bien DHT22!");
    display.setCursor(0, 20);
    display.println("fall sennor dht22");
    display.display();
    delay(2000);
  }
  Serial.print("Trang thai cho... Do am hien tai: ");
  Serial.print(h);
  Serial.println(" %");
  if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
    display.clearDisplay();
    display.setCursor(0, 0);
    display.println("Vui Long Thoi Con...");
    display.display();
    xSemaphoreGive(i2cMutex);
  }
  delay(4000);
  if (h > NGUONG_DO_AM) {
    Serial.println("--------------------------------------");
    Serial.println("!!! PHAT HIEN HOI THO (Do am > ");
    Serial.print(NGUONG_DO_AM);
    Serial.println(" %)");
    Serial.println("======> BAT DAU DOC NONG DO CON <======");
    if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
      display.clearDisplay();
      display.setCursor(0, 15);
      display.println("BAT DAU THOI!");
      display.setCursor(0, 20);
      display.println("Thoi lien tuc 5s...");
      display.display();
      xSemaphoreGive(i2cMutex);
    }
    docNongDoCon();
    Serial.println("--------------------------------------");
    Serial.println("\nHoan tat do. Vui long cho 5 giay de cam bien on dinh lai...");
    delay(5000);
    Serial.println("SAN SANG. Vui long thoi vao cam bien.");
  } else {
    if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
      display.clearDisplay();
      display.setCursor(0, 0);
      display.println("Vui Long Thoi Lai!");
      display.setCursor(0, 15);
      display.println("Nhan Phim 15 Thoi lai!");
      display.display();
      xSemaphoreGive(i2cMutex);
    }
    delay(500);  // Tránh spam nút nhấn
  }
}
/**
 * @brief Tinh toan Rs, ty le (Ratio) va nong do (mg/L)
 */
void docNongDoCon() {
  long tongGiaTriADC = 0;
  int soLanDoc = 5;

  Serial.println("Dang lay mau...");

  for (int i = 0; i < soLanDoc; i++) {
    tongGiaTriADC += analogRead(MQ3_PIN);
    delay(200);
  }
  float adcTrungBinh = (float)tongGiaTriADC / soLanDoc;
  float v_out_esp32 = adcTrungBinh * (3.3 / 4095.0);
  float v_out_mq3 = v_out_esp32 * ((R1_DIVIDER + R2_DIVIDER) / R2_DIVIDER);
  if (v_out_mq3 < 0.01) v_out_mq3 = 0.01;
  float Rs = ((5.0 - v_out_mq3) * R_L_LOAD) / v_out_mq3;
  float ratio = Rs / R0_CLEAN_AIR;
  mgL_global = pow(10, ((log10(ratio) - LOG_CURVE_INTERCEPT) / LOG_CURVE_SLOPE));
  Serial.println("----------- KET QUA -----------");
  Serial.print("Gia tri ADC trung binh: ");
  Serial.println(adcTrungBinh, 2);
  Serial.print("Dien ap ESP32 (V): ");
  Serial.println(v_out_esp32, 3);
  Serial.print("Dien ap MQ-3 (V): ");
  Serial.println(v_out_mq3, 3);
  Serial.print("Gia tri Rs (Ohm): ");
  Serial.println(Rs, 2);
  Serial.print("Ty le (Rs/R0): ");
  Serial.println(ratio, 4);
  Serial.println("---------------------------------");
  Serial.print("==> NONG DO CON (mg/L): ");
  if (mgL_global < 0.05) {  // Dat mot nguong san
    Serial.println("~0.00 mg/L (Khong phat hien)");
    if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
      display.clearDisplay();
      display.setCursor(0, 0);
      display.println("Khong Phat Hien Con");  // Nếu không phát hiện sẽ thoát khỏi kiểm tra cồn
      display.display();
      xSemaphoreGive(i2cMutex);
    }
  } else {
    Serial.print(mgL_global, 3);
    Serial.println(" mg/L");
    if (xSemaphoreTake(i2cMutex, portMAX_DELAY) == pdTRUE) {
      display.clearDisplay();
      display.setCursor(0, 0);
      display.println("Phat Hien Co Con");
      display.setCursor(0, 15);  // Xử lý khi phát hiện cồn trên ngưỡng đã hiệu chuẩn
      display.println("Nong Do Con khoang:");
      display.print(mgL_global, 3);
      display.println(" mg/L");
      display.display();
      xSemaphoreGive(i2cMutex);
    }
  }
}
