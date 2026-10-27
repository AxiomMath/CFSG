module

public import Certificates.Certificate3951

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem closureCheck_E8_0_lo :
    closureCheck .E8 ⟨0, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.1.1

theorem closureCheck_E8_0_hi :
    closureCheck .E8 ⟨0, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.1.2

theorem closureCheck_E8_1_lo :
    closureCheck .E8 ⟨1, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.2.1.1

theorem closureCheck_E8_1_hi :
    closureCheck .E8 ⟨1, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.2.1.2

theorem closureCheck_E8_2_lo :
    closureCheck .E8 ⟨2, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.2.2.1.1

theorem closureCheck_E8_2_hi :
    closureCheck .E8 ⟨2, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.2.2.1.2

theorem closureCheck_E8_3_lo :
    closureCheck .E8 ⟨3, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.2.2.2.1.1

theorem closureCheck_E8_3_hi :
    closureCheck .E8 ⟨3, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.2.2.2.1.2

theorem closureCheck_E8_4_lo :
    closureCheck .E8 ⟨4, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.2.2.2.2.1.1

theorem closureCheck_E8_4_hi :
    closureCheck .E8 ⟨4, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.2.2.2.2.1.2

theorem closureCheck_E8_5_lo :
    closureCheck .E8 ⟨5, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.2.2.2.2.2.1.1

theorem closureCheck_E8_5_hi :
    closureCheck .E8 ⟨5, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.2.2.2.2.2.1.2

theorem closureCheck_E8_6_lo :
    closureCheck .E8 ⟨6, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.2.2.2.2.2.2.1.1

theorem closureCheck_E8_6_hi :
    closureCheck .E8 ⟨6, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.2.2.2.2.2.2.1.2

theorem closureCheck_E8_7_lo :
    closureCheck .E8 ⟨7, by decide⟩ 0 120 = true :=
  Certificates.certificate3951.1.2.2.2.2.2.2.2.1

theorem closureCheck_E8_7_hi :
    closureCheck .E8 ⟨7, by decide⟩ 120 240 = true :=
  Certificates.certificate3951.1.2.2.2.2.2.2.2.2

theorem negCheck_E8 :
    negCheck .E8 = true :=
  Certificates.certificate3951.2.1

theorem tableCheck_E8 :
    tableCheck .E8 = true :=
  Certificates.certificate3951.2.2.1

theorem sizeCheck_E8_0 :
    sizeCheck .E8 0 = true :=
  Certificates.certificate3951.2.2.2.1

theorem sizeCheck_E8_1 :
    sizeCheck .E8 1 = true :=
  Certificates.certificate3951.2.2.2.2.1

theorem sizeCheck_E8_2 :
    sizeCheck .E8 2 = true :=
  Certificates.certificate3951.2.2.2.2.2

theorem closureOK_E8 : ClosureOK .E8 := by
  intro i m n hm hn
  have hN : Tag.E8.rootCertificate.roots.length = 240 := by decide +kernel
  rw [hN] at hm
  rcases Nat.lt_or_ge m 120 with h | h
  · fin_cases i
    · exact closureCheck_spec closureCheck_E8_0_lo (Nat.zero_le m) h hn
    · exact closureCheck_spec closureCheck_E8_1_lo (Nat.zero_le m) h hn
    · exact closureCheck_spec closureCheck_E8_2_lo (Nat.zero_le m) h hn
    · exact closureCheck_spec closureCheck_E8_3_lo (Nat.zero_le m) h hn
    · exact closureCheck_spec closureCheck_E8_4_lo (Nat.zero_le m) h hn
    · exact closureCheck_spec closureCheck_E8_5_lo (Nat.zero_le m) h hn
    · exact closureCheck_spec closureCheck_E8_6_lo (Nat.zero_le m) h hn
    · exact closureCheck_spec closureCheck_E8_7_lo (Nat.zero_le m) h hn
  · fin_cases i
    · exact closureCheck_spec closureCheck_E8_0_hi h hm hn
    · exact closureCheck_spec closureCheck_E8_1_hi h hm hn
    · exact closureCheck_spec closureCheck_E8_2_hi h hm hn
    · exact closureCheck_spec closureCheck_E8_3_hi h hm hn
    · exact closureCheck_spec closureCheck_E8_4_hi h hm hn
    · exact closureCheck_spec closureCheck_E8_5_hi h hm hn
    · exact closureCheck_spec closureCheck_E8_6_hi h hm hn
    · exact closureCheck_spec closureCheck_E8_7_hi h hm hn

theorem sizesOK_E8 : SizesOK .E8 := by
  intro r hr
  have hl : (pairTable .E8).length = 3 := by decide
  rw [hl] at hr
  interval_cases r
  · exact sizeCheck_E8_0
  · exact sizeCheck_E8_1
  · exact sizeCheck_E8_2

end CFSG.LieType.Chevalley.RootOps
