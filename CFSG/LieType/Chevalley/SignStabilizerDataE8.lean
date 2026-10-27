module

public import Certificates.Certificate3952

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem e8SignOrbit_check :
    OrbitCheck .E8 e8SignReps e8SignOrbit :=
  Certificates.certificate3952.1

theorem e8SignStab0_check :
    e8SignStab0.check e8Certificate = true :=
  Certificates.certificate3952.2.1

theorem e8SignStab0_passing :
    (e8SignStab0.passing e8Certificate).length ≤ 1 :=
  Certificates.certificate3952.2.2.1

theorem e8SignStab1_check :
    e8SignStab1.check e8Certificate = true :=
  Certificates.certificate3952.2.2.2.1

theorem e8SignStab1_passing :
    (e8SignStab1.passing e8Certificate).length ≤ 1 :=
  Certificates.certificate3952.2.2.2.2.1

theorem e8SignStab2_check :
    e8SignStab2.check e8Certificate = true :=
  Certificates.certificate3952.2.2.2.2.2.1

theorem e8SignStab2_passing :
    (e8SignStab2.passing e8Certificate).length ≤ 1 :=
  Certificates.certificate3952.2.2.2.2.2.2

theorem card_kernelPosStabilizer_le_E8 :
    ∀ ρ < e8SignReps.length,
    Nat.card (kernelPosStabilizer (maskChar (τ := .E8) (listMask (e8SignReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact (StabCert.card_kernelPosStabilizer_le e8Certificate_check e8SignStab0_check).trans
      e8SignStab0_passing
  · exact (StabCert.card_kernelPosStabilizer_le e8Certificate_check e8SignStab1_check).trans
      e8SignStab1_passing
  · exact (StabCert.card_kernelPosStabilizer_le e8Certificate_check e8SignStab2_check).trans
      e8SignStab2_passing

end CFSG.LieType.Chevalley
