
module

public import CFSG.GF2Type.Widths1112.Co2FormsBase

public import Certificates.Certificate38952

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native
  CFSG.GF2W1112 Matrix

theorem q₀₂_co2Act
    (g : NativeSporadic.Co2) (v : Vec22) : q₀₂ (co2Act g v) = q₀₂ v :=
  Certificates.certificate38952.1 g v

theorem bil₀₂_co2Act
    (g : NativeSporadic.Co2) (u v : Vec22) : bil₀₂ (co2Act g u) (co2Act g v) = bil₀₂ u v := by
  rw [← polar_q₀₂ (co2Act g u) (co2Act g v), ← polar_q₀₂ u v, ← co2Act_add, q₀₂_co2Act,
    q₀₂_co2Act, q₀₂_co2Act]

theorem co2_dual_fixed_zero {c : Vec22}
    (h : ∀ (g : NativeSporadic.Co2) (v : Vec22), c ⬝ᵥ co2Act g v = c ⬝ᵥ v) : c = 0 :=
  Certificates.certificate38952.2.2.1 c h

theorem co2_dual_fixed_stab {c : Vec22}
    (h : ∀ g : NativeSporadic.Co2,
      co2Act g (toVecD 22 (w12Co2Rep 0)) = toVecD 22 (w12Co2Rep 0) →
        ∀ v : Vec22, c ⬝ᵥ co2Act g v = c ⬝ᵥ v) :
    c = 0 ∨ ∀ v : Vec22, c ⬝ᵥ v = bil₀₂ (toVecD 22 (w12Co2Rep 0)) v :=
  Certificates.certificate38952.2.2.2.1 c h

theorem co2_rep_singular {i : ℕ} (hi : i < 3) :
    toVecD 22 (w12Co2Rep i) ≠ 0 ∧ q₀₂ (toVecD 22 (w12Co2Rep i)) = 0 :=
  Certificates.certificate38952.2.2.2.2 i hi

end CFSG.GF2Type.Widths1112
