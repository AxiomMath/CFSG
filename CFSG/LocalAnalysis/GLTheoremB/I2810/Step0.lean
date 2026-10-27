module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Off
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Cent
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Concl
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Quasi
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Offender

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Step0
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem s0_o2K (h : Setup28 W K S) : pCoreOf 2 K = K ⊓ W := s0_o2K_aux h

theorem s0_quasi (h : Setup28 W K S) : IsQuasisimple ↥(bar W K) := s0_quasi_aux h

theorem s0_w1_nrm (h : Setup28 W K S) :
    ∀ n ∈ K ⊔ S, ∀ w ∈ kerAct W K S, n * w * n⁻¹ ∈ kerAct W K S := s0_w1_nrm_aux h

theorem s0_k_w1 (h : Setup28 W K S) : K ⊓ kerAct W K S = K ⊓ W := s0_k_w1_aux h

theorem s0_v_props (h : Setup28 W K S) :
    IsElemAbelian 2 (vOf W K S) ∧ vOf W K S ≤ kerAct W K S ∧
      ∀ n ∈ K ⊔ S, ∀ v ∈ vOf W K S, n * v * n⁻¹ ∈ vOf W K S := s0_v_props_aux h

theorem s0_concl28d_of_cent (h : Setup28 W K S)
    (hK : K ≤ Subgroup.centralizer (vOf W K S : Set X)) : Concl28d K S :=
  s0_concl28d_aux h hK

theorem s0_cent_comm (h : Setup28 W K S) (hq : IsQuasisimple ↥(bar W K))
    (hnt : ¬ K ≤ Subgroup.centralizer (vOf W K S : Set X)) :
    ∀ c ∈ K ⊔ S, (∀ v ∈ vOf W K S, c * v = v * c) → ∀ k ∈ K, ⁅c, k⁆ ∈ W :=
  s0_cent_comm_aux h hq hnt

theorem s0_exists_offender (h : Setup28 W K S) (hd : ¬ Concl28d K S) :
    ∃ A : Subgroup X, Quasithin.IsMaxElemAbelian S A ∧ ¬ A ≤ kerAct W K S :=
  s0_exists_offender_aux h hd

theorem s0_off (h : Setup28 W K S) (hq : IsQuasisimple ↥(bar W K))
    (hnt : ¬ K ≤ Subgroup.centralizer (vOf W K S : Set X)) {A : Subgroup X}
    (hA : Quasithin.IsMaxElemAbelian S A) :
    (Subgroup.centralizer (A : Set X)).relIndex (vOf W K S) ≤ (kerAct W K S).relIndex A :=
  s0_off_aux h hA

end Step0

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
