module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClPSUGraph
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClPSU

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.U

variable {p f : ℕ} {K : Type} [Field K] (hu : UnitaryFieldData p f K) {n : ℕ}

include hu in
theorem noL2At_psu (hp2 : p ≠ 2) (hn : 6 ≤ n)
    {v : MulAut (StatedProj (StatedSU n (p ^ f) K))} (hv : orderOf v = 2) : NoL2At v := by
  have := hu.finite
  have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun h => by omega
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut hu (by omega) hq' v
  have hsq : (uConjAut hu (by omega) A * uFieldAut hu (by omega) φ) ^ 2 = 1 := by
    rw [← hα, ← hv, pow_orderOf_eq_one]
  rcases uFieldAut_eq_or_of_sq hu (by omega) hq' hsq with rfl | hφ
  · rw [map_one, mul_one] at hα
    rw [hα] at hv ⊢
    exact noL2At_uConjAut hu hp2 hn hv
  · have hφe : φ = barEq hu := RingEquiv.ext hφ
    subst hφe
    rw [graph_sq] at hsq
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff hu (by omega) _).1 hsq
    have hAc : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar = (c : K) • 1 := by
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uGlAut]
        at e
      change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq hu) = _
      rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hα]
    exact noL2At_uGraph hu hp2 hn _ hAc

theorem noL2At_of_lieModel_PSU {S : Type} [Group S] [Finite S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : 6 ≤ n) (hL : CFSG.Blueprint.LieModel S .PSU n p f) {v : MulAut S}
    (hv : orderOf v = 2) : NoL2At v := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    have hu : UnitaryFieldData p f K := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
    refine NoL2At.of_congr θ (noL2At_psu hu hp2 hn ?_)
    rw [MulEquiv.orderOf_eq]
    exact hv
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.Cl
