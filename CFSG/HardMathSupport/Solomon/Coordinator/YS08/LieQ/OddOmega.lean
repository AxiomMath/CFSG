module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddForm
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSL
public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl CFSG.Assembly.LowTwoRank
open scoped Matrix

section Omega

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F] {q : ℕ} [Fact q.Prime]
  [CharP F q] (Φ : QuadForm F (ι → F))

theorem ea1_Omega (hι : 5 ≤ Fintype.card ι) :
    EA1ε Φ.polar (fun v => Φ.Q v = 0) (natRep (StatedOmega Φ.Q)) (-1) := by
  intro x y hx hxy
  obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι hx hxy
  refine ⟨-Φ.Q y, ⟨A, hA⟩, fun v => ?_⟩
  rw [natRep_apply]
  show (A : Matrix ι ι F) *ᵥ v = _
  rw [hAv v, Φ.eichler_apply]
  module

theorem radRigidInner_Omega (hι : 6 ≤ Fintype.card ι) :
    RadRigidInner q (StatedProj (StatedOmega Φ.Q)) := by
  have hι5 : 5 ≤ Fintype.card ι := by omega
  have hQ : ∀ (h : StatedOmega Φ.Q) (v : ι → F), Φ.Q (natRep (StatedOmega Φ.Q) h v) = Φ.Q v :=
    fun h v => by
      rw [natRep_apply]
      exact orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q h.2) v
  have hstar : NoQuotientReflection Φ (natRep (StatedOmega Φ.Q)) := fun h Z hZ a ha hQa => by
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega Φ h.2 hZ ha hQa
  have hdim : 3 ≤ Module.finrank F (ι → F) := by
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  have hdim6 : 6 ≤ Module.finrank F (ι → F) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hι
  refine radRigidInner_of_rigid (H := StatedOmega Φ.Q)
    ((StatedScalars ι F).subgroupOf (StatedOmega Φ.Q)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime q _) (natRep (StatedOmega Φ.Q)) (natRep_injective _)
    (fun Q => singFlag Φ (natRep (StatedOmega Φ.Q)) Q) (fun Q _ => singFlag_zero _ _ Q)
    (fun Q _ => ⟨_, singFlag_top _ _ Q⟩) (fun Q _ => normalizer_le_flagStab_singFlag hQ Q)
    (fun Q hQp => le_flagKernel_singFlag q hQ hstar Q hQp)
    (fun x hx => mem_statedScalars_of_natRep _ x hx) ?_
  exact rigidInner_form Φ.polar (fun v => Φ.Q v = 0) Φ.IsTotallySingular (natRep (StatedOmega Φ.Q))
    (fun Q => singFlag Φ (natRep (StatedOmega Φ.Q)) Q) (Or.inr rfl)
    (fun c => by rw [Φ.polar_σ]; rfl) hdim (fun U hU => hU.isTotallyIsotropic)
    (fun U hU v hv => hU v hv) (natRep_injective _) (ea1_Omega Φ hι5) (Or.inr hdim6)
    (fun Q _ => ⟨singSeq Φ (natRep (StatedOmega Φ.Q)) Q, Module.finrank F (ι → F),
      singSeq_zero _ _ Q, singSeq_mono _ _ Q, isTotallySingular_singSeq _ _ Q, rfl⟩)
    (isIsometric_natRep_statedOmega Φ)

end Omega

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
