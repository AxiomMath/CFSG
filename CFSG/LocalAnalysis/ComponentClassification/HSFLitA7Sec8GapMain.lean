module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapKL
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapSyl

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

theorem BData.false_of_K [IsSimpleGroup X] (A : BData S F T₁) (hX : ∃ a b : X, a * b ≠ b * a)
    (hnc : ¬ SubConj F.E₁ F.E₂) : False := by
  obtain ⟨Y⟩ := A.exists_syl
  have hc4 : A.Φ ![0, 0, 1] ^ 4 = 1 := by
    rw [← A.Φ_nsmul, show (4 : ℕ) • (![0, 0, 1] : Fin 3 → ZMod 4) = 0 by decide, A.Φ_zero]
  have hc2 : A.Φ ![0, 0, 1] ^ 2 = F.kF := by
    rw [← A.Φ_nsmul, ← A.Φ_k]
    congr 1
    decide
  refine false_of_cyclic_four (S := S) hX
    (sylowOfMax Y.isPGroup fun R hR hle => Y.max_X hnc hR hle) (ζ := A.Φ ![0, 0, 1])
    (z₀ := S.z) (fun g hg h4 h2 => A.sq_eq_z_of_mem_T hg h4 h2) hc4
    (by rw [hc2]; exact (isK_kF F).ne_one) (fun p hp => Y.conj_c hnc hp) Y.t_mem
    (by rw [A.t_conj_Φ, A.Φ_neg]) (by rw [hc2]; exact A.not_conjTo_z_k hnc)

theorem fritz812dNotSylow : Fritz812dNotSylowInput := by
  intro _ X _ _ _ hX _ S F T₁ h4 hnc D₁ D₂ hq₁ hq₂ hu₁ hu₂ _ _ _
  exact ((BData.mk h4 D₁ D₂ hq₁ hq₂ hu₁ hu₂).false_of_K hX hnc).elim

end Sec8

end CFSG.ComponentClassification.HSFLit
