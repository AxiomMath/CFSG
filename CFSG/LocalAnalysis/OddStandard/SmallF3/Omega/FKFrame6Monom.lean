module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fk_fr_monomial {c : ZMod 3} (fr : NFrame Q (Fin 6) c) (g : OGroup Q)
    (σ : Equiv.Perm (Fin 6))
    (hg : ∀ i, ∃ a : ZMod 3, a ≠ 0 ∧ (g : V ≃ₗ[ZMod 3] V) (fr.b i) = a • fr.b (σ i)) :
    ∃ K : Finset (Fin 6), g = fr.permOrth σ * fr.signChange K := by
  choose a ha hga using hg
  have ha' : ∀ i, a i = 1 ∨ a i = -1 := by
    intro i
    have h := ha i
    revert h
    generalize a i = x
    revert x
    decide
  have h13 : (1 : ZMod 3) ≠ -1 := by decide
  refine ⟨Finset.univ.filter (fun i => a i = -1), ?_⟩
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  change (g : V ≃ₗ[ZMod 3] V) (fr.b i) =
    (((fr.permOrth σ * fr.signChange (Finset.univ.filter fun i => a i = -1) : OGroup Q) :
      V ≃ₗ[ZMod 3] V) (fr.b i))
  rw [ffMono_basis, hga i]
  rcases ha' i with h | h
  · have hn : i ∉ Finset.univ.filter (fun i => a i = -1) := by simp [h, h13]
    rw [if_neg hn, h, one_smul]
  · have hm : i ∈ Finset.univ.filter (fun i => a i = -1) := by simp [h]
    rw [if_pos hm, h, neg_one_smul]

end CFSG.OddStandard.SmallF3.Omega
