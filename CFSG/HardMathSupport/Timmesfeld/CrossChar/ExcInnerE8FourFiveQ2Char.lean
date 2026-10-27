module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section CharTwo

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem rootSL2_uSL_two (β : Fin τ.rank → ℤ) (c : L) :
    rootSL2 τ L β (uSL c) = pinnedX τ L β c := by
  rw [rootSL2_uSL_eq]
  rcases pinnedSign_eq τ β with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

theorem rootSL2_vSL_two {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : L) :
    rootSL2 τ L β (vSL c) = pinnedX τ L (-β) c := by
  obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  have hε1 : ε = 1 := by
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [h, hε1, one_mul]

theorem rootSL2_neg_two {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (A : SL2 L) :
    rootSL2 τ L (-β) A = rootSL2 τ L β (conjSL swapGL A) := by
  have h := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L))
    (f := rootSL2 τ L (-β)) (g := (rootSL2 τ L β).comp (conjSL swapGL)) ?_
  · exact DFunLike.congr_fun h A
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change rootSL2 τ L (-β) (uSL c) = rootSL2 τ L β (conjSL swapGL (uSL c))
    rw [rootSL2_uSL_two]
    have : conjSL swapGL (uSL c : SL2 L) = vSL c := conjSL_swap_sl2Upper c
    rw [this, rootSL2_vSL_two hβ]
  · change rootSL2 τ L (-β) (vSL c) = rootSL2 τ L β (conjSL swapGL (vSL c))
    rw [rootSL2_vSL_two (IsRoot.neg hβ), neg_neg]
    have : conjSL swapGL (vSL c : SL2 L) = uSL c := conjSL_swap_sl2Lower c
    rw [this, rootSL2_uSL_two]

theorem conj_rootSL2_two (w : WeylGroup τ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (A : SL2 L) :
    canonicalRep (coxeterSystem τ) L w * rootSL2 τ L γ A *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootSL2 τ L (w • γ) A := by
  have h := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L))
    (f := (MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom.comp (rootSL2 τ L γ))
    (g := rootSL2 τ L (w • γ)) ?_
  · exact DFunLike.congr_fun h A
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change canonicalRep (coxeterSystem τ) L w * rootSL2 τ L γ (uSL c) *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootSL2 τ L (w • γ) (uSL c)
    rw [rootSL2_uSL_two, rootSL2_uSL_two, canonicalRep_conj_pinnedX_two w hγ]
  · change canonicalRep (coxeterSystem τ) L w * rootSL2 τ L γ (vSL c) *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootSL2 τ L (w • γ) (vSL c)
    rw [rootSL2_vSL_two hγ, rootSL2_vSL_two ((isRoot_smul_iff w).2 hγ),
      canonicalRep_conj_pinnedX_two w (IsRoot.neg hγ), smul_neg]

end CharTwo

end CFSG.HardMathSupport.Timmesfeld.CrossChar
