module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph3Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph3Model
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallBasic

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBLinearHigherB

theorem a6_psl_pureGraph_small_three (hO : LieOrderFormulasInput) {f : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 3 ^ f) (hs : A6Shape .PSL 3 f) (A : GL (Fin 3) K)
    (hsigma : orderOf (pureGraphAction 3 K A) = 2)
    (D : Subgroup ↥(fixedSubgroup (pureGraphAction 3 K A)))
    (hD : A6Hyp (pureGraphAction 3 K A) D) :
    A6SmallConcl .PSL 3 f (pureGraphAction 3 K A) D := by
  clear hO
  have hf : f = 2 := PSLSmallGraph3.shape_f hs
  subst hf
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have hodd : Odd (Nat.card K) := by rw [hK9]; decide
  have hodd' := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have hsq2 : pureGraphAction 3 K A ^ 2 = 1 := by
    have := pow_orderOf_eq_one (pureGraphAction 3 K A)
    rwa [hsigma] at this
  have hsymm : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = (A : Matrix (Fin 3) (Fin 3) K) := by
    rcases CatalogueBGraphForm.pureGraph_involution_form_data 3 K (by norm_num) hodd' A hsq2 with
      h | ⟨-, h⟩
    · exact h
    · exact absurd h (by decide)
  obtain ⟨z, t, hz, ht, hzt⟩ :=
    PSLSmallGraph3.exists_dihedral hodd' hK9 A (transpose_inv_of_transpose_eq A hsymm)
  obtain ⟨x, hx2, hxD⟩ := PSLSmallGraph3.outer_involution_of_dihedral hD hz ht hzt
  exact ⟨fun hin => absurd hin (PSLSmallGraph3.pureGraph_not_inner (by norm_num) A),
    fun _ hle => ⟨PSLSmall.card_eq_720 hD hle hxD, Or.inl ⟨x, hx2, hxD⟩⟩⟩

end CFSG.ComponentClassification.CatFC
