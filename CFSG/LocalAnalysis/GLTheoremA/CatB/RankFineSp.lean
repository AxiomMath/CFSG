module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineAbs
public import CFSG.LargeExtraspecial.DWFldSymplectic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmega
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.Open CFSG.LargeExtraspecial.DW

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def glRep (ι : Type*) [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R] :
    GL ι R →* Module.End R (ι → R) :=
  (Matrix.toLinAlgEquiv' (R := R) (n := ι)).toAlgHom.toMonoidHom.comp
    (Units.coeHom (Matrix ι ι R))

theorem glRep_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (g : GL ι R)
    (x : ι → R) : glRep ι R g x = (g : Matrix ι ι R) *ᵥ x := by
  simp [glRep]

theorem glRep_injective (ι : Type*) [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R] :
    Function.Injective (glRep ι R) := by
  intro g h hgh
  apply Units.ext
  ext i j
  have := congrFun (congrArg (fun f : Module.End R (ι → R) => f (Pi.single j 1)) hgh) i
  simpa [glRep_apply, Matrix.mulVec_single_one] using this

section Symplectic

variable (n : ℕ)

theorem spB_isRefl : (spB n (ZMod 2)).IsRefl := fun x y h => by
  rw [spB_comm]
  exact h

theorem spB_nondegenerate : (spB n (ZMod 2)).Nondegenerate :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (spB_isRefl n)).2 fun _ h => eq_zero_of_spB h

theorem finrank_sp (n : ℕ) :
    Module.finrank (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem rankFine_statedSp_two :
    RankFine (StatedSp n (ZMod 2)) (3 ^ (n - 1)) := by
  have h := card_le_of_normalizes (spB n (ZMod 2)) (spB_nondegenerate n) (spB_isRefl n)
    (by rw [finrank_sp]; exact ⟨n, by ring⟩)
    ((glRep (Fin n ⊕ Fin n) (ZMod 2)).comp (StatedSp n (ZMod 2)).subtype)
    ((glRep_injective _ _).comp Subtype.val_injective)
    (fun g x y => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, glRep_apply]
      exact mem_statedSp_iff_spB.1 g.2 x y)
  rw [finrank_sp] at h
  simpa using h

end Symplectic

section Orthogonal

theorem mem_statedOmega_quad {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) {g : GL ι K} (hg : g ∈ StatedOmega Q) (v : ι → K) :
    Q ((g : Matrix ι ι K) *ᵥ v) = Q v := by
  have h := CFSG.Blueprint.EvenSource.statedOmega_eq_commutator Q
  rw [h] at hg
  have hle : ⁅CFSG.Blueprint.EvenSource.matrixOrthogonal Q,
      CFSG.Blueprint.EvenSource.matrixOrthogonal Q⁆ ≤
        CFSG.Blueprint.EvenSource.matrixOrthogonal Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Blueprint.EvenSource.matrixOrthogonal Q).mul_mem
      ((CFSG.Blueprint.EvenSource.matrixOrthogonal Q).mul_mem
        ((CFSG.Blueprint.EvenSource.matrixOrthogonal Q).mul_mem ha hb)
        ((CFSG.Blueprint.EvenSource.matrixOrthogonal Q).inv_mem ha))
      ((CFSG.Blueprint.EvenSource.matrixOrthogonal Q).inv_mem hb)
  exact hle hg v

theorem spB_eq_quad (x y : Fin 4 ⊕ Fin 4 → ZMod 2) :
    spB 4 (ZMod 2) x y = StatedQuadPlus 4 (ZMod 2) (x + y) + StatedQuadPlus 4 (ZMod 2) x +
      StatedQuadPlus 4 (ZMod 2) y := by
  simp only [StatedQuadPlus, spB_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize x (Sum.inl i) = a
  generalize x (Sum.inr i) = b
  generalize y (Sum.inl i) = c
  generalize y (Sum.inr i) = d
  revert a b c d
  decide

theorem om8_spB {g : GL CFSG.AGLEmbedding.ι8 (ZMod 2)} (hg : g ∈ CFSG.AGLEmbedding.Om8)
    (x y : CFSG.AGLEmbedding.ι8 → ZMod 2) :
    spB 4 (ZMod 2) ((g : Matrix _ _ (ZMod 2)) *ᵥ x) ((g : Matrix _ _ (ZMod 2)) *ᵥ y) =
      spB 4 (ZMod 2) x y := by
  have hQ := mem_statedOmega_quad (StatedQuadPlus 4 (ZMod 2)) hg
  rw [spB_eq_quad, spB_eq_quad, ← Matrix.mulVec_add, hQ, hQ, hQ]

theorem rankFine_om8 : RankFine CFSG.AGLEmbedding.Om8 27 := by
  have h := card_le_of_normalizes (spB 4 (ZMod 2)) (spB_nondegenerate 4) (spB_isRefl 4)
    (by rw [finrank_sp]; exact ⟨4, by ring⟩)
    ((glRep (Fin 4 ⊕ Fin 4) (ZMod 2)).comp CFSG.AGLEmbedding.Om8.subtype)
    ((glRep_injective _ _).comp Subtype.val_injective)
    (fun g x y => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, glRep_apply]
      exact om8_spB g.2 x y)
  rw [finrank_sp] at h
  simpa using h

end Orthogonal

end CFSG.LocalAnalysis.GLTheoremA.CatB
