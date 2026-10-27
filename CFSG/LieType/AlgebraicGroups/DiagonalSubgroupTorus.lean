module

public import CFSG.LieType.AlgebraicGroups.GLCoordPoints
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupClosed

public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.HopfAlgebra.GroupLike.FiniteGeneration
public import TauCeti.Algebra.Bialgebra.GroupLike.Torsion
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CategoryTheory WithConv

open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] [IsAlgClosed k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isGroupLikeElem_glEntry_of_diagonal_points
    (H : Subgroup (WithConv (GLCoord k ι →ₐ[k] k)))
    (hdiag : ∀ x ∈ H, ∀ i j, i ≠ j → x.ofConv (glEntry k ι i j) = 0) (i : ι) :
    IsGroupLikeElem k (Ideal.Quotient.mk (subgroupIdeal H) (glEntry k ι i i)) := by
  classical
  have hoff : ∀ a b, a ≠ b →
      Ideal.Quotient.mk (subgroupIdeal H) (glEntry k ι a b) = 0 := by
    intro a b hab
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (mem_subgroupIdeal.2 fun x hx => hdiag x hx a b hab)
  refine ⟨?_, ?_⟩
  · rw [Bialgebra.Quotient.counit_mk, counit_glEntry]
    simp
  · rw [Bialgebra.Quotient.comul_mk, comul_glEntry, map_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [TensorProduct.map_tmul]
      change Ideal.Quotient.mk (subgroupIdeal H) (glEntry k ι i j) ⊗ₜ[k]
        Ideal.Quotient.mk (subgroupIdeal H) (glEntry k ι j i) = 0
      simp [hoff i j (Ne.symm hji)]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem torusCommHopfAlgProperty_of_diagonal_points
    (H : Subgroup (WithConv (GLCoord k ι →ₐ[k] k)))
    (hH : IsConnectedAlgebraicSubgroup k H)
    (hdiag : ∀ x ∈ H, ∀ i j, i ≠ j → x.ofConv (glEntry k ι i j) = 0) :
    TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k
        (GLCoord k ι ⧸ subgroupIdeal H)) := by
  classical
  let A := GLCoord k ι ⧸ subgroupIdeal H
  let q : GLCoord k ι →ₐ[k] A := Ideal.Quotient.mkₐ k (subgroupIdeal H)
  obtain ⟨hgl, hcoideal, hfin, hdom, hadjoin, hdet, hcomul, hcomulDet, hcounit,
    hcounitDet, hanti, hantiDet, hmul, happly, happlyDet, hmodGL⟩ :=
    GLCoord_structure (k := k) ι
  have hoff : ∀ i j, i ≠ j → q (glEntry k ι i j) = 0 := by
    intro i j hij
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (mem_subgroupIdeal.2 fun y hy => hdiag y hy i j hij)
  let diag : Set A := Set.range (fun i : ι => q (glEntry k ι i i)) ∪ {q (glDetInv k ι)}
  have hgroupLike : ∀ a ∈ diag, IsGroupLikeElem k a := by
    intro a ha
    rcases ha with ⟨i, rfl⟩ | rfl
    · exact isGroupLikeElem_glEntry_of_diagonal_points H hdiag i
    · refine ⟨?_, ?_⟩
      · rw [Ideal.Quotient.mkₐ_eq_mk, Bialgebra.Quotient.counit_mk, hcounitDet]
      · rw [Ideal.Quotient.mkₐ_eq_mk, Bialgebra.Quotient.comul_mk, hcomulDet]
        simp [Ideal.Quotient.mkₐ_eq_mk]
  have hspan : Algebra.adjoin k diag = ⊤ := by
    have hmap : Algebra.adjoin k
        (q '' (Set.range (fun p : ι × ι => glEntry k ι p.1 p.2) ∪ {glDetInv k ι})) = ⊤ := by
      rw [Algebra.adjoin_image, hadjoin, Algebra.map_top]
      exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective k (subgroupIdeal H))
    have hle : Algebra.adjoin k
        (q '' (Set.range (fun p : ι × ι => glEntry k ι p.1 p.2) ∪ {glDetInv k ι})) ≤
          Algebra.adjoin k diag := by
      apply Algebra.adjoin_le
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · obtain ⟨p, rfl⟩ := hx
        by_cases hp : p.1 = p.2
        · change q (glEntry k ι p.1 p.2) ∈ Algebra.adjoin k diag
          rw [← hp]
          exact Algebra.subset_adjoin (Or.inl ⟨p.1, rfl⟩)
        · rw [hoff p.1 p.2 hp]
          exact Subalgebra.zero_mem _
      · subst hx
        exact Algebra.subset_adjoin (Or.inr rfl)
    exact top_le_iff.mp (hmap ▸ hle)
  have heval_surj : Function.Surjective (TauCeti.GroupLike.evaluationBialgHom k A) := by
    have hrange : (TauCeti.GroupLike.evaluationBialgHom k A).toAlgHom.range = ⊤ := by
      apply top_le_iff.mp
      rw [← hspan]
      apply Algebra.adjoin_le
      intro a ha
      change a ∈ (TauCeti.GroupLike.evaluationBialgHom k A).toAlgHom.range
      rw [AlgHom.mem_range]
      exact ⟨MonoidAlgebra.single ⟨a, hgroupLike a ha⟩ 1, by simp⟩
    rw [AlgHom.range_eq_top] at hrange
    simpa only [BialgHom.coe_toAlgHom] using hrange
  have hspan_sub :
      Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤ :=
    (TauCeti.GroupLike.evaluationBialgHom_surjective_iff_span_eq_top k A).mp heval_surj
  have hgroupLikeSpan :
      TauCeti.Subcoalgebra.groupLikeSetSpan (R := k) (C := A) Set.univ = ⊤ :=
    (TauCeti.GroupLike.evaluationBialgHom_surjective_iff_groupLikeSetSpan_eq_top k A).mp
      heval_surj
  have hfinite : Algebra.FiniteType k A := hH.finiteType
  have hfg : Group.FG (GroupLike k A) :=
    TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top k A hfinite hgroupLikeSpan
  have : IsReduced A := hH.isReduced
  have : ConnectedSpace (PrimeSpectrum A) := hH.connectedSpace
  have htorsionfree : IsMulTorsionFree (GroupLike k A) :=
    TauCeti.isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace k A
  have hfiniteZ : Module.Finite ℤ (Additive (GroupLike k A)) := by
    rw [Module.Finite.iff_addGroup_fg]
    exact AddGroup.fg_iff_mul_fg.mpr hfg
  have htorsionfreeZ : Module.IsTorsionFree ℤ (Additive (GroupLike k A)) := by
    have : IsMulTorsionFree (GroupLike k A) := htorsionfree
    exact Module.isTorsionFree_int_iff_isAddTorsionFree.mpr inferInstance
  obtain ⟨n, b⟩ :=
    Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive (GroupLike k A))
  let e : GroupLike k A ≃* Multiplicative (Fin n →₀ ℤ) :=
    AddEquiv.toMultiplicative b.repr.toAddEquiv
  let eULift : GroupLike k A ≃* Multiplicative (ULift (Fin n) →₀ ℤ) :=
    e.trans (AddEquiv.toMultiplicative
      (Finsupp.domCongr (Equiv.ulift.symm) : (Fin n →₀ ℤ) ≃+ (ULift (Fin n) →₀ ℤ)))
  let evalEquiv : MonoidAlgebra k (GroupLike k A) ≃ₐc[k] A :=
    TauCeti.GroupLike.evaluationBialgEquiv k A hspan_sub
  let bialgEquiv : MonoidAlgebra k (Multiplicative (ULift (Fin n) →₀ ℤ)) ≃ₐc[k] A :=
    (MonoidAlgebra.domCongrBialgEquiv k k eULift).symm.trans evalEquiv
  let iso : TauCeti.DiagonalizableGroup.coordinateRing k
      (TauCeti.SplitTorus.characterGroup (ULift (Fin n))) ≅
        TauCeti.FiniteTypeCommHopfAlgCat.of k A :=
    ObjectProperty.isoMk _ (_root_.CommHopfAlgCat.isoMk bialgEquiv)
  have hsplit : TauCeti.splitTorusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k A) :=
    (TauCeti.splitTorusCommHopfAlgProperty_iff k _).mpr ⟨n, ⟨iso⟩⟩
  exact hsplit.torus

end CFSG.LieType.AlgebraicGroups

end
