module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_zmod3_eq_one_or_neg_one (z : ZMod 3) (hz : z ≠ 0) : z = 1 ∨ z = -1 := by
  revert z
  decide

private lemma aux_units_zmod3_comm (a b : (ZMod 3)ˣ) : a * b = b * a := by
  revert a b
  decide

private lemma aux_squareClass_zmod3_comm
    (a b : Multiplicative (SquareClassGroup (ZMod 3))) : a * b = b * a := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_mul]
  exact add_comm _ _

theorem commutator_le_omegaGroup (hQ : Q.Nondegenerate) :
    commutator (OGroup Q) ≤ omegaGroup hQ := by
  haveI : IsMulCommutative ((ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3))) :=
    IsMulCommutative.of_comm fun a b =>
      Prod.ext (aux_units_zmod3_comm a.1 b.1) (aux_squareClass_zmod3_comm a.2 b.2)
  rw [omegaGroup]
  exact Abelianization.commutator_subset_ker (detSpinorNorm hQ)

theorem index_commutator_le_four (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) : (commutator (OGroup Q)).index ≤ 4 := by
  classical
  haveI : NeZero (2 : ZMod 3) := ⟨(isUnit_of_invertible (2 : ZMod 3)).ne_zero⟩
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  let O := OGroup Q
  let N : Subgroup O := commutator O
  haveI hN : N.Normal := inferInstance
  haveI hcomm : IsMulCommutative (O ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  obtain ⟨v1, hv1⟩ := exists_eq_unit_of_two_le_finrank hQ h2 (1 : (ZMod 3)ˣ)
  obtain ⟨v2, hv2⟩ := exists_eq_unit_of_two_le_finrank hQ h2 (-1 : (ZMod 3)ˣ)
  have hv1' : Q v1 = 1 := by rw [hv1]; rfl
  have hv2' : Q v2 = -1 := by rw [hv2]; rfl
  have hQv1 : Q v1 ≠ 0 := by rw [hv1']; exact one_ne_zero
  have hQv2 : Q v2 ≠ 0 := by rw [hv2']; exact neg_ne_zero.mpr one_ne_zero
  haveI : Invertible (Q v1) := invertibleOfNonzero hQv1
  haveI : Invertible (Q v2) := invertibleOfNonzero hQv2
  set π : O →* O ⧸ N := QuotientGroup.mk' N with hπ
  set s1 : O := TauCeti.QuadraticMap.reflectionOrthogonal Q v1 with hs1def
  set s2 : O := TauCeti.QuadraticMap.reflectionOrthogonal Q v2 with hs2def
  have hs1 : s1 * s1 = 1 := TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q v1
  have hs2 : s2 * s2 = 1 := TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q v2
  set a : O ⧸ N := π s1 with ha
  set b : O ⧸ N := π s2 with hb
  have haa : a * a = 1 := by rw [ha, ← map_mul, hs1, map_one]
  have hbb : b * b = 1 := by rw [hb, ← map_mul, hs2, map_one]
  have hab : a * b = b * a := mul_comm' a b
  have hrefl : ∀ (v : V) [Invertible (Q v)],
      π (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = a ∨
        π (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = b := by
    intro v _
    have hv0 : Q v ≠ 0 := (isUnit_of_invertible (Q v)).ne_zero
    rcases aux_zmod3_eq_one_or_neg_one (Q v) hv0 with hv | hv
    · left
      obtain ⟨f, hf⟩ := _root_.QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq (Q := Q)
        (x := v1) (y := v) (by rw [hv1', hv]) hv0
      let g : O := (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm f
      have hgv : (g : V ≃ₗ[ZMod 3] V) v1 = v := by
        show (((TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm f :
          V ≃ₗ[ZMod 3] V) : V → V) v1 = v
        rw [TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv_symm]
        exact hf
      haveI : Invertible (Q ((g : V ≃ₗ[ZMod 3] V) v1)) := by rw [hgv]; exact inferInstance
      have hconj := TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv Q g v1
      have hrefl_eq : TauCeti.QuadraticMap.reflectionOrthogonal Q v =
          TauCeti.QuadraticMap.reflectionOrthogonal Q ((g : V ≃ₗ[ZMod 3] V) v1) := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
          TauCeti.QuadraticMap.coe_reflectionOrthogonal,
          TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
          TauCeti.QuadraticMap.reflection_apply_eq_sub_div, hgv]
      have key : π (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = a := by
        rw [hrefl_eq, ← hconj, map_mul, map_mul, map_inv]
        change π g * a * (π g)⁻¹ = a
        rw [mul_comm' (π g) a, mul_assoc, mul_inv_cancel, mul_one]
      exact key
    · right
      obtain ⟨f, hf⟩ := _root_.QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq (Q := Q)
        (x := v2) (y := v) (by rw [hv2', hv]) hv0
      let g : O := (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm f
      have hgv : (g : V ≃ₗ[ZMod 3] V) v2 = v := by
        show (((TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm f :
          V ≃ₗ[ZMod 3] V) : V → V) v2 = v
        rw [TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv_symm]
        exact hf
      haveI : Invertible (Q ((g : V ≃ₗ[ZMod 3] V) v2)) := by rw [hgv]; exact inferInstance
      have hconj := TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv Q g v2
      have hrefl_eq : TauCeti.QuadraticMap.reflectionOrthogonal Q v =
          TauCeti.QuadraticMap.reflectionOrthogonal Q ((g : V ≃ₗ[ZMod 3] V) v2) := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
          TauCeti.QuadraticMap.coe_reflectionOrthogonal,
          TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
          TauCeti.QuadraticMap.reflection_apply_eq_sub_div, hgv]
      have key : π (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = b := by
        rw [hrefl_eq, ← hconj, map_mul, map_mul, map_inv]
        change π g * b * (π g)⁻¹ = b
        rw [mul_comm' (π g) b, mul_assoc, mul_inv_cancel, mul_one]
      exact key
  have hgen : ∀ x : O ⧸ N, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    set H : Subgroup O := (Subgroup.closure ({a, b} : Set (O ⧸ N))).comap π with hH
    have hHtop : H = ⊤ := by
      refine TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ H ?_
      intro v _
      rw [hH, Subgroup.mem_comap]
      rcases hrefl v with h | h <;> rw [h] <;> exact Subgroup.subset_closure (by simp)
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hg : g ∈ H := by rw [hHtop]; exact Subgroup.mem_top g
    exact CFSG.ClassicalInvolution.eq_one_or_eq_or_eq_mul_of_mem_closure_pair
      haa hbb hab (Subgroup.mem_comap.1 hg)
  have hle : N.index ≤ 4 := by
    have hcard : Nat.card (O ⧸ N) ≤ 4 := by
      rw [← Set.ncard_univ]
      have hsub : (Set.univ : Set (O ⧸ N)) ⊆ ({1, a, b, a * b} : Set (O ⧸ N)) := by
        intro x _
        rcases hgen x with h | h | h | h <;> simp [h]
      refine (Set.ncard_le_ncard hsub).trans ?_
      have h1 := Set.ncard_insert_le (1 : O ⧸ N)
        (insert a (insert b ({a * b} : Set (O ⧸ N))))
      have h2 := Set.ncard_insert_le (a : O ⧸ N) (insert b ({a * b} : Set (O ⧸ N)))
      have h3 := Set.ncard_insert_le (b : O ⧸ N) ({a * b} : Set (O ⧸ N))
      have h4 : ({a * b} : Set (O ⧸ N)).ncard = 1 := Set.ncard_singleton _
      omega
    exact hcard
  simpa only [N, O] using hle

theorem omegaGroup_eq_commutator (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) : omegaGroup hQ = commutator (OGroup Q) := by
  refine le_antisymm ?_ (commutator_le_omegaGroup hQ)
  have hcm : (commutator (OGroup Q)).index = 4 := by
    have hdvd : (omegaGroup hQ).index ∣ (commutator (OGroup Q)).index :=
      Subgroup.index_dvd_of_le (commutator_le_omegaGroup hQ)
    rw [index_omegaGroup hQ h2] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hle := index_commutator_le_four hQ h2
    have hne : (commutator (OGroup Q)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hrel := Subgroup.relIndex_mul_index (commutator_le_omegaGroup hQ)
  rw [hcm, index_omegaGroup hQ h2] at hrel
  have hrel1 : (commutator (OGroup Q)).relIndex (omegaGroup hQ) = 1 := by omega
  exact Subgroup.relIndex_eq_one.mp hrel1

end CFSG.OddStandard.SmallF3.Omega
