module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsPrimary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSetup

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt elt elt_neg E)
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Standard

variable {K : Type} [Field K] {m : ℕ}

theorem commutator_expand_of_mul_self {R : Type*} [Ring R] {X Y : R} (hX : X * X = 0)
    (hY : Y * Y = 0) :
    (1 + X) * (1 + Y) * (1 - X) * (1 - Y) =
      1 + (X * Y - Y * X) - X * Y * X + Y * X * Y + X * Y * X * Y := by
  have h : (1 + X) * (1 + Y) * (1 - X) * (1 - Y) =
      1 + (X * Y - Y * X) - X * Y * X + Y * X * Y + X * Y * X * Y - X * X - Y * Y -
        X * (Y * Y) + X * X * Y := by noncomm_ring
  rw [h, hX, hY]
  simp

theorem mat_comm_difference_positiveLong {j : Fin (m + 1)} (hj : (0 : Fin (m + 1)) ≠ j)
    (s t : K) :
    mat (m + 1) K ⁅elt (.difference 0 j hj) s, elt (.positiveLong j) t⁆ =
      1 + (s * t) • (single (Sum.inl 0) (Sum.inr j) 1 + single (Sum.inl j) (Sum.inr 0) 1) +
        (s ^ 2 * t) • single (Sum.inl 0) (Sum.inr 0) 1 := by
  rw [commutatorElement_def, ← elt_neg, ← elt_neg, map_mul, map_mul, map_mul, mat_elt, mat_elt,
    mat_elt, mat_elt, neg_smul, neg_smul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  simp only [E]
  rw [commutator_expand_of_mul_self]
  · simp [Matrix.mul_sub, Matrix.sub_mul, single_mul_single_same, single_mul_single_of_ne]
    rw [sq, mul_assoc]
  · simp [Matrix.mul_sub, Matrix.sub_mul, single_mul_single_of_ne, hj, hj.symm]
  · simp [single_mul_single_of_ne]

theorem commute_difference_positiveLong_zero {j : Fin (m + 1)} (hj : (0 : Fin (m + 1)) ≠ j)
    (s c : K) :
    elt (.difference 0 j hj) s * elt (.positiveLong 0) c =
      elt (.positiveLong 0) c * elt (.difference 0 j hj) s := by
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt]
  simp only [E]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, single_mul_single_of_ne,
    hj, hj.symm]
  abel

theorem one_add_smul_mul_one_add_smul_longBlock (j : Fin (m + 1)) (a b a' b' : K) :
    (1 + a • (single (Sum.inl 0) (Sum.inr j) 1 + single (Sum.inl j) (Sum.inr 0) 1) +
        b • single (Sum.inl 0) (Sum.inr 0) (1 : K) :
          Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K) *
      (1 + a' • (single (Sum.inl 0) (Sum.inr j) 1 + single (Sum.inl j) (Sum.inr 0) 1) +
        b' • single (Sum.inl 0) (Sum.inr 0) (1 : K)) =
      1 + (a + a') • (single (Sum.inl 0) (Sum.inr j) 1 + single (Sum.inl j) (Sum.inr 0) 1) +
        (b + b') • single (Sum.inl 0) (Sum.inr 0) (1 : K) := by
  simp [Matrix.mul_add, Matrix.add_mul, single_mul_single_of_ne, single_add]
  abel

theorem elt_positiveLong_zero_mem_perfectCore (hm : 1 ≤ m) (h4 : 4 ≤ Nat.card K) (c : K) :
    elt (.positiveLong 0) c ∈ perfectCore (centralizer
      ({elt (.positiveLong 0) c} : Set (StatedSp (m + 1) K))) := by
  set t₀ : StatedSp (m + 1) K := elt (.positiveLong 0) c with ht₀
  set j : Fin (m + 1) := Fin.last m with hjdef
  have hj : (0 : Fin (m + 1)) ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [hjdef] at this
    omega
  have hL : (longBlock K (m + 1) j).range ≤ centralizer ({t₀} : Set (StatedSp (m + 1) K)) := by
    rintro _ ⟨X, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : longBlock K (m + 1) j X ∈ suppGroup (coords j) := by
      rw [← range_longBlock]
      exact ⟨X, rfl⟩
    have h2 : t₀ ∈ suppGroup (coords j)ᶜ := by
      refine suppGroup_mono (coords_subset_compl hj) ?_
      rw [← range_longBlock, ht₀, ← longBlock_sl2Upper]
      exact ⟨_, rfl⟩
    exact commute_suppGroup_compl h1 h2
  have hperf : ⁅(longBlock K (m + 1) j).range, (longBlock K (m + 1) j).range⁆ =
      (longBlock K (m + 1) j).range := by
    have hP := (CFSG.RankThree.PartOne.KCOrthogonal.sl2_isPerfect h4).commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hP]
  have hLP := CFSG.Quasithin.le_perfectCore_of_perfect hL hperf
  have hst : ∀ s t : K, ⁅elt (.difference 0 j hj) s, elt (.positiveLong j) t⁆ ∈
      perfectCore (centralizer ({t₀} : Set (StatedSp (m + 1) K))) := by
    intro s t
    refine commutatorElement_mem_perfectCore ?_ (hLP ⟨sl2Upper t, longBlock_sl2Upper j t⟩)
    rw [mem_centralizer_singleton_iff]
    exact commute_difference_positiveLong_zero hj s c
  obtain ⟨l, hl0, hl1⟩ : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
    classical
    by_contra hne
    have hne' : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by_contra fun h1 => hne ⟨x, hx, h1⟩
    have hs : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hne' x hx]⟩
    have h2 := Nat.card_le_card_of_surjective _ hs
    rw [show Nat.card Bool = 2 by simp] at h2
    omega
  obtain ⟨d, hd⟩ : ∃ d : K, (l ^ 2 - l) * d = 1 :=
    ⟨(l ^ 2 - l)⁻¹, mul_inv_cancel₀ (by
      rw [sq, ← mul_sub_one]
      exact mul_ne_zero hl0 (sub_ne_zero.2 hl1))⟩
  have key : t₀ = ⁅elt (.difference 0 j hj) (1 : K), elt (.positiveLong j) (-(l * (c * d)))⁆ *
      ⁅elt (.difference 0 j hj) l, elt (.positiveLong j) (c * d)⁆ := by
    apply mat_injective
    rw [map_mul, mat_comm_difference_positiveLong, mat_comm_difference_positiveLong,
      one_add_smul_mul_one_add_smul_longBlock, ht₀, mat_elt,
      show 1 * -(l * (c * d)) + l * (c * d) = 0 by ring,
      show 1 ^ 2 * -(l * (c * d)) + l ^ 2 * (c * d) = c by linear_combination c * hd, zero_smul,
      add_zero]
    rfl
  have hmem := mul_mem (hst 1 (-(l * (c * d)))) (hst l (c * d))
  rwa [← key] at hmem

end Standard

theorem symplecticTransvectionPerfect : SymplecticTransvectionPerfect := by
  intro n K _ _ _ hn h4 M hM _ hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set M' : StatedSp (m + 1) K := ⟨M, hM⟩ with hM'
  have hr' : (mat (m + 1) K M' - 1).rank = 1 := hr
  obtain ⟨u, c, hu, -, huc⟩ := exists_transvection_form M' hr'
  obtain ⟨w₀, hw₀⟩ := exists_form_eq_one hu
  obtain ⟨g, hge, -⟩ := exists_sp_apply_eq u w₀ hw₀
  have hgi : mat (m + 1) K g⁻¹ *ᵥ u = Pi.single (Sum.inl 0) 1 :=
    ((mulVec_eq_iff g _ u).1 hge).symm
  have hconj : mat (m + 1) K g⁻¹ * (mat (m + 1) K M' - 1) * mat (m + 1) K g =
      single (Sum.inl 0) (Sum.inr 0) c := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, huc,
      mulVec_smul, hgi, ← hge, form_mulVec, form_single_left', single_mulVec]
    ext r
    by_cases hr : r = Sum.inl 0
    · subst hr
      simp
    · simp [hr]
  have ht : g⁻¹ * M' * g = elt (.positiveLong 0) c := by
    apply mat_injective
    have hM1 : mat (m + 1) K M' = 1 + (mat (m + 1) K M' - 1) := by rw [add_sub_cancel]
    rw [map_mul, map_mul, hM1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← map_mul,
      inv_mul_cancel, map_one, hconj, mat_elt]
    simp [E, smul_single]
  have hφ : (MulAut.conj g).toMonoidHom (elt (.positiveLong 0) c) = M' := by
    rw [← ht, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h₁ := map_mem_perfectCore_of_le (MulAut.conj g).toMonoidHom
    (K := centralizer ({M'} : Set (StatedSp (m + 1) K)))
    (by
      have := map_centralizer_le (MulAut.conj g).toMonoidHom (elt (.positiveLong 0) c)
      rwa [hφ] at this)
    (elt_positiveLong_zero_mem_perfectCore (by omega) h4 c)
  rw [hφ] at h₁
  exact map_mem_perfectCore_of_le (StatedSp (m + 1) K).subtype
    (map_subtype_centralizer M').le h₁

theorem classicalPrimaryPerfect_of_unitary_orthogonal (hU : UnitaryTransvectionPerfect)
    (hO : OrthogonalSingularPerfect) : ClassicalPrimaryPerfect :=
  classicalPrimaryPerfect_of symplecticTransvectionPerfect hU hO

end CFSG.ComponentClassification.RankTwoClassical
