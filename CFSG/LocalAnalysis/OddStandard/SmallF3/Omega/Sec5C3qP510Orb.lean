module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Tw
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3q510Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

private theorem sec5p510c_t_ne_one (hR : Sec5RCtx G t L S z r B A) : t ≠ 1 := by
  intro h
  have h2 := hR.involution
  rw [h, orderOf_one] at h2
  omega

private theorem sec5p510c_tM_subset (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    conjClassIn (normalizer (A : Set G)) t ⊆
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 := by
  intro x hx
  rcases hx with ⟨m, hmM, rfl⟩
  have hxA : m * t * m⁻¹ ∈ (A : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hmM t).mp hm.mem_A.1
  have hx1 : m * t * m⁻¹ ≠ 1 := by
    intro h
    refine sec5p510c_t_ne_one hR ?_
    have h2 : m * t = m * 1 := by
      rw [mul_one]
      exact mul_inv_eq_one.mp (by simpa [mul_assoc] using h)
    exact mul_left_cancel h2
  have hzM : conjClassIn (normalizer (A : Set G)) z = wclass φ 3 ∪ wclass φ 4 :=
    sec5b_zM_eq hy hR hm
  have hxnotzM : m * t * m⁻¹ ∉ conjClassIn (normalizer (A : Set G)) z := by
    rintro ⟨m', hm'M, hxeq⟩
    have hz' : z = m'⁻¹ * (m * t * m⁻¹) * m' := by rw [hxeq]; group
    have hconj : (m'⁻¹ * m)⁻¹ * z * (m'⁻¹ * m) = t := by rw [hz']; group
    exact (sec5_t_not_conj_z hy.h37 hR.toSec5Ctx (m'⁻¹ * m)) hconj
  have hxnot3 : m * t * m⁻¹ ∉ wclass φ 3 := fun hw => hxnotzM (by rw [hzM]; exact Or.inl hw)
  have hxnot4 : m * t * m⁻¹ ∉ wclass φ 4 := fun hw => hxnotzM (by rw [hzM]; exact Or.inr hw)
  obtain ⟨k, hk1, hk6, hxWk⟩ := hm.perm.exists_wclass_pos hxA hx1
  have hk3 : k ≠ 3 := by rintro rfl; exact hxnot3 hxWk
  have hk4 : k ≠ 4 := by rintro rfl; exact hxnot4 hxWk
  have hk : k = 1 ∨ k = 2 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk with rfl | rfl | rfl | rfl <;> (simp only [Set.mem_union]; tauto)

private theorem sec5p510c_tM_block (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) (k : ℕ) :
    wclass φ k ⊆ conjClassIn (normalizer (A : Set G)) t ∨
      conjClassIn (normalizer (A : Set G)) t ∩ wclass φ k = ∅ := by
  by_cases h : (conjClassIn (normalizer (A : Set G)) t ∩ wclass φ k).Nonempty
  · left
    refine hm.perm.wclass_subset_of_inter ?_ h
    intro a ha x hx
    rcases ha with ⟨_, haM⟩
    rcases hx with ⟨m, hmM, rfl⟩
    exact ⟨a * m, mul_mem haM hmM, by group⟩
  · right
    exact Set.not_nonempty_iff_eq_empty.mp h

theorem sec5p510_wclass_twist_three (φ : (Fin 6 → ZMod 2) → G) :
    wclass (fun v => φ (sec5p510_twist v)) 3 = wclass φ 3 := by
  rw [wclass, wclass, ← Set.image_image]
  congr 1
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : vecWeight v = 3 := hv
    have hsum : (∑ i, v i) ≠ 0 := by
      intro h0
      have he : Even (vecWeight v) :=
        (sec5b6_isEvenVec_iff v).mp (by simpa [IsEvenVec] using h0)
      rw [hv'] at he
      norm_num at he
    show vecWeight (sec5p510_twist v) = 3
    rw [sec5p510_weight_twist, if_neg hsum, hv']
  · intro hu
    have hu' : vecWeight u = 3 := hu
    refine ⟨sec5p510_twist u, ?_, sec5p510_twist_twist u⟩
    have hsum : (∑ i, u i) ≠ 0 := by
      intro h0
      have he : Even (vecWeight u) :=
        (sec5b6_isEvenVec_iff u).mp (by simpa [IsEvenVec] using h0)
      rw [hu'] at he
      norm_num at he
    show vecWeight (sec5p510_twist u) = 3
    rw [sec5p510_weight_twist, if_neg hsum, hu']

theorem sec5p510_wclass_twist_four (φ : (Fin 6 → ZMod 2) → G) :
    wclass (fun v => φ (sec5p510_twist v)) 4 = wclass φ 4 := by
  rw [wclass, wclass, ← Set.image_image]
  congr 1
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : vecWeight v = 4 := hv
    have hsum : (∑ i, v i) = 0 := by
      have he : Even (vecWeight v) := by rw [hv']; norm_num
      simpa [IsEvenVec] using (sec5b6_isEvenVec_iff v).mpr he
    show vecWeight (sec5p510_twist v) = 4
    rw [sec5p510_weight_twist, if_pos hsum, hv']
  · intro hu
    have hu' : vecWeight u = 4 := hu
    refine ⟨sec5p510_twist u, ?_, sec5p510_twist_twist u⟩
    have hsum : (∑ i, u i) = 0 := by
      have he : Even (vecWeight u) := by rw [hu']; norm_num
      simpa [IsEvenVec] using (sec5b6_isEvenVec_iff u).mpr he
    show vecWeight (sec5p510_twist u) = 4
    rw [sec5p510_weight_twist, if_pos hsum, hu']

theorem sec5p510_delta_cases (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ)
    (h7 : Set.ncard (conjClassIn (normalizer (A : Set G)) t) = 7) :
    conjClassIn (normalizer (A : Set G)) t = wclass φ 6 ∪ wclass φ 1 ∨
      conjClassIn (normalizer (A : Set G)) t = wclass φ 6 ∪ wclass φ 5 := by
  classical
  set T : Set G := conjClassIn (normalizer (A : Set G)) t with hT
  have h7T : T.ncard = 7 := by rw [hT]; exact h7
  have htT : t ∈ T := by rw [hT]; exact ⟨1, Subgroup.one_mem _, by group⟩
  have hsub : T ⊆ wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 := by
    rw [hT]; exact sec5p510c_tM_subset hy hR hm
  have hblock : ∀ k, wclass φ k ⊆ T ∨ T ∩ wclass φ k = ∅ := by
    intro k
    have h := sec5p510c_tM_block hR hm k
    rwa [← hT] at h
  have hW6 : wclass φ 6 ⊆ T := by
    rcases hblock 6 with h | h
    · exact h
    · exfalso
      have hmem : t ∈ T ∩ wclass φ 6 := ⟨htT, hm.t_mem_wclass⟩
      rw [h] at hmem
      exact hmem
  have hW2not : ¬ wclass φ 2 ⊆ T := by
    intro h2
    have hunion : wclass φ 2 ∪ wclass φ 6 ⊆ T := Set.union_subset h2 hW6
    have hcard : (wclass φ 2 ∪ wclass φ 6).ncard = 16 := by
      rw [Set.ncard_union_eq (hm.perm.disjoint_wclass (by norm_num : (2 : ℕ) ≠ 6))]
      rw [IsPerm6.ncard_wclass hm.perm 2, IsPerm6.ncard_wclass hm.perm 6]
      norm_num [Nat.choose]
    have hle := Set.ncard_le_ncard hunion (Set.toFinite T)
    rw [hcard, h7T] at hle
    omega
  have hW2empty : T ∩ wclass φ 2 = ∅ := by
    rcases hblock 2 with h | h
    · exact absurd h hW2not
    · exact h
  have hnotboth : ¬ (wclass φ 1 ⊆ T ∧ wclass φ 5 ⊆ T) := by
    rintro ⟨h1, h5⟩
    have hunion : wclass φ 1 ∪ wclass φ 5 ∪ wclass φ 6 ⊆ T := by
      intro x hx
      simp only [Set.mem_union] at hx
      rcases hx with (hx1 | hx5) | hx6
      · exact h1 hx1
      · exact h5 hx5
      · exact hW6 hx6
    have hcard : (wclass φ 1 ∪ wclass φ 5 ∪ wclass φ 6).ncard = 13 := by
      rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr
        ⟨hm.perm.disjoint_wclass (by norm_num : (1 : ℕ) ≠ 6),
         hm.perm.disjoint_wclass (by norm_num : (5 : ℕ) ≠ 6)⟩)]
      rw [Set.ncard_union_eq (hm.perm.disjoint_wclass (by norm_num : (1 : ℕ) ≠ 5))]
      rw [IsPerm6.ncard_wclass hm.perm 1, IsPerm6.ncard_wclass hm.perm 5,
        IsPerm6.ncard_wclass hm.perm 6]
      norm_num [Nat.choose]
    have hle := Set.ncard_le_ncard hunion (Set.toFinite T)
    rw [hcard, h7T] at hle
    omega
  have hW1orW5 : wclass φ 1 ⊆ T ∨ wclass φ 5 ⊆ T := by
    by_cases h1 : wclass φ 1 ⊆ T
    · exact Or.inl h1
    · refine Or.inr ?_
      by_contra h5
      have h1e : T ∩ wclass φ 1 = ∅ := by
        rcases hblock 1 with h | h
        · exact absurd h h1
        · exact h
      have h5e : T ∩ wclass φ 5 = ∅ := by
        rcases hblock 5 with h | h
        · exact absurd h h5
        · exact h
      have hTW6 : T ⊆ wclass φ 6 := by
        intro x hx
        have hxU := hsub hx
        simp only [Set.mem_union] at hxU
        rcases hxU with ((hx1 | hx2) | hx5) | hx6
        · exfalso
          simpa [h1e] using (show x ∈ T ∩ wclass φ 1 from ⟨hx, hx1⟩)
        · exfalso
          simpa [hW2empty] using (show x ∈ T ∩ wclass φ 2 from ⟨hx, hx2⟩)
        · exfalso
          simpa [h5e] using (show x ∈ T ∩ wclass φ 5 from ⟨hx, hx5⟩)
        · exact hx6
      have hle := Set.ncard_le_ncard hTW6 (Set.toFinite _)
      have hc6 : (wclass φ 6).ncard = 1 := by
        rw [IsPerm6.ncard_wclass hm.perm 6]; norm_num [Nat.choose]
      rw [hc6, h7T] at hle
      omega
  rcases hW1orW5 with h1 | h5
  · left
    have h5not : ¬ wclass φ 5 ⊆ T := fun h5' => hnotboth ⟨h1, h5'⟩
    have h5e : T ∩ wclass φ 5 = ∅ := by
      rcases hblock 5 with h | h
      · exact absurd h h5not
      · exact h
    apply Set.Subset.antisymm
    · intro x hx
      have hxU := hsub hx
      simp only [Set.mem_union] at hxU ⊢
      rcases hxU with ((hx1 | hx2) | hx5) | hx6
      · exact Or.inr hx1
      · exfalso
        simpa [hW2empty] using (show x ∈ T ∩ wclass φ 2 from ⟨hx, hx2⟩)
      · exfalso
        simpa [h5e] using (show x ∈ T ∩ wclass φ 5 from ⟨hx, hx5⟩)
      · exact Or.inl hx6
    · intro x hx
      simp only [Set.mem_union] at hx
      rcases hx with hx6 | hx1
      · exact hW6 hx6
      · exact h1 hx1
  · right
    have h1not : ¬ wclass φ 1 ⊆ T := fun h1' => hnotboth ⟨h1', h5⟩
    have h1e : T ∩ wclass φ 1 = ∅ := by
      rcases hblock 1 with h | h
      · exact absurd h h1not
      · exact h
    apply Set.Subset.antisymm
    · intro x hx
      have hxU := hsub hx
      simp only [Set.mem_union] at hxU ⊢
      rcases hxU with ((hx1 | hx2) | hx5) | hx6
      · exfalso
        simpa [h1e] using (show x ∈ T ∩ wclass φ 1 from ⟨hx, hx1⟩)
      · exfalso
        simpa [hW2empty] using (show x ∈ T ∩ wclass φ 2 from ⟨hx, hx2⟩)
      · exact Or.inr hx5
      · exact Or.inl hx6
    · intro x hx
      simp only [Set.mem_union] at hx
      rcases hx with hx6 | hx5
      · exact hW6 hx6
      · exact h5 hx5

theorem sec5p510_ctx_of (hy : Sec5B59Hyp) (h58d : Asc82Lemma58d)
    (hR : Sec5RCtx G t L S z r B A)
    (h7 : Set.ncard (conjClassIn (normalizer (A : Set G)) t) = 7)
    (hnc : ¬ ∃ h : G, h⁻¹ * t * h = t * z) :
    ∃ (ρ : G) (φ : (Fin 6 → ZMod 2) → G), Sec510Ctx G t L S z r ρ B A φ := by
  obtain ⟨φ, hm⟩ := sec5b_model58_of h58d hR
  have hsyl : IsSylow2Of S (⊤ : Subgroup G) :=
    sec5c3q_isSylow2Of_top_ctx hy.h37 hy.h53 hR.toSec5Ctx hnc
  have htnz : ∀ g : G, g⁻¹ * z * g ≠ t := sec5_t_not_conj_z hy.h37 hR.toSec5Ctx
  rcases sec5p510_delta_cases hy hR hm h7 with h | h
  · refine ⟨r, φ, ?_⟩
    exact
      { toSec5RCtx := hR
        syl := hsyl
        model := hm
        nconj := hnc
        delta := h
        tnz := htnz
        zM := sec5b_zM_eq hy hR hm }
  · refine ⟨r * t, fun v => φ (sec5p510_twist v), ?_⟩
    refine
      { toSec5RCtx := hR
        syl := hsyl
        model := sec5p510_model_twist hm
        nconj := hnc
        delta := ?_
        tnz := htnz
        zM := ?_ }
    · rw [sec5p510_wclass_twist_six, sec5p510_wclass_twist_one]; exact h
    · rw [sec5p510_wclass_twist_three, sec5p510_wclass_twist_four]
      exact sec5b_zM_eq hy hR hm

end CFSG.OddStandard.SmallF3.Omega
