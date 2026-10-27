module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BTClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

private theorem sec5b_tG_inter_A_eq (hy : Sec5B59Hyp) (f510 : Asc82Fact510)
    (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ) :
    conjClassIn ⊤ t ∩ (A : Set G) =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxG, hxA⟩
    obtain ⟨h, -, rfl⟩ := hxG
    have ht2 : orderOf t = 2 := hR.involution
    have hx1 : h * t * h⁻¹ ≠ 1 := by
      intro hone
      have ht1 : t = 1 := by
        calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
          _ = 1 := by rw [hone]; group
      rw [ht1, orderOf_one] at ht2
      omega
    obtain ⟨k, hk1, hk6, hxWk⟩ := hm.perm.exists_wclass_pos hxA hx1
    have hzM : conjClassIn (normalizer (A : Set G)) z = wclass φ 3 ∪ wclass φ 4 :=
      sec5b_zM_eq hy hR hm
    have hxnotzM : h * t * h⁻¹ ∉ conjClassIn (normalizer (A : Set G)) z := by
      intro hz
      obtain ⟨m, -, hmz⟩ := hz
      have hconj : (m⁻¹ * h)⁻¹ * z * (m⁻¹ * h) = t := by
        calc (m⁻¹ * h)⁻¹ * z * (m⁻¹ * h) = h⁻¹ * (m * z * m⁻¹) * h := by group
          _ = t := by rw [← hmz]; group
      exact (sec5_t_not_conj_z hy.h37 hR.toSec5Ctx (m⁻¹ * h)) hconj
    have hk3 : k ≠ 3 := by
      rintro rfl
      exact hxnotzM (by rw [hzM]; exact Or.inl hxWk)
    have hk4 : k ≠ 4 := by
      rintro rfl
      exact hxnotzM (by rw [hzM]; exact Or.inr hxWk)
    have hk : k = 1 ∨ k = 2 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk with rfl | rfl | rfl | rfl <;> (simp only [Set.mem_union]; tauto)
  · intro x hx
    have hxM : x ∈ conjClassIn (normalizer (A : Set G)) t := by
      rw [sec5b_tM_eq hy f510 hR hm]
      exact hx
    refine ⟨?_, ?_⟩
    · obtain ⟨m, hmM, hmx⟩ := hxM
      exact ⟨m, trivial, hmx⟩
    · rcases hx with ((hx1 | hx2) | hx5) | hx6
      · exact hm.perm.wclass_subset 1 hx1
      · exact hm.perm.wclass_subset 2 hx2
      · exact hm.perm.wclass_subset 5 hx5
      · exact hm.perm.wclass_subset 6 hx6

private theorem sec5b_gamma_eq (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    ((A : Set G) \ {1}) \ conjClassIn (normalizer (A : Set G)) z =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 := by
  rw [sec5b_zM_eq hy hR hm]
  have hne_one : ∀ {k : ℕ}, k ≠ 0 → ∀ {x : G}, x ∈ wclass φ k → x ≠ 1 := by
    intro k hk0 x hxk hx1
    have hx0 : x ∈ wclass φ 0 := by
      rw [hm.perm.wclass_zero]
      exact Set.mem_singleton_iff.mpr hx1
    exact (Set.disjoint_left.mp (hm.perm.disjoint_wclass hk0) hxk) hx0
  have hnot34 : ∀ {k : ℕ}, k ≠ 3 → k ≠ 4 → ∀ {x : G},
      x ∈ wclass φ k → x ∉ wclass φ 3 ∪ wclass φ 4 := by
    intro k hk3 hk4 x hxk hx
    rcases hx with h3 | h4
    · exact (Set.disjoint_left.mp (hm.perm.disjoint_wclass hk3) hxk) h3
    · exact (Set.disjoint_left.mp (hm.perm.disjoint_wclass hk4) hxk) h4
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk1, hk6, hxWk⟩ := hm.perm.exists_wclass_pos hx.1.1 hx.1.2
    have hk3 : k ≠ 3 := by
      rintro rfl
      exact hx.2 (Or.inl hxWk)
    have hk4 : k ≠ 4 := by
      rintro rfl
      exact hx.2 (Or.inr hxWk)
    have hk : k = 1 ∨ k = 2 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk with rfl | rfl | rfl | rfl <;> (simp only [Set.mem_union]; tauto)
  · intro x hx
    rcases hx with ((hx1 | hx2) | hx5) | hx6
    · exact ⟨⟨hm.perm.wclass_subset 1 hx1, hne_one (by norm_num) hx1⟩,
        hnot34 (by norm_num) (by norm_num) hx1⟩
    · exact ⟨⟨hm.perm.wclass_subset 2 hx2, hne_one (by norm_num) hx2⟩,
        hnot34 (by norm_num) (by norm_num) hx2⟩
    · exact ⟨⟨hm.perm.wclass_subset 5 hx5, hne_one (by norm_num) hx5⟩,
        hnot34 (by norm_num) (by norm_num) hx5⟩
    · exact ⟨⟨hm.perm.wclass_subset 6 hx6, hne_one (by norm_num) hx6⟩,
        hnot34 (by norm_num) (by norm_num) hx6⟩

theorem sec5b_case59_sets (hy : Sec5B59Hyp) (f510 : Asc82Fact510)
    (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ) :
    conjClassIn ⊤ t ∩ (A : Set G) =
        ((A : Set G) \ {1}) \ conjClassIn (normalizer (A : Set G)) z ∧
      conjClassIn ⊤ t ∩ (A : Set G) = conjClassIn (normalizer (A : Set G)) t ∧
      Set.ncard (conjClassIn ⊤ t ∩ (A : Set G)) = 28 := by
  have hmain := sec5b_tG_inter_A_eq hy f510 hR hm
  refine ⟨?_, ?_, ?_⟩
  · rw [hmain, sec5b_gamma_eq hy hR hm]
  · rw [hmain, sec5b_tM_eq hy f510 hR hm]
  · rw [hmain]
    have hd12 : Disjoint (wclass φ 1) (wclass φ 2) := hm.perm.disjoint_wclass (by norm_num)
    have hd15 : Disjoint (wclass φ 1) (wclass φ 5) := hm.perm.disjoint_wclass (by norm_num)
    have hd16 : Disjoint (wclass φ 1) (wclass φ 6) := hm.perm.disjoint_wclass (by norm_num)
    have hd25 : Disjoint (wclass φ 2) (wclass φ 5) := hm.perm.disjoint_wclass (by norm_num)
    have hd26 : Disjoint (wclass φ 2) (wclass φ 6) := hm.perm.disjoint_wclass (by norm_num)
    have hd56 : Disjoint (wclass φ 5) (wclass φ 6) := hm.perm.disjoint_wclass (by norm_num)
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨hd16, hd26⟩, hd56⟩)]
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hd15, hd25⟩)]
    rw [Set.ncard_union_eq hd12]
    rw [IsPerm6.ncard_wclass hm.perm 1, IsPerm6.ncard_wclass hm.perm 2,
      IsPerm6.ncard_wclass hm.perm 5, IsPerm6.ncard_wclass hm.perm 6]
    norm_num [Nat.choose]

end CFSG.OddStandard.SmallF3.Omega
