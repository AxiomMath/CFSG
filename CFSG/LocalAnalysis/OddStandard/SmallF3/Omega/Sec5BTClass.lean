module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BGL6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB2
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

private theorem sec5b_t_ne_one (hR : Sec5RCtx G t L S z r B A) : t ≠ 1 := by
  intro h
  have h2 := hR.involution
  rw [h, orderOf_one] at h2
  omega

private theorem sec5b_tM_subset (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    conjClassIn (normalizer (A : Set G)) t ⊆
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 := by
  intro x hx
  rcases hx with ⟨m, hmM, rfl⟩
  have hxA : m * t * m⁻¹ ∈ (A : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hmM t).mp hm.mem_A.1
  have hx1 : m * t * m⁻¹ ≠ 1 := by
    intro h
    refine sec5b_t_ne_one hR ?_
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

private theorem sec5b_tM_block (hR : Sec5RCtx G t L S z r B A)
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

theorem sec5b_tM_cases (hy : Sec5B59Hyp) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    conjClassIn (normalizer (A : Set G)) t =
        wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 ∨
      (conjClassIn (normalizer (A : Set G)) t).ncard = 7 ∨
      (conjClassIn (normalizer (A : Set G)) t).ncard = 13 ∨
      (conjClassIn (normalizer (A : Set G)) t).ncard = 22 := by
  classical
  set T : Set G := conjClassIn (normalizer (A : Set G)) t with hT
  have htT : t ∈ T := by rw [hT]; exact ⟨1, Subgroup.one_mem _, by group⟩
  have ht1 : t ≠ 1 := sec5b_t_ne_one hR
  have hsub : T ⊆ wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 := by
    rw [hT]; exact sec5b_tM_subset hy hR hm
  have hblock : ∀ k, wclass φ k ⊆ T ∨ T ∩ wclass φ k = ∅ := by
    intro k
    have h := sec5b_tM_block hR hm k
    rwa [← hT] at h
  have hstab : ∀ m ∈ normalizer (A : Set G), ∀ x ∈ T, m * x * m⁻¹ ∈ T := by
    intro m hmM x hx
    rw [hT] at hx ⊢
    rcases hx with ⟨m', hm'M, rfl⟩
    exact ⟨m * m', mul_mem hmM hm'M, by group⟩
  have hTA : T ⊆ (A : Set G) := by
    intro x hx
    rw [hT] at hx
    rcases hx with ⟨m, hmM, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hmM t).mp hm.mem_A.1
  have hirr := hy.l58b G t L S z r B A hR
  have hnotL : ¬ T ⊆ (L : Set G) :=
    hm.not_subset_L hirr hTA hstab ⟨t, htT, ht1⟩
  obtain ⟨x0, hx0T, hx0L⟩ := Set.not_subset.mp hnotL
  have hac : wclass φ 1 ⊆ T ∨ wclass φ 5 ⊆ T := by
    have hx0U := hsub hx0T
    rcases hx0U with ((hx1 | hx2) | hx5) | hx6
    · rcases hblock 1 with h | h
      · exact Or.inl h
      · exfalso
        have hmem : x0 ∈ T ∩ wclass φ 1 := ⟨hx0T, hx1⟩
        rw [h] at hmem
        exact hmem
    · exfalso
      exact hx0L ((hm.mem_L_iff hx2).mpr ⟨1, by norm_num⟩)
    · rcases hblock 5 with h | h
      · exact Or.inr h
      · exfalso
        have hmem : x0 ∈ T ∩ wclass φ 5 := ⟨hx0T, hx5⟩
        rw [h] at hmem
        exact hmem
    · exfalso
      exact hx0L ((hm.mem_L_iff hx6).mpr ⟨3, by norm_num⟩)
  have hW6 : wclass φ 6 ⊆ T := by
    rcases hblock 6 with h | h
    · exact h
    · exfalso
      have hmem : t ∈ T ∩ wclass φ 6 := ⟨htT, hm.t_mem_wclass⟩
      rw [h] at hmem
      exact hmem
  have hdecomp : T = (T ∩ wclass φ 1) ∪ (T ∩ wclass φ 2) ∪ (T ∩ wclass φ 5) ∪
      (T ∩ wclass φ 6) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxU := hsub hx
      simp only [Set.mem_union] at hxU
      simp only [Set.mem_union, Set.mem_inter_iff]
      tauto
    · intro x hx
      simp only [Set.mem_union, Set.mem_inter_iff] at hx
      tauto
  have hd : ∀ j k : ℕ, j ≠ k → Disjoint (T ∩ wclass φ j) (T ∩ wclass φ k) :=
    fun j k hjk => (hm.perm.disjoint_wclass hjk).mono Set.inter_subset_right Set.inter_subset_right
  have hd12 : Disjoint (T ∩ wclass φ 1) (T ∩ wclass φ 2) := hd 1 2 (by norm_num)
  have hd15 : Disjoint (T ∩ wclass φ 1) (T ∩ wclass φ 5) := hd 1 5 (by norm_num)
  have hd16 : Disjoint (T ∩ wclass φ 1) (T ∩ wclass φ 6) := hd 1 6 (by norm_num)
  have hd25 : Disjoint (T ∩ wclass φ 2) (T ∩ wclass φ 5) := hd 2 5 (by norm_num)
  have hd26 : Disjoint (T ∩ wclass φ 2) (T ∩ wclass φ 6) := hd 2 6 (by norm_num)
  have hd56 : Disjoint (T ∩ wclass φ 5) (T ∩ wclass φ 6) := hd 5 6 (by norm_num)
  have hncard : T.ncard = (T ∩ wclass φ 1).ncard + (T ∩ wclass φ 2).ncard +
      (T ∩ wclass φ 5).ncard + (T ∩ wclass φ 6).ncard := by
    conv_lhs => rw [hdecomp]
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨hd16, hd26⟩, hd56⟩)]
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hd15, hd25⟩)]
    rw [Set.ncard_union_eq hd12]
  have hc1 : Nat.choose 6 1 = 6 := by decide
  have hc2 : Nat.choose 6 2 = 15 := by decide
  have hc5 : Nat.choose 6 5 = 6 := by decide
  have hc6 : Nat.choose 6 6 = 1 := by decide
  have hS1 : (T ∩ wclass φ 1).ncard = if wclass φ 1 ⊆ T then 6 else 0 := by
    by_cases h : wclass φ 1 ⊆ T
    · rw [if_pos h, Set.inter_eq_right.mpr h, hm.perm.ncard_wclass 1, hc1]
    · rw [if_neg h]
      rcases hblock 1 with hh | hh
      · exact absurd hh h
      · rw [hh, Set.ncard_empty]
  have hS2 : (T ∩ wclass φ 2).ncard = if wclass φ 2 ⊆ T then 15 else 0 := by
    by_cases h : wclass φ 2 ⊆ T
    · rw [if_pos h, Set.inter_eq_right.mpr h, hm.perm.ncard_wclass 2, hc2]
    · rw [if_neg h]
      rcases hblock 2 with hh | hh
      · exact absurd hh h
      · rw [hh, Set.ncard_empty]
  have hS5 : (T ∩ wclass φ 5).ncard = if wclass φ 5 ⊆ T then 6 else 0 := by
    by_cases h : wclass φ 5 ⊆ T
    · rw [if_pos h, Set.inter_eq_right.mpr h, hm.perm.ncard_wclass 5, hc5]
    · rw [if_neg h]
      rcases hblock 5 with hh | hh
      · exact absurd hh h
      · rw [hh, Set.ncard_empty]
  have hS6 : (T ∩ wclass φ 6).ncard = 1 := by
    rw [Set.inter_eq_right.mpr hW6, hm.perm.ncard_wclass 6, hc6]
  by_cases h1 : wclass φ 1 ⊆ T
  · by_cases h2 : wclass φ 2 ⊆ T
    · by_cases h5 : wclass φ 5 ⊆ T
      · left
        apply Set.Subset.antisymm hsub
        apply Set.union_subset
        · apply Set.union_subset
          · apply Set.union_subset
            · exact h1
            · exact h2
          · exact h5
        · exact hW6
      · right; right; right
        rw [hncard, hS1, hS2, hS5, hS6, if_pos h1, if_pos h2, if_neg h5]
    · by_cases h5 : wclass φ 5 ⊆ T
      · right; right; left
        rw [hncard, hS1, hS2, hS5, hS6, if_pos h1, if_neg h2, if_pos h5]
      · right; left
        rw [hncard, hS1, hS2, hS5, hS6, if_pos h1, if_neg h2, if_neg h5]
  · by_cases h2 : wclass φ 2 ⊆ T
    · by_cases h5 : wclass φ 5 ⊆ T
      · right; right; right
        rw [hncard, hS1, hS2, hS5, hS6, if_neg h1, if_pos h2, if_pos h5]
      · exfalso
        rcases hac with h | h
        · exact h1 h
        · exact h5 h
    · by_cases h5 : wclass φ 5 ⊆ T
      · right; left
        rw [hncard, hS1, hS2, hS5, hS6, if_neg h1, if_neg h2, if_pos h5]
      · exfalso
        rcases hac with h | h
        · exact h1 h
        · exact h5 h

theorem sec5b_tM_eq (hy : Sec5B59Hyp) (f510 : Asc82Fact510) (hR : Sec5RCtx G t L S z r B A)
    (hm : Sec5Model58 t L z r A φ) :
    conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6 := by
  rcases sec5b_tM_cases hy hR hm with h | h7 | h13 | h22
  · exact h
  · exact absurd h7 (f510 G t L S z r B A hR)
  · exact absurd h13 (hm.perm.ncard_conjClass_ne_thirteen hm.mem_A.1)
  · exact absurd h22 (hm.perm.ncard_conjClass_ne_twentytwo hm.mem_A.1)

end CFSG.OddStandard.SmallF3.Omega
