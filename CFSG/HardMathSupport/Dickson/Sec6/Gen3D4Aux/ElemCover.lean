module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterElem

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.Open CFSG.AGLEmbedding.ChevOuter

variable {G : Type*} [Group G]

theorem independent_of_chain (x y z : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (h1 : x ≠ 1) (h2 : y ∉ Subgroup.closure {x}) (h3 : z ∉ Subgroup.closure {x, y}) :
    ∀ a b c : ℕ, a < 3 → b < 3 → c < 3 → x ^ a * y ^ b * z ^ c = 1 → a = 0 ∧ b = 0 ∧ c = 0 := by
  have hxm : ∀ n : ℕ, x ^ n ∈ Subgroup.closure {x, y} := fun n =>
    Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) n
  have hym : ∀ n : ℕ, y ^ n ∈ Subgroup.closure {x, y} := fun n =>
    Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) n
  have hxm1 : ∀ n : ℕ, x ^ n ∈ Subgroup.closure {x} := fun n =>
    Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) n
  intro a b c ha hb hc h
  have hc0 : c = 0 := by
    by_contra hne
    apply h3
    have hzc : z ^ c = (x ^ a * y ^ b)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hmem : z ^ c ∈ Subgroup.closure {x, y} := by
      rw [hzc]; exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (hxm a) (hym b))
    interval_cases c
    · exact absurd rfl hne
    · simpa using hmem
    · have : z = (z ^ 2) ^ 2 := by
        calc z = z ^ 3 * z := by rw [hz, one_mul]
          _ = (z ^ 2) ^ 2 := by group
      rw [this]
      exact Subgroup.pow_mem _ hmem 2
  subst hc0
  simp only [pow_zero, mul_one] at h
  have hb0 : b = 0 := by
    by_contra hne
    apply h2
    have hyb : y ^ b = (x ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hmem : y ^ b ∈ Subgroup.closure {x} := by
      rw [hyb]; exact Subgroup.inv_mem _ (hxm1 a)
    interval_cases b
    · exact absurd rfl hne
    · simpa using hmem
    · have : y = (y ^ 2) ^ 2 := by
        calc y = y ^ 3 * y := by rw [hy, one_mul]
          _ = (y ^ 2) ^ 2 := by group
      rw [this]
      exact Subgroup.pow_mem _ hmem 2
  subst hb0
  simp only [pow_zero, mul_one] at h
  have ha0 : a = 0 := by
    by_contra hne
    apply h1
    interval_cases a
    · exact absurd rfl hne
    · simpa using h
    · calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx, h]; simp
  exact ⟨ha0, rfl, rfl⟩

variable [Finite G]

theorem elem_abelian_le_cover {ι : Type*} (P : Subgroup G) (M : ι → Subgroup G)
    (hM : ∀ t, Nat.card (M t) = 27)
    (H3 : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, x ^ 3 = 1 → y ^ 3 = 1 → z ^ 3 = 1 →
      Commute x y → Commute x z → Commute y z → ∃ t, x ∈ M t ∧ y ∈ M t ∧ z ∈ M t)
    (H4 : ∀ t, ∀ w ∈ P, w ^ 3 = 1 → (∀ m ∈ M t, Commute w m) → w ∈ M t)
    (B : Subgroup G) (hBP : B ≤ P) (hB : IsElemAbelian 3 B) : ∃ t, B ≤ M t := by
  classical
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcube : ∀ x ∈ B, x ^ 3 = 1 := hB.2
  have key : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, ∃ t, Subgroup.closure {x, y, z} ≤ M t := by
    intro x hx y hy z hz
    obtain ⟨t, hxt, hyt, hzt⟩ := H3 x (hBP hx) y (hBP hy) z (hBP hz) (hcube x hx) (hcube y hy)
      (hcube z hz) (hcomm x hx y hy) (hcomm x hx z hz) (hcomm y hy z hz)
    refine ⟨t, ?_⟩
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  suffices hsuff : ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, B ≤ Subgroup.closure {x, y, z} by
    obtain ⟨x, hx, y, hy, z, hz, hle⟩ := hsuff
    obtain ⟨t, ht⟩ := key x hx y hy z hz
    exact ⟨t, hle.trans ht⟩
  by_cases hA : ∀ b ∈ B, b = 1
  · refine ⟨1, B.one_mem, 1, B.one_mem, 1, B.one_mem, fun b hb => ?_⟩
    rw [hA b hb]
    exact Subgroup.one_mem _
  push Not at hA
  obtain ⟨x1, hx1B, hx1⟩ := hA
  by_cases hB1 : B ≤ Subgroup.closure {x1}
  · refine ⟨x1, hx1B, 1, B.one_mem, 1, B.one_mem, hB1.trans ?_⟩
    exact Subgroup.closure_mono (by intro g hg; simp at hg ⊢; exact Or.inl hg)
  rw [SetLike.not_le_iff_exists] at hB1
  obtain ⟨x2, hx2B, hx2⟩ := hB1
  by_cases hB2 : B ≤ Subgroup.closure {x1, x2}
  · refine ⟨x1, hx1B, x2, hx2B, 1, B.one_mem, hB2.trans ?_⟩
    exact Subgroup.closure_mono (by intro g hg; simp at hg ⊢; tauto)
  rw [SetLike.not_le_iff_exists] at hB2
  obtain ⟨x3, hx3B, hx3⟩ := hB2
  by_cases hB3 : B ≤ Subgroup.closure {x1, x2, x3}
  · exact ⟨x1, hx1B, x2, hx2B, x3, hx3B, hB3⟩
  rw [SetLike.not_le_iff_exists] at hB3
  obtain ⟨x4, hx4B, hx4⟩ := hB3
  exfalso
  have hind := independent_of_chain x1 x2 x3 (hcube x1 hx1B) (hcube x2 hx2B) (hcube x3 hx3B)
    hx1 hx2 hx3
  obtain ⟨-, -, hcard⟩ := closure_triple x1 x2 x3 (hcube x1 hx1B) (hcube x2 hx2B) (hcube x3 hx3B)
    (hcomm x1 hx1B x2 hx2B) (hcomm x1 hx1B x3 hx3B) (hcomm x2 hx2B x3 hx3B) hind
  obtain ⟨t, ht⟩ := key x1 hx1B x2 hx2B x3 hx3B
  have heq : Subgroup.closure {x1, x2, x3} = M t :=
    Subgroup.eq_of_le_of_card_ge ht (by rw [hM t, hcard]; norm_num)
  have hCB : Subgroup.closure {x1, x2, x3} ≤ B := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  apply hx4
  rw [heq]
  exact H4 t x4 (hBP hx4B) (hcube x4 hx4B) fun m hm =>
    hcomm x4 hx4B m (hCB (heq ▸ hm))

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
