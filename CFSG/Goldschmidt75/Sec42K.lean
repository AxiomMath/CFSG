module

public import CFSG.Goldschmidt75.Sec42
public import CFSG.Goldschmidt75.WeakClosure

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def kSub (S₁ S₂ : Subgroup G) : Subgroup G :=
  normalClosureIn (normalizer (S₂ : Set G)) S₁

omit [Finite G] in
theorem kSub_le_normalizer {S₁ S₂ : Subgroup G} : kSub S₁ S₂ ≤ normalizer (S₂ : Set G) :=
  map_subtype_le _

omit [Finite G] in
theorem le_kSub {S₁ S₂ : Subgroup G} (h : S₁ ≤ normalizer (S₂ : Set G)) : S₁ ≤ kSub S₁ S₂ :=
  fun x hx => ⟨⟨x, h hx⟩, subset_normalClosure (mem_subgroupOf.mpr hx), rfl⟩

omit [Finite G] in
theorem conj_mem_kSub {S₁ S₂ : Subgroup G} {n y : G} (hn : n ∈ normalizer (S₂ : Set G))
    (hy : y ∈ kSub S₁ S₂) : n * y * n⁻¹ ∈ kSub S₁ S₂ := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨n, hn⟩ * y' * ⟨n, hn⟩⁻¹, (normalClosure_normal).conj_mem _ hy' _, rfl⟩

omit [Finite G] in
theorem normal_centralizer_subgroupOf (S : Subgroup G) :
    ((centralizer (S : Set G)).subgroupOf (normalizer (S : Set G))).Normal := by
  refine ⟨fun c hc n => ?_⟩
  rw [mem_subgroupOf, mem_centralizer_iff] at hc ⊢
  intro s hs
  have h1 : (n : G)⁻¹ * s * n ∈ S := by
    have := (mem_normalizer_iff.mp (inv_mem n.2) s).mp hs
    simpa using this
  have h2 := hc _ h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc s * ((n : G) * c * (n : G)⁻¹) = n * ((n : G)⁻¹ * s * n * c) * (n : G)⁻¹ := by group
    _ = n * (c * ((n : G)⁻¹ * s * n)) * (n : G)⁻¹ := by rw [h2]
    _ = (n : G) * c * (n : G)⁻¹ * s := by group

omit [Finite G] in
theorem kSub_le_centralizer {S₁ S₂ : Subgroup G} (h : S₁ ≤ centralizer (S₂ : Set G)) :
    kSub S₁ S₂ ≤ centralizer (S₂ : Set G) := by
  have := normal_centralizer_subgroupOf S₂
  have hle : normalClosure ((S₁.subgroupOf (normalizer (S₂ : Set G)) : Subgroup _) : Set _) ≤
      (centralizer (S₂ : Set G)).subgroupOf (normalizer (S₂ : Set G)) :=
    normalClosure_le_normal fun x hx => mem_subgroupOf.mpr (h (mem_subgroupOf.mp hx))
  rintro _ ⟨y, hy, rfl⟩
  exact mem_subgroupOf.mp (hle hy)

variable {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.false_of_lt (h : MinCE G T S₁ S₂) {R : Subgroup G} (hRS : R < S₁) (hR1 : R ≠ ⊥)
    (hRcl : fusionStronglyClosed (R : Set G) T) : False := by
  have hO := h.oddCore_eq_bot
  have hRlt : Nat.card R < Nat.card S₁ := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hRS.le) fun hc => hRS.ne ?_
    exact Subgroup.eq_of_le_of_card_ge hRS.le hc.ge
  have hS₂pos : 0 < Nat.card S₂ := Nat.card_pos
  have hihS := h.ihS T R S₂ (hRS.le.trans h.le₁) h.le₂ hRcl h.sc₂
    (hRS.le.trans h.comm) (le_bot_iff.mp (h.disj ▸ inf_le_inf_right _ hRS.le))
    (Nat.mul_lt_mul_of_pos_right hRlt hS₂pos)
  rw [hO, le_bot_iff] at hihS
  have hM1 : normalClosure (R : Set G) ≠ ⊥ := fun h0 =>
    hR1 (le_bot_iff.mp (h0 ▸ le_normalClosure))
  apply h.symm.not_le_centralizer normalClosure_normal hM1
  rw [← commutator_eq_bot_iff_le_centralizer]
  exact le_bot_iff.mp (hihS ▸ commutator_mono le_rfl le_normalClosure)

theorem MinCE.kSub_le_closure (h : MinCE G T S₁ S₂) :
    kSub S₁ S₂ ≤ closure {y | ∃ k ∈ kSub S₁ S₂, ∃ s ∈ S₁, s ^ 2 = 1 ∧ y = k * s * k⁻¹} := by
  set N₂ := normalizer (S₂ : Set G) with hN₂
  set D := {y | ∃ k ∈ kSub S₁ S₂, ∃ s ∈ S₁, s ^ 2 = 1 ∧ y = k * s * k⁻¹} with hD
  set Kh := closure D with hKh
  have hS₁N : S₁ ≤ N₂ := h.comm.trans (centralizer_le_normalizer _)
  have hS₁K : S₁ ≤ kSub S₁ S₂ := le_kSub hS₁N
  have hKhK : Kh ≤ kSub S₁ S₂ := (closure_le _).mpr fun y ⟨k, hk, s, hs, _, hy⟩ =>
    hy ▸ mul_mem (mul_mem hk (hS₁K hs)) (inv_mem hk)
  have hDn : ∀ n ∈ N₂, ∀ y ∈ D, n * y * n⁻¹ ∈ D := by
    rintro n hn y ⟨k, hk, s, hs, hs2, rfl⟩
    obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosureIn T h.le₁ h.sc₁ hS₁N (inv_mem hn)
    have h1 : n * s * n⁻¹ ∈ conjSub n⁻¹ S₁ := by
      rw [mem_conjSub]
      simpa [mul_assoc] using hs
    rw [hmeq, mem_conjSub] at h1
    refine ⟨n * k * n⁻¹ * m⁻¹, mul_mem (conj_mem_kSub hn hk) (inv_mem hm),
      m * (n * s * n⁻¹) * m⁻¹, h1, ?_, by group⟩
    have e : (m * (n * s * n⁻¹) * m⁻¹) ^ 2 = m * n * s ^ 2 * n⁻¹ * m⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [e, hs2]
    group
  have hconj : ∀ n ∈ N₂, ∀ y ∈ Kh, n * y * n⁻¹ ∈ Kh := by
    intro n hn y hy
    have hle : Kh ≤ Kh.comap (MulAut.conj n).toMonoidHom :=
      (closure_le _).mpr fun z hz => subset_closure (hDn n hn z hz)
    exact hle hy
  have hKhN : N₂ ≤ normalizer (Kh : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hconj n hn y, fun hy => ?_⟩
    have := hconj n⁻¹ (inv_mem hn) _ hy
    simpa [mul_assoc] using this
  by_cases hS : S₁ ≤ Kh
  · have hn : (Kh.subgroupOf N₂).Normal :=
      (normal_subgroupOf_iff_le_normalizer (hKhK.trans kSub_le_normalizer)).mpr hKhN
    have h1 : normalClosure ((S₁.subgroupOf N₂ : Subgroup N₂) : Set N₂) ≤ Kh.subgroupOf N₂ :=
      normalClosure_le_normal fun x hx => mem_subgroupOf.mpr (hS (mem_subgroupOf.mp hx))
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp (h1 hx)
  · exfalso
    have hRcl : fusionStronglyClosed ((S₁ ⊓ Kh : Subgroup G) : Set G) T := by
      intro a ha g hg
      have hb := h.sc₁ a ha.1 g hg
      obtain ⟨m, hm, hmeq⟩ := exists_normalizer_conj T h.le₂ h.sc₂ (h.comm ha.1) (h.comm hb)
      refine ⟨hb, ?_⟩
      rw [SetLike.mem_coe, ← hmeq]
      have := (mem_normalizer_iff.mp (hKhN (inv_mem hm)) a).mp ha.2
      simpa using this
    obtain ⟨z, hzS, hz2, -⟩ := exists_central_involution T h.le₁ h.sc₁ h.ne_bot
    have hzKh : z ∈ Kh := subset_closure ⟨1, one_mem _, z, hzS,
      by rw [← hz2]; exact pow_orderOf_eq_one z, by group⟩
    refine h.false_of_lt (lt_of_le_of_ne inf_le_left fun he => hS (he ▸ inf_le_right)) ?_ hRcl
    intro h0
    have : z ∈ S₁ ⊓ Kh := ⟨hzS, hzKh⟩
    rw [h0, mem_bot] at this
    exact ne_one_of_orderOf_eq_two hz2 this

end CFSG.Goldschmidt75
