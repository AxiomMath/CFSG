module

public import CFSG.CGT.Timmesfeld75.Config

public section

namespace CFSG.CGT.T75JM

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

structure TCtx (T T₁ : Subgroup G) : Prop where
  wc : IsWC T
  inf_bot : T ⊓ T₁ = ⊥
  conj : ∃ s : G, T₁ = conjSubgroup s T
  norm1 : Nat.card (normIn T T₁) = 4
  norm2 : Nat.card (normIn T₁ T) = 4

theorem inter_unique {T : Subgroup G} (hT : IsWC T) {a b x : G} (hxa : x ∈ conjSubgroup a T)
    (hxb : x ∈ conjSubgroup b T) (hx1 : x ≠ 1) : conjSubgroup a T = conjSubgroup b T := by
  rw [mem_conjSubgroup] at hxa hxb
  have hne : T ⊓ conjSubgroup (a⁻¹ * b) T ≠ ⊥ := by
    intro hbot
    have hmem : a⁻¹ * x * a ∈ T ⊓ conjSubgroup (a⁻¹ * b) T := by
      refine Subgroup.mem_inf.2 ⟨hxa, ?_⟩
      rw [mem_conjSubgroup]
      have : (a⁻¹ * b)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * b) = b⁻¹ * x * b := by group
      rw [this]
      exact hxb
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hx1
    have : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    rw [this, hmem]
    group
  have h1 := hT.conj_eq_of_inf_ne_bot hne
  have h2 : conjSubgroup a (conjSubgroup (a⁻¹ * b) T) = conjSubgroup a T := by rw [h1]
  rw [conjSubgroup_conjSubgroup] at h2
  simpa using h2.symm

theorem mem_normalizer_conj {T : Subgroup G} {s x : G} :
    x ∈ Subgroup.normalizer ((conjSubgroup s T : Subgroup G) : Set G) ↔
      s⁻¹ * x * s ∈ Subgroup.normalizer (T : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, mem_normalizer_iff_conjSubgroup_eq,
    conjSubgroup_conjSubgroup]
  constructor
  · intro h
    have h2 : conjSubgroup s⁻¹ (conjSubgroup (x * s) T) = conjSubgroup s⁻¹ (conjSubgroup s T) := by
      rw [h]
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at h2
    simpa [mul_assoc, conjSubgroup_one] using h2
  · intro h
    have h2 : conjSubgroup s (conjSubgroup (s⁻¹ * x * s) T) = conjSubgroup s T := by rw [h]
    rw [conjSubgroup_conjSubgroup] at h2
    simpa [mul_assoc] using h2

theorem mem_normalizer_inf' {K L : Subgroup G} {n : G}
    (hK : n ∈ Subgroup.normalizer (K : Set G)) (hL : n ∈ Subgroup.normalizer (L : Set G)) :
    n ∈ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hK hL ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hK x, hL x]

theorem exists_ne_one_of_one_lt_card {K : Subgroup G} (h : 1 < Nat.card K) :
    ∃ x ∈ K, x ≠ 1 := by
  have hK : K ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h
    omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hK
  exact ⟨x, hx, fun h' => hx1 (Subtype.ext h')⟩

namespace TCtx

variable {T T₁ : Subgroup G} (h : TCtx T T₁)
include h

theorem wc₁ : IsWC T₁ := by
  obtain ⟨s, rfl⟩ := h.conj
  exact h.wc.conj s

theorem elemAbelian₁ : IsElemAbelian 2 T₁ := h.wc₁.1

theorem symm : TCtx T₁ T where
  wc := h.wc₁
  inf_bot := by rw [inf_comm]; exact h.inf_bot
  conj := by
    obtain ⟨s, hs⟩ := h.conj
    refine ⟨s⁻¹, ?_⟩
    rw [hs, conjSubgroup_conjSubgroup]
    simp [conjSubgroup_one]
  norm1 := h.norm2
  norm2 := h.norm1

theorem mem_normalizer_B_iff {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    n ∈ Subgroup.normalizer ((normIn T₁ T : Subgroup G) : Set G) ↔
      n ∈ Subgroup.normalizer (T₁ : Set G) := by
  constructor
  · intro hnB
    obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_one_lt_card (K := normIn T₁ T)
      (by rw [h.norm2]; norm_num)
    have hb' : n * b * n⁻¹ ∈ normIn T₁ T := (Subgroup.mem_normalizer_iff.1 hnB b).1 hb
    have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
    have hb'T₁ : n * b * n⁻¹ ∈ T₁ := (mem_normIn.1 hb').1
    have hb'1 : n * b * n⁻¹ ≠ 1 := by
      intro h1
      apply hb1
      have : b = n⁻¹ * (n * b * n⁻¹) * n := by group
      rw [this, h1]
      group
    obtain ⟨s, hs⟩ := h.conj
    have hmem1 : n * b * n⁻¹ ∈ conjSubgroup s T := by rw [← hs]; exact hb'T₁
    have hmem2 : n * b * n⁻¹ ∈ conjSubgroup (n * s) T := by
      rw [← conjSubgroup_conjSubgroup, ← hs, mem_conjSubgroup]
      simpa [mul_assoc] using hbT₁
    have heq := inter_unique h.wc hmem1 hmem2 hb'1
    rw [← hs, ← conjSubgroup_conjSubgroup, ← hs] at heq
    rw [mem_normalizer_iff_conjSubgroup_eq]
    exact heq.symm
  · intro hn1
    exact mem_normalizer_inf' hn1 (Subgroup.le_normalizer hn)

theorem mem_normalizer_A_iff {n : G} (hn : n ∈ Subgroup.normalizer (T₁ : Set G)) :
    n ∈ Subgroup.normalizer ((normIn T T₁ : Subgroup G) : Set G) ↔
      n ∈ Subgroup.normalizer (T : Set G) :=
  h.symm.mem_normalizer_B_iff hn

theorem comm_A_B {a b : G} (ha : a ∈ normIn T T₁) (hb : b ∈ normIn T₁ T) : a * b = b * a := by
  have haT : a ∈ T := (mem_normIn.1 ha).1
  have haN₁ : a ∈ Subgroup.normalizer (T₁ : Set G) := (mem_normIn.1 ha).2
  have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hb).2
  have haN : a ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer haT
  have hbN₁ : b ∈ Subgroup.normalizer (T₁ : Set G) := Subgroup.le_normalizer hbT₁
  have h1 : a * b * a⁻¹ ∈ normIn T₁ T :=
    (Subgroup.mem_normalizer_iff.1 ((h.mem_normalizer_B_iff haN).2 haN₁) b).1 hb
  have h2 : b * a * b⁻¹ ∈ normIn T T₁ :=
    (Subgroup.mem_normalizer_iff.1 ((h.mem_normalizer_A_iff hbN₁).2 hbN) a).1 ha
  have hc1 : a * b * a⁻¹ * b⁻¹ ∈ T₁ :=
    T₁.mul_mem (mem_normIn.1 h1).1 (T₁.inv_mem hbT₁)
  have hc2 : a * b * a⁻¹ * b⁻¹ ∈ T := by
    have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [this]
    refine T.mul_mem haT ?_
    have h3 : (b * a * b⁻¹)⁻¹ ∈ T := T.inv_mem (mem_normIn.1 h2).1
    simpa [mul_assoc] using h3
  have hbot : a * b * a⁻¹ * b⁻¹ ∈ T ⊓ T₁ := ⟨hc2, hc1⟩
  rw [h.inf_bot, Subgroup.mem_bot] at hbot
  have : a * b = b * a := by
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hbot]; group
  exact this

end TCtx

end CFSG.CGT.T75JM
