module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiModel

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

structure Fi24InBase (Y : Type) [Group Y] (uY : Y) (KY : Subgroup Y) : Prop where
  u_sq : uY * uY = 1
  u_ne_one : uY ≠ 1
  u_mem : uY ∈ KY
  le_centralizer : KY ≤ centralizer ({uY} : Set Y)
  card_le : Nat.card (centralizer ({uY} : Set Y)) ≤ 2 * Nat.card KY
  perfect : ⁅KY, KY⁆ = KY
  cent : ∀ z : Y, (∀ k ∈ KY, z * k = k * z) → z = 1 ∨ z = uY
  induced : ∀ α : MulAut KY, ∃ y ∈ centralizer ({uY} : Set Y),
    ∀ k : KY, ((α k : KY) : Y) = y * k * y⁻¹
  outTwo : OutTwo Y

section Derived

variable {Y : Type} [Group Y] {uY : Y} {KY : Subgroup Y}

theorem Fi24InBase.cent_subset (h : Fi24InBase Y uY KY) :
    ((centralizer (KY : Set Y) : Subgroup Y) : Set Y) ⊆ {1, uY} := fun z hz =>
  h.cent z fun k hk => (mem_centralizer_iff.1 hz k hk).symm

theorem Fi24InBase.card_centralizer_le [Finite Y] (h : Fi24InBase Y uY KY) :
    Nat.card (centralizer (KY : Set Y)) ≤ 2 := by
  calc Nat.card (centralizer (KY : Set Y))
      = ((centralizer (KY : Set Y) : Subgroup Y) : Set Y).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ ({1, uY} : Set Y).ncard := Set.ncard_le_ncard h.cent_subset (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem fi24in_le_normalizer_of_card_le {G : Type} [Group G] [Finite G] {K C : Subgroup G}
    (hle : K ≤ C) (hcard : Nat.card C ≤ 2 * Nat.card K) : C ≤ normalizer (K : Set G) := by
  have hc : Nat.card ↥(K.subgroupOf C) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hmul := (K.subgroupOf C).card_mul_index
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h0 : (K.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : (K.subgroupOf C).index ≤ 2 := by
    rw [hc] at hmul
    nlinarith
  have hn : (K.subgroupOf C).Normal := by
    rcases (by omega : (K.subgroupOf C).index = 1 ∨ (K.subgroupOf C).index = 2) with h1 | h1
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h1
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hn

theorem Fi24InBase.centralizer_le_normalizer [Finite Y] (h : Fi24InBase Y uY KY) :
    centralizer ({uY} : Set Y) ≤ normalizer (KY : Set Y) :=
  fi24in_le_normalizer_of_card_le h.le_centralizer h.card_le

theorem Fi24InBase.stdBare [Finite Y] (h : Fi24InBase Y uY KY) : StdBare KY := by
  have hN := h.centralizer_le_normalizer
  refine ⟨fun g hbot => ?_, fun g hg => ?_⟩
  · have h1 : KY.map (MulAut.conj g).toMonoidHom ≤ centralizer (KY : Set Y) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hbot
    have hab : ∀ k ∈ KY, g * k * g⁻¹ = 1 ∨ g * k * g⁻¹ = uY := fun k hk => by
      have := h.cent_subset (h1 ⟨k, hk, rfl⟩)
      simpa using this
    have hKK : KY ≤ centralizer (KY : Set Y) := by
      intro k₁ hk₁
      rw [mem_centralizer_iff]
      intro k₂ hk₂
      have e : g * k₂ * g⁻¹ * (g * k₁ * g⁻¹) = g * k₁ * g⁻¹ * (g * k₂ * g⁻¹) := by
        rcases hab k₁ hk₁ with h₁ | h₁ <;> rcases hab k₂ hk₂ with h₂ | h₂ <;>
          rw [h₁, h₂] <;> simp
      have e2 : g * (k₂ * k₁) * g⁻¹ = g * (k₁ * k₂) * g⁻¹ := by
        calc g * (k₂ * k₁) * g⁻¹ = g * k₂ * g⁻¹ * (g * k₁ * g⁻¹) := by group
          _ = g * k₁ * g⁻¹ * (g * k₂ * g⁻¹) := e
          _ = g * (k₁ * k₂) * g⁻¹ := by group
      have := mul_left_cancel (mul_right_cancel e2)
      exact this
    have hbot2 : ⁅KY, KY⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKK
    have : uY ∈ (⊥ : Subgroup Y) := by rw [← hbot2, h.perfect]; exact h.u_mem
    exact h.u_ne_one (Subgroup.mem_bot.1 this)
  · have hgC : g ∉ centralizer ({uY} : Set Y) := fun hc => hg (hN hc)
    have hne : g * uY * g⁻¹ ≠ uY := by
      intro he
      apply hgC
      rw [mem_centralizer_singleton_iff]
      calc g * uY = g * uY * g⁻¹ * g := by group
        _ = uY * g := by rw [he]
    have hbot : centralizer (KY : Set Y) ⊓
        (centralizer (KY : Set Y)).map (MulAut.conj g).toMonoidHom = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx, y, hy, rfl⟩
      rw [Subgroup.mem_bot]
      rcases h.cent_subset hy with hy1 | hyu
      · rw [hy1, map_one]
      · exfalso
        have hyu' : y = uY := hyu
        have hx' := h.cent_subset hx
        rw [hyu'] at hx'
        have hcg : (MulAut.conj g).toMonoidHom uY = g * uY * g⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hcg] at hx'
        rcases hx' with h1 | h1
        · apply h.u_ne_one
          have : uY = g⁻¹ * (g * uY * g⁻¹) * g := by group
          rw [this, h1]
          group
        · exact hne h1
    show Odd (Nat.card ↥(centralizer (KY : Set Y) ⊓
      (centralizer (KY : Set Y)).map (MulAut.conj g).toMonoidHom : Subgroup Y))
    rw [hbot, Subgroup.card_bot]
    exact odd_one

end Derived

theorem Fi24InBase.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {uY : Y}
    {KY : Subgroup Y} (h : Fi24InBase Y uY KY) :
    Fi24InBase Y' (e uY) (KY.map e.toMonoidHom) where
  u_sq := by rw [← map_mul, h.u_sq, map_one]
  u_ne_one := fun h1 => h.u_ne_one (e.injective (by rw [h1, map_one]))
  u_mem := Subgroup.mem_map_of_mem _ h.u_mem
  le_centralizer := by
    rw [centralizer_singleton_map_mulEquiv e uY]
    exact Subgroup.map_mono h.le_centralizer
  card_le := by
    rw [centralizer_singleton_map_mulEquiv e uY, Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective e.injective]
    exact h.card_le
  perfect := by rw [← Subgroup.map_commutator, h.perfect]
  cent := by
    intro z hz
    obtain ⟨z0, rfl⟩ := e.surjective z
    have h0 : z0 = 1 ∨ z0 = uY := h.cent z0 fun k hk => e.injective (by
      rw [map_mul, map_mul]
      exact hz _ (Subgroup.mem_map_of_mem _ hk))
    rcases h0 with rfl | rfl
    · left
      simp
    · right
      rfl
  induced := by
    intro α'
    let ε : ↥KY ≃* ↥(KY.map e.toMonoidHom) := e.subgroupMap KY
    obtain ⟨y, hy, hα⟩ := h.induced ((ε.trans α').trans ε.symm)
    refine ⟨e y, ?_, fun k' => ?_⟩
    · rw [centralizer_singleton_map_mulEquiv e uY]
      exact Subgroup.mem_map_of_mem _ hy
    · obtain ⟨k, rfl⟩ := ε.surjective k'
      have h1 := hα k
      have h2 : α' (ε k) = ε (((ε.trans α').trans ε.symm) k) := by
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [h2]
      show e (((((ε.trans α').trans ε.symm) k : ↥KY)) : Y) = e y * e (k : Y) * (e y)⁻¹
      rw [h1, map_mul, map_mul, map_inv]
  outTwo := OutTwo.of_mulEquiv e h.outTwo

end CFSG.EvenSporadicStandard.Induction
