module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingProduct
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineData

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E} (hc : U3RootCoords T₁ σ u v)
include hc

theorem commute_iff {y y' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁) :
    y * y' = y' * y ↔ u y * σ (u y') = u y' * σ (u y) := by
  constructor
  · intro h
    have h1 := hc.mul_v y hy y' hy'
    have h2 := hc.mul_v y' hy' y hy
    rw [h] at h1
    linear_combination h1 - h2
  · intro h
    refine hc.inj _ (mul_mem hy hy') _ (mul_mem hy' hy) ?_ ?_
    · rw [hc.mul_u y hy y' hy', hc.mul_u y' hy' y hy, add_comm]
    · rw [hc.mul_v y hy y' hy', hc.mul_v y' hy' y hy]
      linear_combination -h

theorem u_ne_zero_of_not_comm {y : G} (hy : y ∈ T₁) (hnc : ∃ z ∈ T₁, y * z ≠ z * y) :
    u y ≠ 0 := by
  intro hu
  obtain ⟨z, hz, hyz⟩ := hnc
  apply hyz
  rw [hc.commute_iff hy hz, hu, map_zero, zero_mul, mul_zero]

theorem comm_of_comm_of_comm {y c c' : G} (hy : y ∈ T₁) (hyu : u y ≠ 0) (hcT : c ∈ T₁)
    (hc'T : c' ∈ T₁) (h1 : c * y = y * c) (h2 : c' * y = y * c') : c * c' = c' * c := by
  rw [hc.commute_iff hcT hc'T]
  have e1 := (hc.commute_iff hcT hy).mp h1
  have e2 := (hc.commute_iff hc'T hy).mp h2
  apply mul_left_cancel₀ hyu
  linear_combination (-(u c)) * e2 + (u c') * e1

end U3RootCoords

section Transport

variable {G : Type*} [Group G]

theorem comm_of_comm_of_conj_partner {U T₁ Y Y' : Subgroup G} {t : G} (htt : t * t = 1)
    (hYU : Y ≤ U) (hY'U : Y' ≤ U) (hinf : Y ⊓ Y' = ⊥) (hcomm : ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a)
    (ht : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y') (hCt : ∀ x ∈ U, x * t = t * x → x ∈ T₁)
    (hCA : ∀ y ∈ T₁, (∃ z ∈ T₁, y * z ≠ z * y) →
      ∀ c ∈ T₁, ∀ c' ∈ T₁, c * y = y * c → c' * y = y * c' → c * c' = c' * c) :
    ∀ y ∈ Y, (∃ z ∈ Y, y * z ≠ z * y) →
      ∀ c ∈ Y, ∀ c' ∈ Y, c * y = y * c → c' * y = y * c' → c * c' = c' * c := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hφT : ∀ x ∈ Y, x * (t * x * t⁻¹) ∈ T₁ := by
    intro x hx
    refine hCt _ (mul_mem (hYU hx) (hY'U (ht x hx))) ?_
    have hxx : x * (t * x * t⁻¹) = (t * x * t⁻¹) * x := hcomm x hx _ (ht x hx)
    calc x * (t * x * t⁻¹) * t = (t * x * t⁻¹) * x * t := by rw [hxx]
      _ = t * x * (t⁻¹ * x * t) := by group
      _ = t * x * (t * x * t⁻¹) := by rw [htinv]
      _ = t * (x * (t * x * t⁻¹)) := by group
  have hφmul : ∀ x ∈ Y, ∀ x' ∈ Y, x * x' * (t * (x * x') * t⁻¹) =
      x * (t * x * t⁻¹) * (x' * (t * x' * t⁻¹)) := by
    intro x hx x' hx'
    have h1 : x' * (t * x * t⁻¹) = (t * x * t⁻¹) * x' := hcomm x' hx' _ (ht x hx)
    calc x * x' * (t * (x * x') * t⁻¹) = x * (x' * (t * x * t⁻¹)) * (t * x' * t⁻¹) := by group
      _ = x * ((t * x * t⁻¹) * x') * (t * x' * t⁻¹) := by rw [h1]
      _ = x * (t * x * t⁻¹) * (x' * (t * x' * t⁻¹)) := by group
  have hφinj : ∀ x ∈ Y, ∀ x' ∈ Y, x * (t * x * t⁻¹) = x' * (t * x' * t⁻¹) → x = x' :=
    fun x hx x' hx' h =>
      (eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hinf hx hx' (ht x hx) (ht x' hx') h).1
  have hcommφ : ∀ x ∈ Y, ∀ x' ∈ Y, (x * x' = x' * x ↔
      x * (t * x * t⁻¹) * (x' * (t * x' * t⁻¹)) = x' * (t * x' * t⁻¹) * (x * (t * x * t⁻¹))) := by
    intro x hx x' hx'
    constructor
    · intro h
      rw [← hφmul x hx x' hx', ← hφmul x' hx' x hx, h]
    · intro h
      apply hφinj _ (mul_mem hx hx') _ (mul_mem hx' hx)
      rw [hφmul x hx x' hx', hφmul x' hx' x hx, h]
  intro y hy hync c hcY c' hc'Y h1 h2
  rw [hcommφ c hcY c' hc'Y]
  refine hCA _ (hφT y hy) ?_ _ (hφT c hcY) _ (hφT c' hc'Y) ((hcommφ c hcY y hy).mp h1)
    ((hcommφ c' hc'Y y hy).mp h2)
  obtain ⟨z, hz, hyz⟩ := hync
  exact ⟨_, hφT z hz, fun e => hyz ((hcommφ y hy z hz).mpr e)⟩

theorem comm_of_mem_sup_of_comm {Y₁ Y₂ : Subgroup G} (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hab₁ : ∀ a ∈ Y₁, ∀ a' ∈ Y₁, a * a' = a' * a) (hab₂ : ∀ b ∈ Y₂, ∀ b' ∈ Y₂, b * b' = b' * b)
    {x y : G} (hx : x ∈ Y₁ ⊔ Y₂) (hy : y ∈ Y₁ ⊔ Y₂) : x * y = y * x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hx
  obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hy
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [hcomm a' ha' b hb]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [hab₁ a ha a' ha', hab₂ b hb b' hb']
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hcomm a ha b' hb']
    _ = a' * b' * (a * b) := by group

end Transport

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem product_facts_of_card_sylow
    (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) :
    (∀ y ∈ Y₁, (∃ z ∈ Y₁, y * z ≠ z * y) →
      ∀ c ∈ Y₁, ∀ c' ∈ Y₁, c * y = y * c → c' * y = y * c' → c * c' = c' * c) ∧
    (∀ y ∈ Y₂, (∃ z ∈ Y₂, y * z ≠ z * y) →
      ∀ c ∈ Y₂, ∀ c' ∈ Y₂, c * y = y * c → c' * y = y * c' → c * c' = c' * c) ∧
    (∃ c ∈ Y₁, ∃ c' ∈ Y₁, c * c' ≠ c' * c) ∧ (∃ c ∈ Y₂, ∃ c' ∈ Y₂, c * c' ≠ c' * c) := by
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  obtain ⟨E, _, _, _, σ, -, -, -, u, v, hc, -⟩ := h.exists_rootCoords_of_card_sylow hS2
  have hCA : ∀ y ∈ szT₁ L T, (∃ z ∈ szT₁ L T, y * z ≠ z * y) →
      ∀ c ∈ szT₁ L T, ∀ c' ∈ szT₁ L T, c * y = y * c → c' * y = y * c' → c * c' = c' * c :=
    fun y hy hnc c hc₁ c' hc₂ h1 h2 =>
      hc.comm_of_comm_of_comm hy (hc.u_ne_zero_of_not_comm hy hnc) hc₁ hc₂ h1 h2
  have hCt : ∀ x ∈ U₁, x * t = t * x → x ∈ szT₁ L T :=
    fun x hx hxt => hU.mem_szT₁_of_commute hR hx hxt
  have hY₁U : Y₁ ≤ U₁ := hY ▸ le_sup_left
  have hY₂U : Y₂ ≤ U₁ := hY ▸ le_sup_right
  have hinf' : Y₂ ⊓ Y₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hcomm' : ∀ a ∈ Y₂, ∀ b ∈ Y₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hCA₁ := comm_of_comm_of_conj_partner htt hY₁U hY₂U hinf hcomm ht₁ hCt hCA
  have hCA₂ := comm_of_comm_of_conj_partner htt hY₂U hY₁U hinf' hcomm' ht₂ hCt hCA
  have hR₂ne : R₂ ≠ ⊥ := by
    intro hbot
    have hcard := hR.card
    rw [hbot, card_bot] at hcard
    have h1 : 1 < (2 ^ f) ^ 2 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by have := h.two_le; omega))
    omega
  have hnot_ab : ¬ ∀ x ∈ U₁, ∀ y ∈ U₁, x * y = y * x := by
    intro hab
    apply hR₂ne
    rw [← hU.commutator_eq, commutator_eq_bot_iff_le_centralizer]
    intro x hx
    exact mem_centralizer_iff.mpr fun y hy => hab y hy x hx
  have hconjab : ∀ {X X' : Subgroup G}, (∀ a ∈ X, t * a * t⁻¹ ∈ X') →
      (∀ a ∈ X', ∀ a' ∈ X', a * a' = a' * a) → ∀ b ∈ X, ∀ b' ∈ X, b * b' = b' * b := by
    intro X X' hX hab b hb b' hb'
    have e := hab _ (hX b hb) _ (hX b' hb')
    have e' : t * (b * b') * t⁻¹ = t * (b' * b) * t⁻¹ := by
      calc t * (b * b') * t⁻¹ = t * b * t⁻¹ * (t * b' * t⁻¹) := by group
        _ = t * b' * t⁻¹ * (t * b * t⁻¹) := e
        _ = t * (b' * b) * t⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e')
  have hna : ∀ {X X' : Subgroup G}, (∀ a ∈ X', t * a * t⁻¹ ∈ X) → X ⊔ X' = U₁ →
      (∀ a ∈ X, ∀ b ∈ X', a * b = b * a) → ∃ c ∈ X, ∃ c' ∈ X, c * c' ≠ c' * c := by
    intro X X' hX' hXU hXc
    by_contra hno
    push Not at hno
    apply hnot_ab
    intro x hx y hy
    rw [← hXU] at hx hy
    exact comm_of_mem_sup_of_comm hXc hno (hconjab hX' hno) hx hy
  exact ⟨hCA₁, hCA₂, hna ht₂ hY hcomm, hna ht₁ (by rw [sup_comm]; exact hY) hcomm'⟩

end U3U1Data

end CFSG.SeitzReduction.RankOne
