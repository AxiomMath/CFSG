module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.IV2a
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.IV2

open Subgroup

variable {G : Type*} [Group G]

theorem le_normalizer_of_normal {T Q T' : Subgroup G} (hQn : ∀ x ∈ T, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hT' : T' ≤ T) : T' ≤ normalizer (Q : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hQn s (hT' hs) x hx
  · intro hx
    have := hQn s⁻¹ (T.inv_mem (hT' hs)) _ hx
    simpa [mul_assoc] using this

theorem exists_two_ne_one [Finite G] {U : Subgroup G} (hU : 3 ≤ Nat.card ↥U) :
    ∃ a ∈ U, ∃ b ∈ U, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have : Fintype ↥U := Fintype.ofFinite _
  have h3 : 2 < Fintype.card ↥U := by rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3
  by_cases ha : (a : G) = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro hb
      exact hab (Subtype.ext (ha.trans hb.symm))
    · intro hc
      exact hac (Subtype.ext (ha.trans hc.symm))
  · by_cases hb : (b : G) = 1
    · refine ⟨a, a.2, c, c.2, ha, ?_, fun h => hac (Subtype.ext h)⟩
      intro hc
      exact hbc (Subtype.ext (hb.trans hc.symm))
    · exact ⟨a, a.2, b, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩

theorem one_side [Finite G] {T P Q P' Q' U : Subgroup G} {z : G} (hT : T = Q' ⊔ Q)
    (hTU : T = P ⊔ P' ⊔ U) (hQn : ∀ x ∈ T, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q) (hPQ' : P ≤ Q')
    (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzP : z ∈ P) (hQQ' : Q ⊓ Q' = zpowers z)
    (hcQ : Nat.card ↥Q = 16) (hcQ' : Nat.card ↥Q' = 16) (hcP : Nat.card ↥P = 8)
    (hQuniq : ∀ g ∈ Q, g * g = 1 → g = 1 ∨ g = z) (hU2 : ∀ a ∈ U, a * a = 1)
    (hUcard : Nat.card ↥U = 4) (hPU : (P ⊔ P') ⊓ U = ⊥) :
    ∃ u ∈ U, u ≠ 1 ∧ ∃ x ∈ P, ∃ y ∈ Q, u = x⁻¹ * y ∧ x ∉ Q ∧ y ∉ P' := by
  have hQ'T : Q' ≤ T := hT ▸ le_sup_left
  have hQT : Q ≤ T := hT ▸ le_sup_right
  have hPT : P ≤ T := hTU ▸ (le_sup_left.trans le_sup_left)
  have hUT : U ≤ T := hTU ▸ le_sup_right
  have hzo : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using hz2) hz1
  have hcz : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  have hPQ : Q ⊓ P = zpowers z := by
    apply le_antisymm
    · rintro x ⟨hxQ, hxP⟩
      rw [← hQQ']
      exact ⟨hxQ, hPQ' hxP⟩
    · exact zpowers_le.2 ⟨hzQ, hzP⟩
  have hT' : T = Q ⊔ Q' := by rw [hT, sup_comm]
  have hcT : Nat.card ↥T = 128 := by
    have h1 := A.card_sup_mul_card_inf (le_normalizer_of_normal hQn hQ'T)
    rw [← hT', hQQ', hcz, hcQ, hcQ'] at h1
    omega
  have hcM : Nat.card ↥(Q ⊔ P) = 64 := by
    have h1 := A.card_sup_mul_card_inf (le_normalizer_of_normal hQn hPT)
    rw [hPQ, hcz, hcQ, hcP] at h1
    omega
  have hMT : P ⊔ Q ≤ T := sup_le hPT hQT
  have hrel : (P ⊔ Q).relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (P ⊔ Q) T
    have hcM' : Nat.card ↥(P ⊔ Q) = 64 := by rw [sup_comm]; exact hcM
    rw [inf_eq_left.2 hMT, hcM', hcT] at h1
    omega
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_ne_one (by omega : 3 ≤ Nat.card ↥U)
  obtain ⟨u, huU, hu1, huM⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ∈ P ⊔ Q := by
    rcases A.relIndex_two_pigeon hrel (hUT ha) (hUT hb) with h | h | h
    · exact ⟨a, ha, ha1, h⟩
    · exact ⟨b, hb, hb1, h⟩
    · refine ⟨a⁻¹ * b, U.mul_mem (U.inv_mem ha) hb, ?_, h⟩
      intro h1
      exact hab (inv_mul_eq_one.1 h1)
  obtain ⟨p, hp, q, hq, huq⟩ := A.mem_sup_of_le_normalizer (le_normalizer_of_normal hQn hPT) huM
  have hpQ : p ∉ Q := by
    intro hpQ
    have huQ : u ∈ Q := by rw [huq]; exact Q.mul_mem hpQ hq
    rcases hQuniq u huQ (hU2 u huU) with h | h
    · exact hu1 h
    · have : u ∈ (P ⊔ P') ⊓ U := ⟨h ▸ mem_sup_left hzP, huU⟩
      rw [hPU, Subgroup.mem_bot] at this
      exact hu1 this
  refine ⟨u, huU, hu1, p⁻¹, P.inv_mem hp, q, hq, by rw [inv_inv]; exact huq, ?_, ?_⟩
  · intro h
    exact hpQ (by simpa using Q.inv_mem h)
  · intro hqP'
    have : u ∈ (P ⊔ P') ⊓ U := ⟨by rw [huq]; exact mul_mem (mem_sup_left hp) (mem_sup_right hqP'), huU⟩
    rw [hPU, Subgroup.mem_bot] at this
    exact hu1 this

theorem rel {P₁ Q₁ P₂ Q₂ : Subgroup G} {z x₁ y₁ x₂ y₂ u₁ u₂ : G} (hz2 : z * z = 1)
    (hu₁ : u₁ = x₁⁻¹ * y₁) (hu₂ : u₂ = x₂⁻¹ * y₂) (hx₁ : x₁ ∈ P₁) (hx₁sq : x₁ * x₁ = z)
    (hy₁ : y₁ ∈ Q₁) (hx₂sq : x₂ * x₂ = z) (hx₂ : x₂ ∈ P₂) (hy₂P : y₂ ∉ P₁)
    (hu₂sq : u₂ * u₂ = 1) (hcomm : u₁ * u₂ = u₂ * u₁)
    (hN₁ : ∀ p ∈ P₁, u₂ * p * u₂⁻¹ ∈ P₁) (hN₂ : ∀ q ∈ Q₁, u₂ * q * u₂⁻¹ ∈ Q₁)
    (hPP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hy₂P₂ : ∀ b ∈ P₂, y₂ * b = b * y₂)
    (hPQ : ∀ g ∈ P₁, g ∈ Q₁ → g = 1 ∨ g = z) (hy₂Q₂ : y₂ ∈ Q₂) (hP₁Q₂ : P₁ ≤ Q₂)
    (hQ₂uniq : ∀ g ∈ Q₂, g * g = 1 → g = 1 ∨ g = z) (hzP₁ : z ∈ P₁) :
    u₂ * x₁ * u₂⁻¹ = z * x₁ := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨a, ha⟩ : ∃ a, a = u₂ * x₁⁻¹ * u₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = u₂ * y₁ * u₂⁻¹ := ⟨_, rfl⟩
  have haP : a ∈ P₁ := ha ▸ hN₁ _ (P₁.inv_mem hx₁)
  have hbQ : b ∈ Q₁ := hb ▸ hN₂ _ hy₁
  have h1 : a * b = x₁⁻¹ * y₁ := by
    have : u₂ * (x₁⁻¹ * y₁) * u₂⁻¹ = x₁⁻¹ * y₁ := by
      rw [← hu₁]
      calc u₂ * u₁ * u₂⁻¹ = u₁ * u₂ * u₂⁻¹ := by rw [hcomm]
        _ = u₁ := by group
    rw [ha, hb]
    calc u₂ * x₁⁻¹ * u₂⁻¹ * (u₂ * y₁ * u₂⁻¹) = u₂ * (x₁⁻¹ * y₁) * u₂⁻¹ := by group
      _ = x₁⁻¹ * y₁ := this
  have h2 : x₁ * a = y₁ * b⁻¹ := by
    calc x₁ * a = x₁ * (a * b) * b⁻¹ := by group
      _ = x₁ * (x₁⁻¹ * y₁) * b⁻¹ := by rw [h1]
      _ = y₁ * b⁻¹ := by group
  have hε : x₁ * a = 1 ∨ x₁ * a = z :=
    hPQ _ (P₁.mul_mem hx₁ haP) (h2 ▸ Q₁.mul_mem hy₁ (Q₁.inv_mem hbQ))
  rcases hε with hε | hε
  ·
    exfalso
    have h3 : a = x₁⁻¹ := eq_inv_of_mul_eq_one_right hε
    have hux : u₂ * x₁ = x₁ * u₂ := by
      have : u₂ * x₁⁻¹ * u₂⁻¹ = x₁⁻¹ := by rw [← ha, h3]
      calc u₂ * x₁ = (u₂ * x₁⁻¹ * u₂⁻¹)⁻¹ * u₂ := by group
        _ = x₁ * u₂ := by rw [this]; group
    have hy₂e : y₂ = x₂ * u₂ := by rw [hu₂]; group
    have hy₂x₁ : y₂ * x₁ = x₁ * y₂ := by
      calc y₂ * x₁ = x₂ * (u₂ * x₁) := by rw [hy₂e]; group
        _ = x₂ * (x₁ * u₂) := by rw [hux]
        _ = (x₂ * x₁) * u₂ := by group
        _ = (x₁ * x₂) * u₂ := by rw [hPP x₁ hx₁ x₂ hx₂]
        _ = x₁ * y₂ := by rw [hy₂e]; group
    have hy₂sq : y₂ * y₂ = z := by
      have hc : y₂ * x₂⁻¹ = x₂⁻¹ * y₂ := hy₂P₂ x₂⁻¹ (P₂.inv_mem hx₂)
      have h4 : x₂⁻¹ * x₂⁻¹ * (y₂ * y₂) = 1 := by
        calc x₂⁻¹ * x₂⁻¹ * (y₂ * y₂) = x₂⁻¹ * (x₂⁻¹ * y₂) * y₂ := by group
          _ = x₂⁻¹ * (y₂ * x₂⁻¹) * y₂ := by rw [hc]
          _ = u₂ * u₂ := by rw [hu₂]; group
          _ = 1 := hu₂sq
      have h5 : x₂⁻¹ * x₂⁻¹ = z⁻¹ := by
        calc x₂⁻¹ * x₂⁻¹ = (x₂ * x₂)⁻¹ := by group
          _ = z⁻¹ := by rw [hx₂sq]
      rw [h5, hzinv] at h4
      calc y₂ * y₂ = z⁻¹ * (z * (y₂ * y₂)) := by group
        _ = z := by rw [h4, hzinv]; group
    have hw : y₂ * x₁⁻¹ ∈ Q₂ := Q₂.mul_mem hy₂Q₂ (Q₂.inv_mem (hP₁Q₂ hx₁))
    have hw2 : (y₂ * x₁⁻¹) * (y₂ * x₁⁻¹) = 1 := by
      have hc : y₂ * x₁⁻¹ = x₁⁻¹ * y₂ := by
        calc y₂ * x₁⁻¹ = x₁⁻¹ * (x₁ * y₂) * x₁⁻¹ := by group
          _ = x₁⁻¹ * (y₂ * x₁) * x₁⁻¹ := by rw [hy₂x₁]
          _ = x₁⁻¹ * y₂ := by group
      calc (y₂ * x₁⁻¹) * (y₂ * x₁⁻¹) = y₂ * (x₁⁻¹ * y₂) * x₁⁻¹ := by group
        _ = y₂ * (y₂ * x₁⁻¹) * x₁⁻¹ := by rw [hc]
        _ = (y₂ * y₂) * (x₁⁻¹ * x₁⁻¹) := by group
        _ = z * z⁻¹ := by
          rw [hy₂sq]
          congr 1
          calc x₁⁻¹ * x₁⁻¹ = (x₁ * x₁)⁻¹ := by group
            _ = z⁻¹ := by rw [hx₁sq]
        _ = 1 := by group
    rcases hQ₂uniq _ hw hw2 with h | h
    · apply hy₂P
      have : y₂ = x₁ := by
        calc y₂ = (y₂ * x₁⁻¹) * x₁ := by group
          _ = x₁ := by rw [h]; group
      rw [this]; exact hx₁
    · apply hy₂P
      have : y₂ = z * x₁ := by
        calc y₂ = (y₂ * x₁⁻¹) * x₁ := by group
          _ = z * x₁ := by rw [h]
      rw [this]; exact P₁.mul_mem hzP₁ hx₁
  ·
    have h3 : a = x₁⁻¹ * z := by
      calc a = x₁⁻¹ * (x₁ * a) := by group
        _ = x₁⁻¹ * z := by rw [hε]
    have h4 : u₂ * x₁⁻¹ * u₂⁻¹ = x₁⁻¹ * z := by rw [← ha, h3]
    calc u₂ * x₁ * u₂⁻¹ = (u₂ * x₁⁻¹ * u₂⁻¹)⁻¹ := by group
      _ = (x₁⁻¹ * z)⁻¹ := by rw [h4]
      _ = z * x₁ := by rw [mul_inv_rev, inv_inv, hzinv]


theorem iv2_core [Finite G] {T P₁ P₂ Q₁ Q₂ U : Subgroup G} {z : G} (hT₁ : T = P₁ ⊔ P₂ ⊔ U)
    (hT₂ : T = Q₂ ⊔ Q₁) (hn₁ : ∀ x ∈ T, ∀ y ∈ Q₁, x * y * x⁻¹ ∈ Q₁)
    (hn₂ : ∀ x ∈ T, ∀ y ∈ Q₂, x * y * x⁻¹ ∈ Q₂) (e₁ : ↥Q₁ ≃* QuaternionGroup 4)
    (e₂ : ↥Q₂ ≃* QuaternionGroup 4) (hz : Q₁ ⊓ Q₂ = zpowers z)
    (hz₁ : (center ↥Q₁).map Q₁.subtype = zpowers z) (hz₂ : (center ↥Q₂).map Q₂.subtype = zpowers z)
    (f₁ : ↥P₁ ≃* QuaternionGroup 2) (f₂ : ↥P₂ ≃* QuaternionGroup 2) (h21 : P₂ ≤ Q₁) (h12 : P₁ ≤ Q₂)
    (hc₁ : Q₁ = T ⊓ centralizer (P₁ : Set G)) (hc₂ : Q₂ = T ⊓ centralizer (P₂ : Set G))
    (hU2 : ∀ a ∈ U, a * a = 1) (hUcard : Nat.card ↥U = 4) (hPU : (P₁ ⊔ P₂) ⊓ U = ⊥) :
    ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a := by
  obtain ⟨hzQ₁, hz1, hz2, hzc₁, huniq₁, hcQ₁⟩ := quat16_facts e₁ hz₁
  obtain ⟨hzQ₂, -, -, hzc₂, huniq₂, hcQ₂⟩ := quat16_facts e₂ hz₂
  obtain ⟨z₁, hz₁P, hz₁1, -, hz₁c, -, hz₁sq, hcP₁⟩ := quat8_facts f₁
  obtain ⟨z₂, hz₂P, hz₂1, -, hz₂c, -, hz₂sq, hcP₂⟩ := quat8_facts f₂
  have hTP₁ : P₁ ≤ T := hT₁ ▸ (le_sup_left.trans le_sup_left)
  have hTP₂ : P₂ ≤ T := hT₁ ▸ (le_sup_right.trans le_sup_left)
  have hTQ₁ : Q₁ ≤ T := hT₂ ▸ le_sup_right
  have hTQ₂ : Q₂ ≤ T := hT₂ ▸ le_sup_left
  have hTU : U ≤ T := hT₁ ▸ le_sup_right
  have hcen₁ : ∀ q ∈ Q₁, ∀ p ∈ P₁, p * q = q * p := fun q hq p hp =>
    Subgroup.mem_centralizer_iff.1 (hc₁ ▸ hq : q ∈ T ⊓ centralizer (P₁ : Set G)).2 p hp
  have hcen₂ : ∀ q ∈ Q₂, ∀ p ∈ P₂, p * q = q * p := fun q hq p hp =>
    Subgroup.mem_centralizer_iff.1 (hc₂ ▸ hq : q ∈ T ⊓ centralizer (P₂ : Set G)).2 p hp
  have hz₁z : z₁ = z := by
    have h1 : z₁ ∈ Q₁ := by
      rw [hc₁]
      exact ⟨hTP₁ hz₁P, Subgroup.mem_centralizer_iff.2 fun h hh => (hz₁c h hh).symm⟩
    have h3 : z₁ ∈ zpowers z := hz ▸ ⟨h1, h12 hz₁P⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h3
    rcases B.zpow_of_sq_eq_one hz2 k with h | h
    · exact absurd (hk.symm.trans h) hz₁1
    · exact hk.symm.trans h
  have hz₂z : z₂ = z := by
    have h1 : z₂ ∈ Q₂ := by
      rw [hc₂]
      exact ⟨hTP₂ hz₂P, Subgroup.mem_centralizer_iff.2 fun h hh => (hz₂c h hh).symm⟩
    have h3 : z₂ ∈ zpowers z := hz ▸ ⟨h21 hz₂P, h1⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h3
    rcases B.zpow_of_sq_eq_one hz2 k with h | h
    · exact absurd (hk.symm.trans h) hz₂1
    · exact hk.symm.trans h
  have hsq₁ : ∀ g ∈ P₁, g ≠ 1 → g ≠ z → g * g = z := by rw [← hz₁z]; exact hz₁sq
  have hsq₂ : ∀ g ∈ P₂, g ≠ 1 → g ≠ z → g * g = z := by rw [← hz₂z]; exact hz₂sq
  have hzP₁ : z ∈ P₁ := hz₁z ▸ hz₁P
  have hzP₂ : z ∈ P₂ := hz₂z ▸ hz₂P
  have hzT : ∀ t ∈ T, z * t = t * z := by
    intro t ht
    have ht' : t ∈ Q₂ ⊔ Q₁ := hT₂ ▸ ht
    obtain ⟨q₂, hq₂, q₁, hq₁, rfl⟩ :=
      A.mem_sup_of_le_normalizer (le_normalizer_of_normal hn₁ hTQ₂) ht'
    calc z * (q₂ * q₁) = (z * q₂) * q₁ := by group
      _ = (q₂ * z) * q₁ := by rw [hzc₂ q₂ hq₂]
      _ = q₂ * (z * q₁) := by group
      _ = q₂ * (q₁ * z) := by rw [hzc₁ q₁ hq₁]
      _ = q₂ * q₁ * z := by group
  have hrel₁ : P₁.relIndex Q₂ = 2 := by
    have h1 := Subgroup.relIndex_mul_card P₁ Q₂
    rw [inf_eq_left.2 h12, hcP₁, hcQ₂] at h1
    omega
  have hrel₂ : P₂.relIndex Q₁ = 2 := by
    have h1 := Subgroup.relIndex_mul_card P₂ Q₁
    rw [inf_eq_left.2 h21, hcP₂, hcQ₁] at h1
    omega
  have hP₁n : ∀ y ∈ Q₂, ∀ p ∈ P₁, y * p * y⁻¹ ∈ P₁ := fun y hy p hp =>
    A.conj_mem_of_relIndex_two hrel₁ hy hp h12
  have hP₂n : ∀ y ∈ Q₁, ∀ p ∈ P₂, y * p * y⁻¹ ∈ P₂ := fun y hy p hp =>
    A.conj_mem_of_relIndex_two hrel₂ hy hp h21
  have hz' : Q₂ ⊓ Q₁ = zpowers z := by rw [inf_comm]; exact hz
  obtain ⟨u₁, hu₁U, hu₁1, x₁, hx₁, y₁, hy₁, hu₁, hx₁Q, hy₁P⟩ :=
    one_side hT₂ hT₁ hn₁ h12 hzQ₁ hz2 hz1 hzP₁ hz hcQ₁ hcQ₂ hcP₁ huniq₁ hU2 hUcard hPU
  obtain ⟨u₂, hu₂U, hu₂1, x₂, hx₂, y₂, hy₂, hu₂, hx₂Q, hy₂P⟩ :=
    one_side (by rw [hT₂, sup_comm]) (by rw [hT₁, sup_comm P₁ P₂]) hn₂ h21 hzQ₂ hz2 hz1 hzP₂ hz'
      hcQ₂ hcQ₁ hcP₂ huniq₂ hU2 hUcard (by rw [sup_comm]; exact hPU)
  have hx₁sq : x₁ * x₁ = z :=
    hsq₁ x₁ hx₁ (fun h => hx₁Q (h ▸ Q₁.one_mem)) (fun h => hx₁Q (h ▸ hzQ₁))
  have hx₂sq : x₂ * x₂ = z :=
    hsq₂ x₂ hx₂ (fun h => hx₂Q (h ▸ Q₂.one_mem)) (fun h => hx₂Q (h ▸ hzQ₂))
  have hcomm : u₁ * u₂ = u₂ * u₁ := B.comm_of_forall_sq hU2 hu₁U hu₂U
  have hPQ₁ : ∀ g ∈ P₁, g ∈ Q₁ → g = 1 ∨ g = z := by
    intro g hg hgQ
    have hg' : g ∈ zpowers z := hz ▸ ⟨hgQ, h12 hg⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hg'
    rcases B.zpow_of_sq_eq_one hz2 k with h | h
    · exact Or.inl (hk.symm.trans h)
    · exact Or.inr (hk.symm.trans h)
  have hPQ₂ : ∀ g ∈ P₂, g ∈ Q₂ → g = 1 ∨ g = z := by
    intro g hg hgQ
    have hg' : g ∈ zpowers z := hz ▸ ⟨h21 hg, hgQ⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hg'
    rcases B.zpow_of_sq_eq_one hz2 k with h | h
    · exact Or.inl (hk.symm.trans h)
    · exact Or.inr (hk.symm.trans h)
  have hPP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => hcen₁ b (h21 hb) a ha
  have hPP' : ∀ a ∈ P₂, ∀ b ∈ P₁, a * b = b * a := fun a ha b hb => hcen₂ b (h12 hb) a ha
  have hy₁P₁ : ∀ b ∈ P₁, y₁ * b = b * y₁ := fun b hb => (hcen₁ y₁ hy₁ b hb).symm
  have hy₂P₂ : ∀ b ∈ P₂, y₂ * b = b * y₂ := fun b hb => (hcen₂ y₂ hy₂ b hb).symm
  have hN₁ : ∀ p ∈ P₁, u₂ * p * u₂⁻¹ ∈ P₁ := by
    intro p hp
    have h1 : y₂ * p * y₂⁻¹ ∈ P₁ := hP₁n y₂ hy₂ p hp
    have h2 : (y₂ * p * y₂⁻¹) * x₂ = x₂ * (y₂ * p * y₂⁻¹) := hPP _ h1 x₂ hx₂
    have : u₂ * p * u₂⁻¹ = y₂ * p * y₂⁻¹ := by
      calc u₂ * p * u₂⁻¹ = x₂⁻¹ * (y₂ * p * y₂⁻¹) * x₂ := by rw [hu₂]; group
        _ = x₂⁻¹ * ((y₂ * p * y₂⁻¹) * x₂) := by group
        _ = x₂⁻¹ * (x₂ * (y₂ * p * y₂⁻¹)) := by rw [h2]
        _ = y₂ * p * y₂⁻¹ := by group
    rw [this]
    exact h1
  have hN₁' : ∀ p ∈ P₂, u₁ * p * u₁⁻¹ ∈ P₂ := by
    intro p hp
    have h1 : y₁ * p * y₁⁻¹ ∈ P₂ := hP₂n y₁ hy₁ p hp
    have h2 : (y₁ * p * y₁⁻¹) * x₁ = x₁ * (y₁ * p * y₁⁻¹) := hPP' _ h1 x₁ hx₁
    have : u₁ * p * u₁⁻¹ = y₁ * p * y₁⁻¹ := by
      calc u₁ * p * u₁⁻¹ = x₁⁻¹ * (y₁ * p * y₁⁻¹) * x₁ := by rw [hu₁]; group
        _ = x₁⁻¹ * ((y₁ * p * y₁⁻¹) * x₁) := by group
        _ = x₁⁻¹ * (x₁ * (y₁ * p * y₁⁻¹)) := by rw [h2]
        _ = y₁ * p * y₁⁻¹ := by group
    rw [this]
    exact h1
  have r₁ : u₂ * x₁ * u₂⁻¹ = z * x₁ :=
    rel (P₁ := P₁) (Q₁ := Q₁) (P₂ := P₂) (Q₂ := Q₂) hz2 hu₁ hu₂ hx₁ hx₁sq hy₁ hx₂sq hx₂ hy₂P
      (hU2 u₂ hu₂U) hcomm hN₁ (fun q hq => hn₁ u₂ (hTU hu₂U) q hq) hPP hy₂P₂ hPQ₁ hy₂ h12 huniq₂ hzP₁
  have r₂ : u₁ * x₂ * u₁⁻¹ = z * x₂ :=
    rel (P₁ := P₂) (Q₁ := Q₂) (P₂ := P₁) (Q₂ := Q₁) hz2 hu₂ hu₁ hx₂ hx₂sq hy₂ hx₁sq hx₁ hy₁P
      (hU2 u₁ hu₁U) hcomm.symm hN₁' (fun q hq => hn₂ u₁ (hTU hu₁U) q hq) hPP' hy₁P₁ hPQ₂ hy₁ h21
      huniq₁ hzP₂
  have hy₁e : y₁ = x₁ * u₁ := by rw [hu₁]; group
  have hy₂e : y₂ = x₂ * u₂ := by rw [hu₂]; group
  have hxx : x₁ * x₂ = x₂ * x₁ := hPP x₁ hx₁ x₂ hx₂
  have hzx₁ : z * x₁ = x₁ * z := hzT x₁ (hTP₁ hx₁)
  have hzx₂ : z * x₂ = x₂ * z := hzT x₂ (hTP₂ hx₂)
  have hyy : y₁ * y₂ = y₂ * y₁ := by
    have e1 : y₁ * y₂ = z * (x₁ * x₂) * (u₁ * u₂) := by
      calc y₁ * y₂ = x₁ * (u₁ * x₂ * u₁⁻¹) * (u₁ * u₂) := by rw [hy₁e, hy₂e]; group
        _ = x₁ * (z * x₂) * (u₁ * u₂) := by rw [r₂]
        _ = (x₁ * z) * x₂ * (u₁ * u₂) := by group
        _ = (z * x₁) * x₂ * (u₁ * u₂) := by rw [hzx₁]
        _ = z * (x₁ * x₂) * (u₁ * u₂) := by group
    have e2 : y₂ * y₁ = z * (x₂ * x₁) * (u₂ * u₁) := by
      calc y₂ * y₁ = x₂ * (u₂ * x₁ * u₂⁻¹) * (u₂ * u₁) := by rw [hy₁e, hy₂e]; group
        _ = x₂ * (z * x₁) * (u₂ * u₁) := by rw [r₁]
        _ = (x₂ * z) * x₁ * (u₂ * u₁) := by group
        _ = (z * x₂) * x₁ * (u₂ * u₁) := by rw [hzx₂]
        _ = z * (x₂ * x₁) * (u₂ * u₁) := by group
    rw [e1, e2, hxx, hcomm]
  have hQ₁gen : ∀ a ∈ Q₁, a ∈ P₂ ∨ ∃ p ∈ P₂, a = y₁ * p := by
    intro a ha
    rcases A.relIndex_two_pigeon hrel₂ hy₁ ha with h | h | h
    · exact absurd h hy₁P
    · exact Or.inl h
    · exact Or.inr ⟨y₁⁻¹ * a, h, by group⟩
  have hQ₂gen : ∀ b ∈ Q₂, b ∈ P₁ ∨ ∃ q ∈ P₁, b = y₂ * q := by
    intro b hb
    rcases A.relIndex_two_pigeon hrel₁ hy₂ hb with h | h | h
    · exact absurd h hy₂P
    · exact Or.inl h
    · exact Or.inr ⟨y₂⁻¹ * b, h, by group⟩
  intro a ha b hb
  rcases hQ₁gen a ha with ha' | ⟨p, hp, rfl⟩ <;> rcases hQ₂gen b hb with hb' | ⟨q, hq, rfl⟩
  · exact hPP' a ha' b hb'
  · calc a * (y₂ * q) = (a * y₂) * q := by group
      _ = (y₂ * a) * q := by rw [← hy₂P₂ a ha']
      _ = y₂ * (a * q) := by group
      _ = y₂ * (q * a) := by rw [hPP' a ha' q hq]
      _ = y₂ * q * a := by group
  · calc y₁ * p * b = y₁ * (p * b) := by group
      _ = y₁ * (b * p) := by rw [hPP' p hp b hb']
      _ = (y₁ * b) * p := by group
      _ = (b * y₁) * p := by rw [hy₁P₁ b hb']
      _ = b * (y₁ * p) := by group
  · calc y₁ * p * (y₂ * q) = y₁ * (p * y₂) * q := by group
      _ = y₁ * (y₂ * p) * q := by rw [← hy₂P₂ p hp]
      _ = (y₁ * y₂) * (p * q) := by group
      _ = (y₂ * y₁) * (q * p) := by rw [hyy, hPP' p hp q hq]
      _ = y₂ * (y₁ * q) * p := by group
      _ = y₂ * (q * y₁) * p := by rw [hy₁P₁ q hq]
      _ = y₂ * q * (y₁ * p) := by group

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.IV2
