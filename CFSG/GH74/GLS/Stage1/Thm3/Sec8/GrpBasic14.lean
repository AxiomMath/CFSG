module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic3
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section Cent16

variable {G : Type*} [Group G]

theorem Cent16.le_normalizer {A B : Subgroup G} (h : ∀ a ∈ A, ∀ y ∈ B, a * y * a⁻¹ ∈ B) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h a ha x hx
  · intro hx
    have h1 := h a⁻¹ (inv_mem ha) _ hx
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h1

theorem Cent16.comm_mem_inf {A B : Subgroup G} (hA : ∀ b ∈ B, ∀ y ∈ A, b * y * b⁻¹ ∈ A)
    (hB : ∀ a ∈ A, ∀ y ∈ B, a * y * a⁻¹ ∈ B) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := by
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A := hA b hb a⁻¹ (inv_mem ha)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem ha h1
  · exact mul_mem (hB a ha b hb) (inv_mem hb)

theorem Cent16.exists_twist {S : Subgroup G} {z : G} (hz : ∀ g ∈ S, z * g = g * z) (w : G) :
    ∃ U : Subgroup G, ∀ g, g ∈ U ↔ g ∈ S ∧ ∃ ζ ∈ Subgroup.zpowers z, g * w * g⁻¹ = ζ * w := by
  have hc : ∀ g ∈ S, ∀ ζ ∈ Subgroup.zpowers z, ζ * g = g * ζ := by
    intro g hg ζ hζ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hζ
    exact (Commute.zpow_left (show Commute z g from hz g hg) k).eq
  refine ⟨{ carrier := {g | g ∈ S ∧ ∃ ζ ∈ Subgroup.zpowers z, g * w * g⁻¹ = ζ * w}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro a b ⟨haS, ζa, hζa, ha⟩ ⟨hbS, ζb, hζb, hb⟩
    refine ⟨mul_mem haS hbS, ζb * ζa, mul_mem hζb hζa, ?_⟩
    have h1 : a * ζb * a⁻¹ = ζb := by rw [← hc a haS ζb hζb]; group
    calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
      _ = a * (ζb * w) * a⁻¹ := by rw [hb]
      _ = (a * ζb * a⁻¹) * (a * w * a⁻¹) := by group
      _ = ζb * (ζa * w) := by rw [h1, ha]
      _ = (ζb * ζa) * w := by group
  · exact ⟨one_mem S, 1, one_mem _, by simp⟩
  · rintro a ⟨haS, ζ, hζ, ha⟩
    refine ⟨inv_mem haS, ζ⁻¹, inv_mem hζ, ?_⟩
    have h1 : a⁻¹ * ζ⁻¹ * a = ζ⁻¹ := by rw [← hc a⁻¹ (inv_mem haS) ζ⁻¹ (inv_mem hζ)]; group
    calc a⁻¹ * w * a⁻¹⁻¹ = a⁻¹ * ζ⁻¹ * (ζ * w) * a := by group
      _ = a⁻¹ * ζ⁻¹ * (a * w * a⁻¹) * a := by rw [ha]
      _ = (a⁻¹ * ζ⁻¹ * a) * w := by group
      _ = ζ⁻¹ * w := by rw [h1]

theorem Cent16.card_inf_le [Finite G] {Q M U : Subgroup G} {z w : G} (hz2 : z * z = 1)
    (hq : Nat.card ↥Q = 16) (hM : M ≤ Q) (hc : IsCyclic ↥M) (hm : Nat.card ↥M = 8)
    (hout : ∀ x ∈ Q, x ∉ M → x * x = z ∧ ∀ y ∈ M, x * y * x⁻¹ = y⁻¹) (hw : w ∈ Q) (hwM : w ∉ M)
    (hU : ∀ g ∈ Q, g ∈ U → ∃ ζ ∈ Subgroup.zpowers z, g * w * g⁻¹ = ζ * w) :
    Nat.card ↥(Q ⊓ U) ≤ 8 := by
  have hne : Nat.card ↥(Q ⊓ U) ≠ 16 := by
    intro h16
    have hEq : Q ⊓ U = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hq, h16])
    obtain ⟨g, hgM, hgen⟩ := exists_generator_of_cyclic hc
    have hgo : orderOf g = 8 := by rw [← hm, hgen, Nat.card_zpowers]
    have hgQ : g ∈ Q := hM hgM
    have hgU : g ∈ Q ⊓ U := by rw [hEq]; exact hgQ
    obtain ⟨ζ, hζ, hgζ⟩ := hU g hgQ (Subgroup.mem_inf.1 hgU).2
    have hwg : w * g⁻¹ * w⁻¹ = g := by
      have h1 := (hout w hw hwM).2 g⁻¹ (inv_mem hgM)
      rwa [inv_inv] at h1
    have h1 : g * w * g⁻¹ = g * g * w := by
      calc g * w * g⁻¹ = g * (w * g⁻¹ * w⁻¹) * w := by group
        _ = g * g * w := by rw [hwg]
    have h2 : g * g = ζ := mul_right_cancel (h1.symm.trans hgζ)
    have h3 : ζ * ζ = 1 := by
      rcases (mem_zpowers_of_sq' hz2).1 hζ with h | h
      · rw [h, one_mul]
      · rw [h]
        exact hz2
    have h4 : g ^ 4 = 1 := by rw [pow_four_eq, h2, h3]
    have h5 : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    rw [hgo] at h5
    omega
  have hdvd : Nat.card ↥(Q ⊓ U) ∣ 16 := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : Q ⊓ U ≤ Q)
    rwa [hq] at h1
  have hle : Nat.card ↥(Q ⊓ U) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have key : ∀ d : ℕ, d ≤ 16 → d ∣ 16 → d ≠ 16 → d ≤ 8 := by decide
  exact key _ hle hdvd hne

end Cent16

theorem card_cent_le_sixteen {G : Type*} [Group G] [Finite G] {Q₁ Q₂ M₁ M₂ : Subgroup G}
    {z w₁ w₂ m₁ : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ g ∈ Q₁ ⊔ Q₂, z * g = g * z)
    (hN₁ : ∀ g ∈ Q₁ ⊔ Q₂, ∀ y ∈ Q₁, g * y * g⁻¹ ∈ Q₁)
    (hN₂ : ∀ g ∈ Q₁ ⊔ Q₂, ∀ y ∈ Q₂, g * y * g⁻¹ ∈ Q₂)
    (hQ : Q₁ ⊓ Q₂ = zpowers z) (hM₁ : M₁ ≤ Q₁) (hM₂ : M₂ ≤ Q₂)
    (hc₁ : IsCyclic ↥M₁) (hc₂ : IsCyclic ↥M₂)
    (hq₁ : Nat.card ↥Q₁ = 16) (hq₂ : Nat.card ↥Q₂ = 16)
    (hm₁ : Nat.card ↥M₁ = 8) (hm₂ : Nat.card ↥M₂ = 8) (hz₁ : z ∈ M₁) (hz₂ : z ∈ M₂)
    (hout₁ : ∀ x ∈ Q₁, x ∉ M₁ → x * x = z ∧ ∀ y ∈ M₁, x * y * x⁻¹ = y⁻¹)
    (hout₂ : ∀ x ∈ Q₂, x ∉ M₂ → x * x = z ∧ ∀ y ∈ M₂, x * y * x⁻¹ = y⁻¹)
    (hw₁ : w₁ ∈ Q₁) (hw₁M : w₁ ∉ M₁) (hw₂ : w₂ ∈ Q₂) (hw₂M : w₂ ∉ M₂)
    (hm₁Q : m₁ ∈ M₁) (hm₁sq : m₁ * m₁ = z) (hm₁c : ∀ y ∈ Q₂, m₁ * y = y * m₁) :
    Nat.card ↥((Q₁ ⊔ Q₂) ⊓ centralizer ({w₁ * w₂} : Set G)) ≤ 16 := by
  have hQ₁S : Q₁ ≤ Q₁ ⊔ Q₂ := le_sup_left
  have hQ₂S : Q₂ ≤ Q₁ ⊔ Q₂ := le_sup_right
  have hzQ₁ : z ∈ Q₁ := hM₁ hz₁
  have hzQ₂ : z ∈ Q₂ := hM₂ hz₂
  have hZinf : ∀ x ∈ Q₁, x ∈ Q₂ → x ∈ zpowers z := by
    intro x h1 h2
    rw [← hQ]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  have hZc : ∀ ζ ∈ zpowers z, ∀ g ∈ Q₁ ⊔ Q₂, ζ * g = g * ζ := by
    intro ζ hζ g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hζ
    exact (Commute.zpow_left (show Commute z g from hzc g hg) k).eq
  have hA₁ : ∀ b ∈ Q₂, ∀ y ∈ Q₁, b * y * b⁻¹ ∈ Q₁ := fun b hb y hy => hN₁ b (hQ₂S hb) y hy
  have hB₁ : ∀ a ∈ Q₁, ∀ y ∈ Q₂, a * y * a⁻¹ ∈ Q₂ := fun a ha y hy => hN₂ a (hQ₁S ha) y hy
  have hcomm12 : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
    intro a ha b hb
    have h1 := Cent16.comm_mem_inf hA₁ hB₁ ha hb
    rwa [hQ] at h1
  have hcomm21 : ∀ a ∈ Q₂, ∀ b ∈ Q₁, a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
    intro a ha b hb
    have h1 := Cent16.comm_mem_inf hB₁ hA₁ ha hb
    rwa [inf_comm, hQ] at h1
  obtain ⟨U₁, hU₁⟩ := Cent16.exists_twist hzc w₁
  obtain ⟨U₂, hU₂⟩ := Cent16.exists_twist hzc w₂
  have hQ₂U₁ : ∀ g ∈ Q₂, g ∈ U₁ := fun g hg =>
    (hU₁ g).2 ⟨hQ₂S hg, g * w₁ * g⁻¹ * w₁⁻¹, hcomm21 g hg w₁ hw₁, by group⟩
  have hQ₁U₂ : ∀ g ∈ Q₁, g ∈ U₂ := fun g hg =>
    (hU₂ g).2 ⟨hQ₁S hg, g * w₂ * g⁻¹ * w₂⁻¹, hcomm12 g hg w₂ hw₂, by group⟩
  have hzT₁ : z ∈ Q₁ ⊓ U₁ := by
    refine Subgroup.mem_inf.2 ⟨hzQ₁, (hU₁ z).2 ⟨hQ₁S hzQ₁, 1, one_mem _, ?_⟩⟩
    rw [one_mul, hzc w₁ (hQ₁S hw₁)]
    group
  have hzT₂ : z ∈ Q₂ ⊓ U₂ := by
    refine Subgroup.mem_inf.2 ⟨hzQ₂, (hU₂ z).2 ⟨hQ₂S hzQ₂, 1, one_mem _, ?_⟩⟩
    rw [one_mul, hzc w₂ (hQ₂S hw₂)]
    group
  have hZT₁ : zpowers z ≤ Q₁ ⊓ U₁ := zpowers_le.2 hzT₁
  have hT₁ : Nat.card ↥(Q₁ ⊓ U₁) ≤ 8 :=
    Cent16.card_inf_le hz2 hq₁ hM₁ hc₁ hm₁ hout₁ hw₁ hw₁M (fun g _ hg => ((hU₁ g).1 hg).2)
  have hT₂ : Nat.card ↥(Q₂ ⊓ U₂) ≤ 8 :=
    Cent16.card_inf_le hz2 hq₂ hM₂ hc₂ hm₂ hout₂ hw₂ hw₂M (fun g _ hg => ((hU₂ g).1 hg).2)
  have hnT : Q₂ ⊓ U₂ ≤ normalizer ((Q₁ ⊓ U₁ : Subgroup G) : Set G) := by
    apply Cent16.le_normalizer
    intro t ht x hx
    have htQ : t ∈ Q₂ := (Subgroup.mem_inf.1 ht).1
    have hxQ : x ∈ Q₁ := (Subgroup.mem_inf.1 hx).1
    have e : t * x * t⁻¹ = (t * x * t⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (hZT₁ (hcomm21 t htQ x hxQ)) hx
  have hI : 2 ≤ Nat.card ↥((Q₁ ⊓ U₁) ⊓ (Q₂ ⊓ U₂)) := by
    have hbot : (Q₁ ⊓ U₁) ⊓ (Q₂ ⊓ U₂) ≠ ⊥ := by
      intro h
      have hz' : z ∈ (Q₁ ⊓ U₁) ⊓ (Q₂ ⊓ U₂) := Subgroup.mem_inf.2 ⟨hzT₁, hzT₂⟩
      rw [h, Subgroup.mem_bot] at hz'
      exact hz1 hz'
    have := (Subgroup.one_lt_card_iff_ne_bot _).2 hbot
    omega
  have hK : Nat.card ↥((Q₁ ⊓ U₁) ⊔ (Q₂ ⊓ U₂)) ≤ 32 := by
    have hprod := card_sup_mul_card_inf' hnT
    have h1 : Nat.card ↥(Q₁ ⊓ U₁) * Nat.card ↥(Q₂ ⊓ U₂) ≤ 8 * 8 := Nat.mul_le_mul hT₁ hT₂
    have h2 := Nat.mul_le_mul_left (Nat.card ↥((Q₁ ⊓ U₁) ⊔ (Q₂ ⊓ U₂))) hI
    omega
  have hC : (Q₁ ⊔ Q₂) ⊓ centralizer ({w₁ * w₂} : Set G) ≤ (Q₁ ⊓ U₁) ⊔ (Q₂ ⊓ U₂) := by
    intro c hcC
    obtain ⟨hcS, hcc⟩ := Subgroup.mem_inf.1 hcC
    have hcw : c * (w₁ * w₂) * c⁻¹ = w₁ * w₂ := by
      have h1 := (Subgroup.mem_centralizer_iff.1 hcc) (w₁ * w₂) (Set.mem_singleton _)
      rw [← h1]
      group
    have hp : c * w₁ * c⁻¹ ∈ Q₁ := hN₁ c hcS w₁ hw₁
    have hq : c * w₂ * c⁻¹ ∈ Q₂ := hN₂ c hcS w₂ hw₂
    have e0 : c * w₁ * c⁻¹ = (c * (w₁ * w₂) * c⁻¹) * (c * w₂ * c⁻¹)⁻¹ := by group
    rw [hcw] at e0
    have hr : w₁⁻¹ * (c * w₁ * c⁻¹) = w₂ * (c * w₂ * c⁻¹)⁻¹ := by
      rw [e0]
      group
    have hrZ : w₁⁻¹ * (c * w₁ * c⁻¹) ∈ zpowers z := by
      apply hZinf
      · exact mul_mem (inv_mem hw₁) hp
      · rw [hr]
        exact mul_mem hw₂ (inv_mem hq)
    obtain ⟨ζ, hζ, hζ₁⟩ : ∃ ζ ∈ zpowers z, ζ = w₁⁻¹ * (c * w₁ * c⁻¹) := ⟨_, hrZ, rfl⟩
    have hcw₁ : c * w₁ * c⁻¹ = ζ * w₁ := by
      rw [hZc ζ hζ w₁ (hQ₁S hw₁), hζ₁]
      group
    have hcw₂ : c * w₂ * c⁻¹ = ζ⁻¹ * w₂ := by
      rw [hζ₁, hr]
      group
    have hcU₁ : c ∈ U₁ := (hU₁ c).2 ⟨hcS, ζ, hζ, hcw₁⟩
    have hcU₂ : c ∈ U₂ := (hU₂ c).2 ⟨hcS, ζ⁻¹, inv_mem hζ, hcw₂⟩
    obtain ⟨c₁, hc₁Q, c₂, hc₂Q, rfl⟩ := mem_sup_of_le_normalizer' (Cent16.le_normalizer hB₁) hcS
    have hc₁U : c₁ ∈ U₁ := by
      have h1 := mul_mem hcU₁ (inv_mem (hQ₂U₁ c₂ hc₂Q))
      rwa [mul_inv_cancel_right] at h1
    have hc₂U : c₂ ∈ U₂ := by
      have h1 := mul_mem (inv_mem (hQ₁U₂ c₁ hc₁Q)) hcU₂
      rwa [inv_mul_cancel_left] at h1
    exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hc₁Q, hc₁U⟩))
      (mem_sup_right (Subgroup.mem_inf.2 ⟨hc₂Q, hc₂U⟩))
  have hm₁Q₁ : m₁ ∈ Q₁ := hM₁ hm₁Q
  have hwm : w₁ * m₁⁻¹ * w₁⁻¹ = m₁ := by
    have h1 := (hout₁ w₁ hw₁ hw₁M).2 m₁⁻¹ (inv_mem hm₁Q)
    rwa [inv_inv] at h1
  have hm₁w₁ : m₁ * w₁ * m₁⁻¹ = z * w₁ := by
    calc m₁ * w₁ * m₁⁻¹ = m₁ * (w₁ * m₁⁻¹ * w₁⁻¹) * w₁ := by group
      _ = m₁ * m₁ * w₁ := by rw [hwm]
      _ = z * w₁ := by rw [hm₁sq]
  have hm₁w₂ : m₁ * w₂ * m₁⁻¹ = w₂ := by
    rw [hm₁c w₂ hw₂]
    group
  have hm₁T : m₁ ∈ (Q₁ ⊓ U₁) ⊔ (Q₂ ⊓ U₂) :=
    mem_sup_left (Subgroup.mem_inf.2 ⟨hm₁Q₁, (hU₁ m₁).2 ⟨hQ₁S hm₁Q₁, z, mem_zpowers z, hm₁w₁⟩⟩)
  have hm₁C : m₁ ∉ (Q₁ ⊔ Q₂) ⊓ centralizer ({w₁ * w₂} : Set G) := by
    intro h
    have h1 := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 h).2) (w₁ * w₂)
      (Set.mem_singleton _)
    have h2 : m₁ * (w₁ * w₂) * m₁⁻¹ = z * (w₁ * w₂) := by
      calc m₁ * (w₁ * w₂) * m₁⁻¹ = (m₁ * w₁ * m₁⁻¹) * (m₁ * w₂ * m₁⁻¹) := by group
        _ = z * (w₁ * w₂) := by rw [hm₁w₁, hm₁w₂, mul_assoc]
    have h3 : m₁ * (w₁ * w₂) * m₁⁻¹ = w₁ * w₂ := by
      rw [← h1]
      group
    rw [h3] at h2
    apply hz1
    have h4 : z * (w₁ * w₂) = 1 * (w₁ * w₂) := by
      rw [one_mul]
      exact h2.symm
    exact mul_right_cancel h4
  have hdvd := Subgroup.card_dvd_of_le hC
  have hne : Nat.card ↥((Q₁ ⊔ Q₂) ⊓ centralizer ({w₁ * w₂} : Set G)) ≠
      Nat.card ↥((Q₁ ⊓ U₁) ⊔ (Q₂ ⊓ U₂)) := by
    intro h
    have hCK : (Q₁ ⊔ Q₂) ⊓ centralizer ({w₁ * w₂} : Set G) = (Q₁ ⊓ U₁) ⊔ (Q₂ ⊓ U₂) :=
      Subgroup.eq_of_le_of_card_ge hC h.ge
    apply hm₁C
    rw [hCK]
    exact hm₁T
  have hKpos : 0 < Nat.card ↥((Q₁ ⊓ U₁) ⊔ (Q₂ ⊓ U₂)) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k <;> omega
  have h2 := Nat.mul_le_mul_left
    (Nat.card ↥((Q₁ ⊔ Q₂) ⊓ centralizer ({w₁ * w₂} : Set G))) hk2
  omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
