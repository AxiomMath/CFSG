module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup

theorem t6_card_max_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {C Q : Subgroup G}
    (hQC : Q ≤ C) (hQp : IsPGroup p ↥Q)
    (hmax : ∀ E : Subgroup G, E ≤ C → IsPGroup p ↥E → Nat.card ↥E ≤ Nat.card ↥Q) :
    Nat.card ↥(Q.subgroupOf C) = p ^ (Nat.card ↥C).factorization p := by
  obtain ⟨S, hS⟩ := (hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm).exists_le_sylow
  have h1 : Nat.card ↥(Q.subgroupOf C) ≤ Nat.card ↥(S : Subgroup ↥C) := Subgroup.card_le_of_le hS
  have h2 : Nat.card ↥(S : Subgroup ↥C) ≤ Nat.card ↥Q := by
    have := hmax ((S : Subgroup ↥C).map C.subtype) (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective C.subtype_injective] at this
  have h3 : Nat.card ↥(Q.subgroupOf C) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
  rw [← Sylow.card_eq_multiplicity S]
  omega

theorem t6_sylow_conj_of_max {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C Q₁ Q₂ : Subgroup G} (h₁C : Q₁ ≤ C) (h₂C : Q₂ ≤ C) (h₁p : IsPGroup p ↥Q₁)
    (h₂p : IsPGroup p ↥Q₂)
    (hm₁ : ∀ E : Subgroup G, E ≤ C → IsPGroup p ↥E → Nat.card ↥E ≤ Nat.card ↥Q₁)
    (hm₂ : ∀ E : Subgroup G, E ≤ C → IsPGroup p ↥E → Nat.card ↥E ≤ Nat.card ↥Q₂) :
    ∃ c ∈ C, ∀ x : G, x ∈ Q₁ ↔ c * x * c⁻¹ ∈ Q₂ := by
  have : Fact p.Prime := ⟨hp⟩
  let S₁ : Sylow p ↥C := Sylow.ofCard (Q₁.subgroupOf C) (t6_card_max_sylow h₁C h₁p hm₁)
  let S₂ : Sylow p ↥C := Sylow.ofCard (Q₂.subgroupOf C) (t6_card_max_sylow h₂C h₂p hm₂)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C S₁ S₂
  have hcS : ∀ y : ↥C, y ∈ (S₂ : Subgroup ↥C) ↔ c⁻¹ * y * c ∈ (S₁ : Subgroup ↥C) := by
    intro y
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have e : c⁻¹ * (c * s * c⁻¹) * c = s := by group
      show c⁻¹ * (c * s * c⁻¹) * c ∈ (S₁ : Subgroup ↥C)
      rw [e]; exact hs
    · intro hy
      refine ⟨c⁻¹ * y * c, hy, ?_⟩
      show c * (c⁻¹ * y * c) * c⁻¹ = y
      group
  refine ⟨c, c.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxC : x ∈ C := h₁C hx
    have h1 : (⟨x, hxC⟩ : ↥C) ∈ (S₁ : Subgroup ↥C) := hx
    have h2 : c * ⟨x, hxC⟩ * c⁻¹ ∈ (S₂ : Subgroup ↥C) := (hcS _).2 (by
      have e : c⁻¹ * (c * ⟨x, hxC⟩ * c⁻¹) * c = ⟨x, hxC⟩ := by group
      rw [e]; exact h1)
    exact h2
  · intro hx
    have hxC : x ∈ C := by
      have := C.mul_mem (C.mul_mem (C.inv_mem c.2) (h₂C hx)) c.2
      have e : (c : G)⁻¹ * (c * x * (c : G)⁻¹) * c = x := by group
      rwa [e] at this
    have h2 : (⟨c * x * (c : G)⁻¹, h₂C hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) := hx
    have h3 := (hcS _).1 h2
    have e : (c⁻¹ * ⟨c * x * (c : G)⁻¹, h₂C hx⟩ * c : ↥C) = ⟨x, hxC⟩ :=
      Subtype.ext (by
        show (c : G)⁻¹ * (c * x * (c : G)⁻¹) * c = x
        group)
    rw [e] at h3
    exact h3

theorem t6_no_three_cycle {G : Type} [Group G] {n x₀ x₁ x₂ : G} (h0 : x₀ ≠ x₁) (h0' : x₀ ≠ x₂)
    (e0 : n * x₀ * n⁻¹ = x₁) (e1 : n * x₁ * n⁻¹ = x₂) (e2 : n * x₂ * n⁻¹ = x₀)
    (h2 : ∃ k : ℕ, n ^ (2 ^ k) = 1) : False := by
  obtain ⟨k, hk⟩ := h2
  have h3 : ¬ 3 ∣ 2 ^ k := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  set c : G := n ^ 3 with hc
  have hcx : c * x₀ * c⁻¹ = x₀ := by
    have : c * x₀ * c⁻¹ = n * (n * (n * x₀ * n⁻¹) * n⁻¹) * n⁻¹ := by
      rw [hc, pow_three]; group
    rw [this, e0, e1, e2]
  have hcq : ∀ q : ℕ, c ^ q * x₀ * (c ^ q)⁻¹ = x₀ := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      calc c ^ (q + 1) * x₀ * (c ^ (q + 1))⁻¹ = c ^ q * (c * x₀ * c⁻¹) * (c ^ q)⁻¹ := by
            rw [pow_succ']; group
        _ = x₀ := by rw [hcx, ih]
  have hm : 2 ^ k = 3 * (2 ^ k / 3) + 2 ^ k % 3 := (Nat.div_add_mod _ _).symm
  have hr : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have : 2 ^ k % 3 ≠ 0 := fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
    omega
  set q := 2 ^ k / 3 with hq
  set r := 2 ^ k % 3 with hrdef
  have hnm : c ^ q * n ^ r = 1 := by
    rw [hc, ← pow_mul, ← pow_add, ← hk, hm]
  have hnr : n ^ r = (c ^ q)⁻¹ := eq_inv_of_mul_eq_one_right hnm
  have hconj : n ^ r * x₀ * (n ^ r)⁻¹ = x₀ := by
    rw [hnr, inv_inv]
    have := hcq q
    calc (c ^ q)⁻¹ * x₀ * c ^ q = (c ^ q)⁻¹ * (c ^ q * x₀ * (c ^ q)⁻¹) * c ^ q := by rw [this]
      _ = x₀ := by group
  rcases hr with hr | hr
  · rw [hr, pow_one, e0] at hconj
    exact h0 hconj.symm
  · rw [hr] at hconj
    have : n ^ 2 * x₀ * (n ^ 2)⁻¹ = x₂ := by
      calc n ^ 2 * x₀ * (n ^ 2)⁻¹ = n * (n * x₀ * n⁻¹) * n⁻¹ := by rw [pow_two]; group
        _ = x₂ := by rw [e0, e1]
    rw [this] at hconj
    exact h0' hconj.symm

theorem t6_fixed_pt_klein {G : Type} [Group G] {z u n : G} (hz2 : z * z = 1) (hu2 : u * u = 1)
    (hzu : z * u = u * z) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hne : z ≠ u)
    (hn : ∀ g : G, (g = 1 ∨ g = z ∨ g = u ∨ g = z * u) →
      (n * g * n⁻¹ = 1 ∨ n * g * n⁻¹ = z ∨ n * g * n⁻¹ = u ∨ n * g * n⁻¹ = z * u))
    (h2 : ∃ k : ℕ, n ^ (2 ^ k) = 1) :
    n * z * n⁻¹ = z ∨ n * u * n⁻¹ = u ∨ n * (z * u) * n⁻¹ = z * u := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hzf, huf, hzuf⟩ := hcon
  have hz' := hn z (Or.inr (Or.inl rfl))
  have hu' := hn u (Or.inr (Or.inr (Or.inl rfl)))
  have hzu' := hn (z * u) (Or.inr (Or.inr (Or.inr rfl)))
  have hcj : ∀ a b : G, n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := fun a b => by group
  have hinj : ∀ a : G, n * a * n⁻¹ = 1 → a = 1 := fun a h => by
    have : a = n⁻¹ * (n * a * n⁻¹) * n := by group
    rw [this, h]; group
  have hzu1 : z * u ≠ 1 := by
    intro h
    apply hne
    have : z = u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hu2]
  have hza : n * z * n⁻¹ ≠ 1 := fun h => hz1 (hinj z h)
  have hub : n * u * n⁻¹ ≠ 1 := fun h => hu1 (hinj u h)
  have hzuc : n * (z * u) * n⁻¹ ≠ 1 := fun h => hzu1 (hinj _ h)
  have ha : n * z * n⁻¹ = u ∨ n * z * n⁻¹ = z * u := by
    rcases hz' with h | h | h | h
    · exact absurd h hza
    · exact absurd h hzf
    · exact Or.inl h
    · exact Or.inr h
  have hb : n * u * n⁻¹ = z ∨ n * u * n⁻¹ = z * u := by
    rcases hu' with h | h | h | h
    · exact absurd h hub
    · exact Or.inl h
    · exact absurd h huf
    · exact Or.inr h
  have hc : n * (z * u) * n⁻¹ = z ∨ n * (z * u) * n⁻¹ = u := by
    rcases hzu' with h | h | h | h
    · exact absurd h hzuc
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hzuf
  have hzu_ne : z ≠ z * u := by
    intro h
    apply hu1
    calc u = z⁻¹ * (z * u) := by group
      _ = z⁻¹ * z := by rw [← h]
      _ = 1 := by group
  rw [hcj] at hc
  rcases ha with ha | ha <;> rcases hb with hb | hb
  ·
    rw [ha, hb] at hc
    rcases hc with hc | hc
    · apply hu1
      calc u = u * z * z⁻¹ := by group
        _ = z * z⁻¹ := by rw [hc]
        _ = 1 := by group
    · apply hz1
      calc z = u⁻¹ * (u * z) := by group
        _ = u⁻¹ * u := by rw [hc]
        _ = 1 := by group
  ·
    have e2 : n * (z * u) * n⁻¹ = z := by
      rw [hcj, ha, hb]
      calc u * (z * u) = (u * z) * u := by group
        _ = (z * u) * u := by rw [← hzu]
        _ = z * (u * u) := by group
        _ = z := by rw [hu2, mul_one]
    exact t6_no_three_cycle (n := n) hne hzu_ne ha hb e2 h2
  ·
    have e1 : n * (z * u) * n⁻¹ = u := by
      rw [hcj, ha, hb]
      calc z * u * z = (u * z) * z := by rw [hzu]
        _ = u * (z * z) := by group
        _ = u := by rw [hz2, mul_one]
    exact t6_no_three_cycle (n := n) (x₀ := z) (x₁ := z * u) (x₂ := u) hzu_ne hne ha e1 hb h2
  ·
    apply hne
    have h1 : n * z * n⁻¹ = n * u * n⁻¹ := by rw [ha, hb]
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = n⁻¹ * (n * u * n⁻¹) * n := by rw [h1]
      _ = u := by group

end CFSG.GH74.GLS.Stage4.Rest.T6
