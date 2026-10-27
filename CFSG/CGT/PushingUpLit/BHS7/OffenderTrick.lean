module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem commutator_mem_centralizer {W : Subgroup Γ} {y b : Γ}
    (hy : y ∈ Subgroup.normalizer (W : Set Γ)) (hb : b ∈ Subgroup.normalizer (W : Set Γ))
    (h : y ∈ Subgroup.centralizer (W : Set Γ) ∨ b ∈ Subgroup.centralizer (W : Set Γ)) :
    y * b * y⁻¹ * b⁻¹ ∈ Subgroup.centralizer (W : Set Γ) := by
  rcases h with hyc | hbc
  · have h1 : b * y⁻¹ * b⁻¹ ∈ Subgroup.centralizer (W : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : b⁻¹ * w * b ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hb) w).mp hw
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer _).inv_mem hyc) _ hw'
      calc w * (b * y⁻¹ * b⁻¹) = b * ((b⁻¹ * w * b) * y⁻¹) * b⁻¹ := by group
        _ = b * (y⁻¹ * (b⁻¹ * w * b)) * b⁻¹ := by rw [hc]
        _ = (b * y⁻¹ * b⁻¹) * w := by group
    have h2 : y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
    rw [h2]
    exact (Subgroup.centralizer _).mul_mem hyc h1
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : y⁻¹ * w * y ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hy) w).mp hw
      simpa using this
    have hbw' : (y⁻¹ * w * y) * b = b * (y⁻¹ * w * y) :=
      Subgroup.mem_centralizer_iff.mp hbc _ hw'
    have hbw : w * b⁻¹ = b⁻¹ * w :=
      Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer _).inv_mem hbc) w hw
    calc w * (y * b * y⁻¹ * b⁻¹)
        = y * ((y⁻¹ * w * y) * b) * y⁻¹ * b⁻¹ := by group
      _ = y * (b * (y⁻¹ * w * y)) * y⁻¹ * b⁻¹ := by rw [hbw']
      _ = y * b * y⁻¹ * (w * b⁻¹) := by group
      _ = y * b * y⁻¹ * (b⁻¹ * w) := by rw [hbw]
      _ = (y * b * y⁻¹ * b⁻¹) * w := by group

theorem eq_one_or_eq_of_mem_zpowers {u p : Γ} (hu : u ^ 2 = 1) (hp : p ∈ Subgroup.zpowers u) :
    p = 1 ∨ p = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  have hu' : u ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← sq]
    exact hu
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, hu', one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hu', one_zpow, one_mul]

variable [Finite Γ]

theorem false_of_offender {T A W₁ W₂ : Subgroup Γ} (hA : IsMaxElemAbelian T A)
    (hW₁ : IsElemAbelian 2 W₁) (hW₂ : IsElemAbelian 2 W₂) (hW₁T : W₁ ≤ T) (hW₂T : W₂ ≤ T)
    (h12 : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x) (hdisj : ∀ x ∈ W₁, x ∈ W₂ → x = 1)
    (hAN₁ : ∀ a ∈ A, ∀ w ∈ W₁, a * w * a⁻¹ ∈ W₁) (hAN₂ : ∀ a ∈ A, ∀ w ∈ W₂, a * w * a⁻¹ ∈ W₂)
    {a : Γ} (ha : a ∈ A) {u₁ u₂ : Γ} (hu₁ : u₁ ∈ W₁) (hu₂ : u₂ ∈ W₂)
    (hu₁a : a * u₁ * a⁻¹ ≠ u₁) (hu₂a : a * u₂ * a⁻¹ ≠ u₂)
    (hidx : ∀ b ∈ A,
      b ∈ A ⊓ Subgroup.centralizer (W₁ : Set Γ) ⊓ Subgroup.centralizer (W₂ : Set Γ) ∨
      a⁻¹ * b ∈ A ⊓ Subgroup.centralizer (W₁ : Set Γ) ⊓ Subgroup.centralizer (W₂ : Set Γ)) :
    False := by
  classical
  set A₀ : Subgroup Γ :=
    A ⊓ Subgroup.centralizer (W₁ : Set Γ) ⊓ Subgroup.centralizer (W₂ : Set Γ) with hA₀
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAT : A ≤ T := hA.1
  have hA₀A : A₀ ≤ A := inf_le_left.trans inf_le_left
  have hu₁2 : u₁ ^ 2 = 1 := hW₁.2 u₁ hu₁
  have hu₂2 : u₂ ^ 2 = 1 := hW₂.2 u₂ hu₂
  have hu₁ne : u₁ ≠ 1 := fun e => hu₁a (by rw [e]; group)
  have hu₂ne : u₂ ≠ 1 := fun e => hu₂a (by rw [e]; group)
  set Z₁ : Subgroup Γ := Subgroup.zpowers u₁ with hZ₁
  set Z₂ : Subgroup Γ := Subgroup.zpowers u₂ with hZ₂
  have hZ₁W : Z₁ ≤ W₁ := (Subgroup.zpowers_le).mpr hu₁
  have hZ₂W : Z₂ ≤ W₂ := (Subgroup.zpowers_le).mpr hu₂
  have hZ₁e : IsElemAbelian 2 Z₁ := isElemAbelian_mono' hW₁ hZ₁W
  have hZ₂e : IsElemAbelian 2 Z₂ := isElemAbelian_mono' hW₂ hZ₂W
  have hZc : ∀ x ∈ Z₁, ∀ y ∈ Z₂, x * y = y * x := fun x hx y hy => h12 x (hZ₁W hx) y (hZ₂W hy)
  set U : Subgroup Γ := Z₁ ⊔ Z₂ with hU
  have hUe : IsElemAbelian 2 U := isElemAbelian_sup' hZ₁e hZ₂e hZc
  have hUW : U ≤ W₁ ⊔ W₂ := sup_le_sup hZ₁W hZ₂W
  have hUT : U ≤ T := hUW.trans (sup_le hW₁T hW₂T)
  have hZ₁card : Nat.card Z₁ = 2 := by
    rw [hZ₁, Nat.card_zpowers, orderOf_eq_prime hu₁2 hu₁ne]
  have hZ₂card : Nat.card Z₂ = 2 := by
    rw [hZ₂, Nat.card_zpowers, orderOf_eq_prime hu₂2 hu₂ne]
  have hZ₁₂ : Z₁ ⊓ Z₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hdisj x (hZ₁W hx.1) (hZ₂W hx.2)
  have hUcard : Nat.card U = 4 := by
    have h1 : Nat.card ↥(Z₁ ⊔ Z₂) * Nat.card ↥(Z₁ ⊓ Z₂) = Nat.card Z₁ * Nat.card Z₂ :=
      card_sup_mul_card_inf' hZc
    rw [hZ₁₂, hZ₁card, hZ₂card, Subgroup.card_bot] at h1
    show Nat.card ↥(Z₁ ⊔ Z₂) = 4
    omega
  have hAU : A₀ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxA : x ∈ A := hA₀A hx.1
    have hxa : a * x * a⁻¹ = x := by
      rw [isElemAbelian_comm' hAe ha hxA]
      group
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup' hZc hx.2
    have hp' := eq_one_or_eq_of_mem_zpowers hu₁2 hp
    have hq' := eq_one_or_eq_of_mem_zpowers hu₂2 hq
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
    · simp
    · exact absurd (by simpa using hxa) hu₂a
    · exact absurd (by simpa using hxa) hu₁a
    · exfalso
      have hv₁ : a * p * a⁻¹ ∈ W₁ := hAN₁ a ha p hu₁
      have hv₂ : a * q * a⁻¹ ∈ W₂ := hAN₂ a ha q hu₂
      have h3 : (a * p * a⁻¹) * (a * q * a⁻¹) = p * q := by
        calc (a * p * a⁻¹) * (a * q * a⁻¹) = a * (p * q) * a⁻¹ := by group
          _ = p * q := hxa
      have h4 : p⁻¹ * (a * p * a⁻¹) = q * (a * q * a⁻¹)⁻¹ := by
        calc p⁻¹ * (a * p * a⁻¹) = p⁻¹ * ((a * p * a⁻¹) * (a * q * a⁻¹)) * (a * q * a⁻¹)⁻¹ := by
              group
          _ = p⁻¹ * (p * q) * (a * q * a⁻¹)⁻¹ := by rw [h3]
          _ = q * (a * q * a⁻¹)⁻¹ := by group
      have h5 : p⁻¹ * (a * p * a⁻¹) ∈ W₁ := W₁.mul_mem (W₁.inv_mem hu₁) hv₁
      have h6 : q * (a * q * a⁻¹)⁻¹ ∈ W₂ := W₂.mul_mem hu₂ (W₂.inv_mem hv₂)
      have h7 := hdisj _ h5 (h4 ▸ h6)
      apply hu₁a
      calc a * p * a⁻¹ = p * (p⁻¹ * (a * p * a⁻¹)) := by group
        _ = p := by rw [h7, mul_one]
  have hA₀e : IsElemAbelian 2 A₀ := isElemAbelian_mono' hAe hA₀A
  have hA₀U : ∀ x ∈ A₀, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    have hxc1 : x ∈ Subgroup.centralizer (W₁ : Set Γ) := hx.1.2
    have hxc2 : x ∈ Subgroup.centralizer (W₂ : Set Γ) := hx.2
    have hle : W₁ ⊔ W₂ ≤ Subgroup.centralizer ({x} : Set Γ) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (Subgroup.mem_centralizer_iff.mp hxc1 w hw).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (Subgroup.mem_centralizer_iff.mp hxc2 w hw).symm
    exact Subgroup.mem_centralizer_iff.mp (hle (hUW hy)) x (Set.mem_singleton x)
  have hXe : IsElemAbelian 2 (A₀ ⊔ U) := isElemAbelian_sup' hA₀e hUe hA₀U
  have hXT : A₀ ⊔ U ≤ T := sup_le (hA₀A.trans hAT) hUT
  have hXcard : Nat.card ↥(A₀ ⊔ U) * Nat.card ↥(A₀ ⊓ U) = Nat.card A₀ * Nat.card U :=
    card_sup_mul_card_inf' hA₀U
  rw [hAU, Subgroup.card_bot, hUcard] at hXcard
  have hle := hA.2.2 (A₀ ⊔ U) hXT hXe
  have hAcard : Nat.card A ≤ 2 * Nat.card A₀ := by
    have hsub : (A : Set Γ) ⊆ (A₀ : Set Γ) ∪ (fun x => a * x) '' (A₀ : Set Γ) := by
      intro b hb
      rcases hidx b hb with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨a⁻¹ * b, h1, by simp⟩
    have h1 : (A : Set Γ).ncard ≤
        ((A₀ : Set Γ) ∪ (fun x => a * x) '' (A₀ : Set Γ)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (A₀ : Set Γ) ((fun x => a * x) '' (A₀ : Set Γ))
    have h3 : ((fun x => a * x) '' (A₀ : Set Γ)).ncard = (A₀ : Set Γ).ncard :=
      Set.ncard_image_of_injective _ (mul_right_injective a)
    have e1 : Nat.card A = (A : Set Γ).ncard := Nat.card_coe_set_eq (A : Set Γ)
    have e2 : Nat.card A₀ = (A₀ : Set Γ).ncard := Nat.card_coe_set_eq (A₀ : Set Γ)
    omega
  have hpos : 0 < Nat.card A₀ := Nat.card_pos
  omega

end CFSG.CGT.PushingUpLit.BHS7
