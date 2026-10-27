module

public import CFSG.GH74.GLS.Stage2.Local.Lemma23e
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Q8

theorem q8_comm_central : ∀ x y g : QuaternionGroup 2, g * ⁅x, y⁆ = ⁅x, y⁆ * g := by decide

theorem q8_center :
    ∀ x : QuaternionGroup 2, (∀ g, g * x = x * g) → x = 1 ∨ x = QuaternionGroup.a 2 := by decide

variable {Y : Type} [Group Y]

theorem comm_central_of_q8 {A : Subgroup Y} (hA : Nonempty (↥A ≃* QuaternionGroup 2)) {x y g : Y}
    (hx : x ∈ A) (hy : y ∈ A) (hg : g ∈ A) : g * ⁅x, y⁆ = ⁅x, y⁆ * g := by
  obtain ⟨φ⟩ := hA
  have := q8_comm_central (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) (φ ⟨g, hg⟩)
  have h2 : φ (⟨g, hg⟩ * ⁅(⟨x, hx⟩ : ↥A), ⟨y, hy⟩⁆) = φ (⁅(⟨x, hx⟩ : ↥A), ⟨y, hy⟩⁆ * ⟨g, hg⟩) := by
    simpa [map_mul, map_commutatorElement] using this
  have h3 := φ.injective h2
  exact congrArg Subtype.val h3

theorem center_q8 {A : Subgroup Y} (hA : Nonempty (↥A ≃* QuaternionGroup 2)) {ζ₀ : Y} (hζ₀A : ζ₀ ∈ A)
    (hζ₀1 : ζ₀ ≠ 1) (hζ₀c : ∀ g ∈ A, g * ζ₀ = ζ₀ * g) :
    ∀ x ∈ A, (∀ g ∈ A, g * x = x * g) → x = 1 ∨ x = ζ₀ := by
  obtain ⟨φ⟩ := hA
  have hcent : ∀ x : ↥A, (∀ g ∈ A, g * (x : Y) = (x : Y) * g) → ∀ g : QuaternionGroup 2,
      g * φ x = φ x * g := by
    intro x hx g
    obtain ⟨g', rfl⟩ := φ.surjective g
    have := hx g' g'.2
    have h2 : g' * x = x * g' := Subtype.ext this
    simpa [map_mul] using congrArg φ h2
  have hζ : φ ⟨ζ₀, hζ₀A⟩ = QuaternionGroup.a 2 := by
    have h1 := q8_center (φ ⟨ζ₀, hζ₀A⟩) (hcent ⟨ζ₀, hζ₀A⟩ hζ₀c)
    rcases h1 with h | h
    · exfalso
      apply hζ₀1
      have : (⟨ζ₀, hζ₀A⟩ : ↥A) = 1 := φ.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · exact h
  intro x hx hxc
  rcases q8_center (φ ⟨x, hx⟩) (hcent ⟨x, hx⟩ hxc) with h | h
  · left
    have : (⟨x, hx⟩ : ↥A) = 1 := φ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨x, hx⟩ : ↥A) = ⟨ζ₀, hζ₀A⟩ := φ.injective (by rw [h, hζ])
    exact congrArg Subtype.val this

theorem commutator_mul_mul_of_commute {a₁ a₂ b₁ b₂ : Y} (h₁ : a₁ * b₁ = b₁ * a₁)
    (h₂ : a₁ * b₂ = b₂ * a₁) (h₃ : a₂ * b₁ = b₁ * a₂) (h₄ : a₂ * b₂ = b₂ * a₂) :
    ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  have e₁ : Commute a₁⁻¹ b₁ := (show Commute a₁ b₁ from h₁).inv_left
  have e₂ : Commute a₁⁻¹ b₂ := (show Commute a₁ b₂ from h₂).inv_left
  have f₁ : Commute a₂⁻¹ b₁ := (show Commute a₂ b₁ from h₃).inv_left
  have f₂ : Commute a₂⁻¹ b₂ := (show Commute a₂ b₂ from h₄).inv_left
  have hswap1 : (b₁ * b₂ * b₁⁻¹) * a₁⁻¹ = a₁⁻¹ * (b₁ * b₂ * b₁⁻¹) :=
    ((e₁.mul_right e₂).mul_right e₁.inv_right).eq.symm
  have hswap2 : (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * a₂⁻¹ = a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) :=
    (((f₁.mul_right f₂).mul_right f₁.inv_right).mul_right f₂.inv_right).eq.symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc a₁ * b₁ * (a₂ * b₂) * (b₁⁻¹ * a₁⁻¹) * (b₂⁻¹ * a₂⁻¹)
      = a₁ * (b₁ * a₂) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * (a₂ * b₁) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [← h₃]
    _ = a₁ * a₂ * ((b₁ * b₂ * b₁⁻¹) * a₁⁻¹) * b₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * a₂ * (a₁⁻¹ * (b₁ * b₂ * b₁⁻¹)) * b₂⁻¹ * a₂⁻¹ := by rw [hswap1]
    _ = a₁ * a₂ * a₁⁻¹ * ((b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * a₂⁻¹) := by group
    _ = a₁ * a₂ * a₁⁻¹ * (a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹)) := by rw [hswap2]
    _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by group

end Q8

section Ext

variable {Y : Type} [Group Y]

theorem commutator_mul_right_of_commute {a' a b : Y} (h : a' * b = b * a') :
    ⁅a', a * b⁆ = ⁅a', a⁆ := by
  have e : Commute a'⁻¹ b := (show Commute a' b from h).inv_left
  have hb' : b * a'⁻¹ = a'⁻¹ * b := e.eq.symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc a' * (a * b) * a'⁻¹ * (b⁻¹ * a⁻¹) = a' * a * (b * a'⁻¹) * b⁻¹ * a⁻¹ := by group
    _ = a' * a * (a'⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hb']
    _ = a' * a * a'⁻¹ * a⁻¹ := by group

theorem q8_central_product {A B W : Subgroup Y} (hprod : IsCentralProd A B W)
    (hA : Nonempty (↥A ≃* QuaternionGroup 2)) (hB : Nonempty (↥B ≃* QuaternionGroup 2)) :
    ∃ ζ : Y, ζ ∈ A ∧ ζ ∈ B ∧ ζ ≠ 1 ∧ ζ ^ 2 = 1 ∧ A ⊓ B = zpowers ζ ∧
      (∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ zpowers ζ) ∧
      (∀ x ∈ W, (∀ g ∈ W, g * x = x * g) → x ∈ zpowers ζ) ∧
      (∀ u ∈ W, u ∉ zpowers ζ → ∃ w ∈ W, ⁅w, u⁆ = ζ) := by
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hfin : Finite ↥(A ⊓ B) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨ζ, hζ, hζ1⟩ : ∃ ζ ∈ A ⊓ B, ζ ≠ 1 := by
    by_contra hcon
    have hbot : A ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hζA : ζ ∈ A := hζ.1
  have hζB : ζ ∈ B := hζ.2
  have hord : orderOf ζ = 2 := by
    have h1 : orderOf (⟨ζ, hζ⟩ : ↥(A ⊓ B)) ∣ Nat.card ↥(A ⊓ B) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hcard] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hζ1
    · exact h
  have hζsq : ζ ^ 2 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hord] at this
  have hzp : zpowers ζ = A ⊓ B :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hζ)
      (by rw [hcard, Nat.card_zpowers, hord])
  have hζAc : ∀ g ∈ A, g * ζ = ζ * g := fun g hg => hcomm g hg ζ hζB
  have hζBc : ∀ g ∈ B, g * ζ = ζ * g := fun g hg => (hcomm ζ hζA g hg).symm
  have cenA := center_q8 hA hζA hζ1 hζAc
  have cenB := center_q8 hB hζB hζ1 hζBc
  have hζmem : ζ ∈ zpowers ζ := Subgroup.mem_zpowers ζ
  have h1mem : (1 : Y) ∈ zpowers ζ := Subgroup.one_mem _
  have hAB : ∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b := fun w hw =>
    exists_mul_of_mem_sup_of_commute hcomm (hsup ▸ hw)
  have hAW : A ≤ W := hsup ▸ le_sup_left
  have hBW : B ≤ W := hsup ▸ le_sup_right
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  refine ⟨ζ, hζA, hζB, hζ1, hζsq, hzp.symm, ?_, ?_, ?_⟩
  ·
    intro w hw w' hw'
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hAB w hw
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hAB w' hw'
    rw [commutator_mul_mul_of_commute (hcomm a₁ ha₁ b₁ hb₁) (hcomm a₁ ha₁ b₂ hb₂)
      (hcomm a₂ ha₂ b₁ hb₁) (hcomm a₂ ha₂ b₂ hb₂)]
    have hcA : ⁅a₁, a₂⁆ ∈ A := by
      simp only [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)
    have hcB : ⁅b₁, b₂⁆ ∈ B := by
      simp only [commutatorElement_def]
      exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)
    have h1 := cenA _ hcA (fun g hg => comm_central_of_q8 hA ha₁ ha₂ hg)
    have h2 := cenB _ hcB (fun g hg => comm_central_of_q8 hB hb₁ hb₂ hg)
    refine Subgroup.mul_mem _ ?_ ?_
    · rcases h1 with h | h <;> rw [h] <;> assumption
    · rcases h2 with h | h <;> rw [h] <;> assumption
  ·
    intro x hx hxc
    obtain ⟨a, ha, b, hb, rfl⟩ := hAB x hx
    have haA : ∀ g ∈ A, g * a = a * g := by
      intro g hg
      have h1 := hxc g (hAW hg)
      have h2 : g * (a * b) = a * g * b := by
        calc g * (a * b) = (a * b) * g := h1
          _ = a * (b * g) := by group
          _ = a * (g * b) := by rw [hcomm' b hb g hg]
          _ = a * g * b := by group
      have h3 : g * a * b = a * g * b := by rw [mul_assoc, h2]
      exact mul_right_cancel h3
    have hbB : ∀ g ∈ B, g * b = b * g := by
      intro g hg
      have h1 := hxc g (hBW hg)
      have h2 : g * (a * b) = a * (g * b) := by
        calc g * (a * b) = (g * a) * b := by group
          _ = (a * g) * b := by rw [hcomm' g hg a ha]
          _ = a * (g * b) := by group
      have h3 : a * (g * b) = a * (b * g) := by
        calc a * (g * b) = g * (a * b) := h2.symm
          _ = (a * b) * g := h1
          _ = a * (b * g) := by group
      exact mul_left_cancel h3
    refine Subgroup.mul_mem _ ?_ ?_
    · rcases cenA a ha haA with h | h <;> rw [h] <;> assumption
    · rcases cenB b hb hbB with h | h <;> rw [h] <;> assumption
  ·
    intro u hu hnu
    obtain ⟨a, ha, b, hb, rfl⟩ := hAB u hu
    by_cases haz : a ∈ zpowers ζ
    ·
      have haB : a ∈ B := by rw [hzp] at haz; exact haz.2
      have huB : a * b ∈ B := B.mul_mem haB hb
      have hnc : ¬ ∀ g ∈ B, g * (a * b) = (a * b) * g := by
        intro hc
        rcases cenB _ huB hc with h | h <;> rw [h] at hnu <;> exact hnu ‹_›
      push Not at hnc
      obtain ⟨b', hb', hne⟩ := hnc
      have hcB : ⁅b', a * b⁆ ∈ B := by
        simp only [commutatorElement_def]
        exact B.mul_mem (B.mul_mem (B.mul_mem hb' huB) (B.inv_mem hb')) (B.inv_mem huB)
      have hcen : ∀ g ∈ B, g * ⁅b', a * b⁆ = ⁅b', a * b⁆ * g := fun g hg =>
        comm_central_of_q8 hB hb' huB hg
      rcases cenB _ hcB hcen with h | h
      · exfalso
        apply hne
        have := (commutatorElement_eq_one_iff_mul_comm).mp h
        exact this
      · exact ⟨b', hBW hb', h⟩
    ·
      have hnc : ¬ ∀ g ∈ A, g * a = a * g := by
        intro hc
        rcases cenA a ha hc with h | h <;> rw [h] at haz <;> exact haz ‹_›
      push Not at hnc
      obtain ⟨a', ha', hne⟩ := hnc
      have hcA : ⁅a', a⁆ ∈ A := by
        simp only [commutatorElement_def]
        exact A.mul_mem (A.mul_mem (A.mul_mem ha' ha) (A.inv_mem ha')) (A.inv_mem ha)
      have hcen : ∀ g ∈ A, g * ⁅a', a⁆ = ⁅a', a⁆ * g := fun g hg =>
        comm_central_of_q8 hA ha' ha hg
      rcases cenA _ hcA hcen with h | h
      · exfalso
        apply hne
        exact (commutatorElement_eq_one_iff_mul_comm).mp h
      · refine ⟨a', hAW ha', ?_⟩
        rw [commutator_mul_right_of_commute (hcomm a' ha' b hb), h]

end Ext

section M12Core

variable {Y : Type} [Group Y]

theorem mem_zpowers_involution {ζ c : Y} (hζ : ζ ^ 2 = 1) (hc : c ∈ zpowers ζ) : c = 1 ∨ c = ζ := by
  obtain ⟨n, hn⟩ := hc
  beta_reduce at hn
  have h2 : ζ ^ (2 : ℤ) = 1 := by rw [zpow_two]; simpa [pow_two] using hζ
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [← hn, zpow_mul, h2, one_zpow]
  · right
    rw [← hn, zpow_add, zpow_one, zpow_mul, h2, one_zpow, one_mul]

theorem m12_core {W : Subgroup Y} (hWn : W.Normal) {U : Subgroup Y} (hU : U ≤ W)
    (hUsq : ∀ u ∈ U, u ^ 2 = 1) {a : Y} (ha3 : a ^ 3 = 1) {ζ : Y} (hζ1 : ζ ≠ 1) (hζsq : ζ ^ 2 = 1)
    (hζc : ∀ y : Y, y * ζ = ζ * y) (hcomm : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ zpowers ζ)
    (hext : ∀ u ∈ W, u ∉ zpowers ζ → ∃ w ∈ W, ⁅w, u⁆ = ζ)
    (hfix : ∀ w ∈ W, a * w = w * a → w ∈ zpowers ζ) (hex : ∃ u ∈ U, u ∉ zpowers ζ) :
    U ≤ ⁅(⊤ : Subgroup Y), U⁆ := by
  have hNn : (⁅(⊤ : Subgroup Y), U⁆).Normal := normal_commutator_top U
  have hζN : ζ ∈ ⁅(⊤ : Subgroup Y), U⁆ := by
    obtain ⟨u, hu, hnu⟩ := hex
    obtain ⟨w, hw, hwu⟩ := hext u (hU hu) hnu
    rw [← hwu]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top w) hu
  have hzN : zpowers ζ ≤ ⁅(⊤ : Subgroup Y), U⁆ := Subgroup.zpowers_le.mpr hζN
  intro u hu
  by_cases huz : u ∈ zpowers ζ
  · exact hzN huz
  have hu2 : u * u = 1 := by simpa [pow_two] using hUsq u hu
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  obtain ⟨u₁, e₁⟩ : ∃ u₁, a * u * a⁻¹ = u₁ := ⟨_, rfl⟩
  obtain ⟨u₂, e₂⟩ : ∃ u₂, a * u₁ * a⁻¹ = u₂ := ⟨_, rfl⟩
  have ha3' : a * a * a = 1 := by simpa [pow_succ, mul_assoc] using ha3
  have e₃ : a * u₂ * a⁻¹ = u := by
    rw [← e₂, ← e₁]
    calc a * (a * (a * u * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * u * (a * a * a)⁻¹ := by group
      _ = u := by rw [ha3']; group
  have hu₁W : u₁ ∈ W := by rw [← e₁]; exact hWn.conj_mem u (hU hu) a
  have hu₂W : u₂ ∈ W := by rw [← e₂]; exact hWn.conj_mem u₁ hu₁W a
  have hu₁2 : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = a * (u * u) * a⁻¹ := by rw [← e₁]; group
      _ = 1 := by rw [hu2]; group
  have hp : (u * u₁ * u₂) ∈ W := W.mul_mem (W.mul_mem (hU hu) hu₁W) hu₂W
  obtain ⟨p, hpdef⟩ : ∃ p, u * u₁ * u₂ = p := ⟨_, rfl⟩
  rw [hpdef] at hp
  have hap : a * p * a⁻¹ = u⁻¹ * p * u := by
    calc a * p * a⁻¹ = (a * u * a⁻¹) * (a * u₁ * a⁻¹) * (a * u₂ * a⁻¹) := by rw [← hpdef]; group
      _ = u₁ * u₂ * u := by rw [e₁, e₂, e₃]
      _ = u⁻¹ * p * u := by rw [← hpdef, hinv]; calc u₁ * u₂ * u = (u * u) * u₁ * u₂ * u := by rw [hu2]; group
                                                          _ = u * (u * u₁ * u₂) * u := by group
  have hcp : ⁅p⁻¹, u⁻¹⁆ ∈ zpowers ζ := hcomm _ (W.inv_mem hp) _ (W.inv_mem (hU hu))
  have hap2 : a * p * a⁻¹ = p * ⁅p⁻¹, u⁻¹⁆ := by
    rw [hap]; simp only [commutatorElement_def]; group
  have hσζ : a * ζ * a⁻¹ = ζ := by rw [hζc a]; group
  have hc1 : ⁅p⁻¹, u⁻¹⁆ = 1 := by
    rcases mem_zpowers_involution hζsq hcp with h | h
    · exact h
    · exfalso
      rw [h] at hap2
      have h2 : a * (a * p * a⁻¹) * a⁻¹ = p * ζ * ζ := by
        calc a * (a * p * a⁻¹) * a⁻¹ = a * (p * ζ) * a⁻¹ := by rw [hap2]
          _ = (a * p * a⁻¹) * (a * ζ * a⁻¹) := by group
          _ = p * ζ * ζ := by rw [hap2, hσζ]
      have h3 : a * (a * (a * p * a⁻¹) * a⁻¹) * a⁻¹ = p * ζ * ζ * ζ := by
        calc a * (a * (a * p * a⁻¹) * a⁻¹) * a⁻¹ = a * (p * ζ * ζ) * a⁻¹ := by rw [h2]
          _ = (a * (p * ζ) * a⁻¹) * (a * ζ * a⁻¹) := by group
          _ = (a * p * a⁻¹) * (a * ζ * a⁻¹) * (a * ζ * a⁻¹) := by group
          _ = p * ζ * ζ * ζ := by rw [hap2, hσζ]
      have h4 : a * (a * (a * p * a⁻¹) * a⁻¹) * a⁻¹ = p := by
        calc a * (a * (a * p * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * p * (a * a * a)⁻¹ := by group
          _ = p := by rw [ha3']; group
      have h5 : p * (ζ * ζ * ζ) = p * 1 := by
        rw [mul_one, ← mul_assoc, ← mul_assoc, ← h3, h4]
      have h6 : ζ * ζ * ζ = 1 := mul_left_cancel h5
      have hzz : ζ * ζ = 1 := by simpa [pow_two] using hζsq
      rw [hzz, one_mul] at h6
      exact hζ1 h6
  rw [hc1, mul_one] at hap2
  have hpz : p ∈ zpowers ζ := hfix p hp (mul_inv_eq_iff_eq_mul.mp hap2)
  have hn₀ : u₁ * u ∈ ⁅(⊤ : Subgroup Y), U⁆ := by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hu
    simpa [commutatorElement_def, e₁, hinv] using this
  have hu₂ : u₂ = (u₁ * u) * p := by
    rw [← hpdef]
    calc u₂ = (u₁ * u₁) * u₂ := by rw [hu₁2, one_mul]
      _ = u₁ * (u * u) * u₁ * u₂ := by rw [hu2]; group
      _ = u₁ * u * (u * u₁ * u₂) := by group
  have hu₂N : u₂ ∈ ⁅(⊤ : Subgroup Y), U⁆ := by
    rw [hu₂]
    exact Subgroup.mul_mem _ hn₀ (hzN hpz)
  have := hNn.conj_mem u₂ hu₂N a
  rwa [e₃] at this

end M12Core

section M12Glue

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem barOf_zpowers_self (z : G) :
    barOf z (zpowers z) = zpowers (toBar z ⟨z, mem_Cen_self z⟩) := by
  apply le_antisymm
  · rintro _ ⟨⟨c, hcC⟩, hc, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_subgroupOf.mp hc
    refine ⟨n, ?_⟩
    beta_reduce
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    simpa using hn
  · rintro _ ⟨n, rfl⟩
    refine ⟨⟨z, mem_Cen_self z⟩ ^ n, ?_, map_zpow _ _ _⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    exact ⟨n, by simp⟩

theorem Stage2Ctx.m12_res (h : Stage2Ctx G z k S) (hM : Stage1M12 G z S) {U : Subgroup G}
    (hUS : U ≤ S) (h4 : IVK.IsFourSubgroup U) (hnorm : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) :
    U ≤ ⁅Cen z, U⁆ := by
  have hUL : U ≤ LC z := hM.base.four_le U hUS h4 hnorm
  have hUC : U ≤ Cen z := hUL.trans (LC_le_Cen z)
  obtain ⟨U₀, -, -, -, hzU₀, hU₀W, huniq, -⟩ := hM.four_group
  have hUU₀ : U = U₀ := huniq U hUS h4 hnorm
  have hzU : z ∈ U := hUU₀ ▸ hzU₀
  have hUW : U ≤ WC z := hUU₀ ▸ hU₀W
  obtain ⟨A, B, hprod, hAq, hBq, -⟩ := hM.W_shape
  obtain ⟨A', ⟨eA'⟩, -, -, hFst, -, hfixA'⟩ := hM.L_shape
  obtain ⟨ζ, -, -, hζ1, hζsq, -, hcomm, hcen, hext⟩ := q8_central_product hprod hAq hBq
  obtain ⟨zb, hzb⟩ : ∃ zb, zb = toBar z ⟨z, mem_Cen_self z⟩ := ⟨_, rfl⟩
  have hzbc : zb ∈ center (CentralizerBar z) := hzb ▸ toBar_z_mem_center z
  have hzbW : zb ∈ WBar z := by
    have := centralizer_generalizedFitting_le (CentralizerBar z)
      (Subgroup.mem_centralizer_iff.mpr fun y _ => Subgroup.mem_center_iff.mp hzbc y)
    rw [hFst] at this
    exact hzb ▸ this
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  have hzb1 : zb ≠ 1 := by
    intro h1
    have hsq : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ^ 2 = 1 := Subtype.ext hz2
    have := eq_one_of_toBar_eq_one z hsq (hzb ▸ h1)
    have hz1 : z = 1 := congrArg Subtype.val this
    have h2 := h.orderOf_z
    rw [hz1, orderOf_one] at h2
    omega
  have hzbζ : zb = ζ := by
    have := hcen zb hzbW (fun g _ => Subgroup.mem_center_iff.mp hzbc g)
    rcases mem_zpowers_involution hζsq this with h1 | h1
    · exact absurd h1 hzb1
    · exact h1
  have hζc : ∀ y, y * ζ = ζ * y := fun y => hzbζ ▸ Subgroup.mem_center_iff.mp hzbc y
  have hcardA' : Nat.card ↥A' = 3 := by
    rw [Nat.card_congr eA'.toEquiv, Nat.card_eq_fintype_card]
    simp
  obtain ⟨a, haA', hAgen, ha3⟩ := CFSG.GH74.GLS.Stage1.Thm6.Prod.exists_gen_card_three hcardA'
  have hfix : ∀ w ∈ WBar z, a * w = w * a → w ∈ zpowers ζ := by
    intro w hw hcw
    have hall : ∀ a' ∈ A', a' * w = w * a' := by
      intro a' ha'
      rw [hAgen] at ha'
      obtain ⟨n, rfl⟩ := ha'
      exact (((show Commute a w from hcw).zpow_left n)).eq
    have := hfixA' w hw hall
    rw [barOf_zpowers_self, ← hzb, hzbζ] at this
    exact this
  have h4bar := isFour_barOf z hUC h4
  have hUbarW : barOf z U ≤ WBar z := Subgroup.map_mono (Subgroup.comap_mono hUW)
  have hUsq : ∀ u ∈ barOf z U, u ^ 2 = 1 := by
    have : IsElementaryAbelian 2 ↥(barOf z U) := h4bar.1
    intro u hu
    exact elemPow_eq_one_of_isElementaryAbelian u hu
  have hex : ∃ u ∈ barOf z U, u ∉ zpowers ζ := by
    by_contra hcon
    have hle : barOf z U ≤ zpowers ζ := fun u hu => by
      by_contra hu'
      exact hcon ⟨u, hu, hu'⟩
    have := Subgroup.card_le_of_le hle
    rw [h4bar.2, Nat.card_zpowers, orderOf_eq_prime hζsq hζ1] at this
    omega
  have hWn : (WBar z).Normal := by
    rw [← hFst]
    exact CFSG.LocalCores.generalized_fitting_characteristic.2
  have hcore := m12_core hWn hUbarW hUsq ha3 hζ1 hζsq hζc hcomm hext hfix hex
  exact le_commutator_of_barOf_le z hUC (isFour_orderOf h4) (hcore.trans (commutator_top_le_barOf z))

end M12Glue

section G2Three

open Matrix

abbrev SL23 := SpecialLinearGroup (Fin 2) (ZMod 3)

def slThreeC : SL23 := ⟨!![1, 1; 0, 1], by decide⟩

theorem sl23_key : ∀ b : SL23, (∀ g : SL23, g * b ^ 2 = b ^ 2 * g) →
    (∀ g : SL23, g * b = b * g) ∨
      ∃ s : SL23, (∀ g : SL23, g * s = s * g) ∧
        b = s * (slThreeC * ⁅slThreeC, b⁆ * slThreeC⁻¹) := by
  decide

noncomputable def slMapEquiv {F F' : Type} [Field F] [Field F'] (φ : F ≃+* F') :
    SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F' :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map (φ : F →+* F'))
    (SpecialLinearGroup.map (φ.symm : F' →+* F))
    (by ext A i j; simp)
    (by ext A i j; simp)

theorem sl2_three_key {Y : Type} [Group Y] {L : Subgroup Y} (h : HasSL2Model ↥L (fun r => r = 3)) :
    ∃ c ∈ L, ∀ b ∈ L, (∀ g ∈ L, g * b ^ 2 = b ^ 2 * g) →
      (∀ g ∈ L, g * b = b * g) ∨
        ∃ s ∈ L, (∀ g ∈ L, g * s = s * g) ∧ b = s * (c * ⁅c, b⁆ * c⁻¹) := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hq', ZMod.card]
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let Φ : ↥L ≃* SL23 :=
    (e.trans (specialLinearGroupEquivStatedSL 2 F).symm).trans (slMapEquiv φ)
  refine ⟨((Φ.symm slThreeC : ↥L) : Y), (Φ.symm slThreeC).2, ?_⟩
  intro b hb hb2
  have hΦ := sl23_key (Φ ⟨b, hb⟩) (by
    intro g
    obtain ⟨g', rfl⟩ := Φ.surjective g
    have := hb2 g' g'.2
    have h2 : g' * (⟨b, hb⟩ : ↥L) ^ 2 = (⟨b, hb⟩ : ↥L) ^ 2 * g' := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow]
      exact this
    have h3 := congrArg Φ h2
    rwa [map_mul, map_mul, map_pow] at h3)
  rcases hΦ with h1 | ⟨s, hs, hbs⟩
  · left
    intro g hg
    have := h1 (Φ ⟨g, hg⟩)
    have h2 : (⟨g, hg⟩ : ↥L) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨g, hg⟩ :=
      Φ.injective (by rw [map_mul, map_mul]; exact this)
    exact congrArg Subtype.val h2
  · right
    refine ⟨((Φ.symm s : ↥L) : Y), (Φ.symm s).2, ?_, ?_⟩
    · intro g hg
      have := hs (Φ ⟨g, hg⟩)
      have h2 : (⟨g, hg⟩ : ↥L) * Φ.symm s = Φ.symm s * ⟨g, hg⟩ :=
        Φ.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact this)
      exact congrArg Subtype.val h2
    · have h2 : (⟨b, hb⟩ : ↥L) = Φ.symm s * (Φ.symm slThreeC * ⁅Φ.symm slThreeC, ⟨b, hb⟩⁆ *
          (Φ.symm slThreeC)⁻¹) := by
        apply Φ.injective
        rw [map_mul, map_mul, map_mul, map_inv, map_commutatorElement, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply]
        exact hbs
      have := congrArg Subtype.val h2
      simpa [commutatorElement_def] using this

end G2Three

section G2ThreeGlue

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem commutator_mul_of_commute_left {Y : Type} [Group Y] {c a b : Y} (hca : c * a = a * c)
    (hay : a * ⁅c, b⁆ = ⁅c, b⁆ * a) : ⁅c, a * b⁆ = ⁅c, b⁆ := by
  calc ⁅c, a * b⁆ = (c * a) * b * c⁻¹ * b⁻¹ * a⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = a * c * b * c⁻¹ * b⁻¹ * a⁻¹ := by rw [hca]
    _ = a * ⁅c, b⁆ * a⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅c, b⁆ := by rw [hay]; group

theorem Stage1G2.res_three (hg : Stage1G2 G z S) (hnb : ¬ G2Big z S)
    {U : Subgroup G} (hUS : U ≤ S) (h4 : IVK.IsFourSubgroup U)
    (hnorm : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) : U ≤ ⁅Cen z, U⁆ := by
  have hUL : U ≤ LC z := hg.base.four_le U hUS h4 hnorm
  have hUC : U ≤ Cen z := hUL.trans (LC_le_Cen z)
  obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
  have hsh' := hsh
  obtain ⟨hodd₁, hodd₂, hgt₁, hprod, m₁, m₂, -⟩ := hsh
  have hr₂le : r₂ ≤ 3 := by
    by_contra hcon
    exact hnb ⟨r₁, r₂, L₁, L₂, by omega, hsh'⟩
  have hr₂ge : 2 ≤ r₂ := by
    obtain ⟨F, hF, hFin, hq, -⟩ := m₂
    have : 1 < Nat.card F := Finite.one_lt_card
    have hq' : Nat.card F = r₂ := hq
    omega
  have hr₂ : r₂ = 3 := by
    have := Nat.odd_iff.mp hodd₂
    omega
  subst hr₂
  obtain ⟨hq₁, hZ₁, hinv₁⟩ := sl2_model_facts hodd₁ (by omega) m₁
  obtain ⟨hZ₂, hinv₂⟩ := sl2_model_center_inv hodd₂ m₂
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have h4bar := isFour_barOf z hUC h4
  have hUle : barOf z U ≤ L₁ ⊔ L₂ := by rw [hsup]; exact barOf_le_LBar hUL
  have hL₁ : L₁ ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ :=
    le_commutator_top_of_two_comps hq₁ hcomm
      (fun a ha hc => central_mem_of_card_inf hcomm hZ₁ hcard ha hc) hinv₂ h4bar hUle
  obtain ⟨c₀, hc₀, hkey⟩ := sl2_three_key m₂
  have hNn := normal_commutator_top (barOf z U)
  have hUsq : ∀ u ∈ barOf z U, u ^ 2 = 1 := by
    have : IsElementaryAbelian 2 ↥(barOf z U) := h4bar.1
    intro u hu
    exact elemPow_eq_one_of_isElementaryAbelian u hu
  have hUN : barOf z U ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hUle hu)
    have hsq : a ^ 2 * b ^ 2 = 1 := by
      rw [← (show Commute a b from hcomm a ha b hb).mul_pow]
      exact hUsq _ hu
    have hb2 : b ^ 2 = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hsq
    have hb2L₁ : b ^ 2 ∈ L₁ := by rw [hb2]; exact L₁.inv_mem (L₁.pow_mem ha 2)
    have hb2cen : ∀ g ∈ L₂, g * b ^ 2 = b ^ 2 * g := fun g hg => (hcomm (b ^ 2) hb2L₁ g hg).symm
    have hinf : Nat.card ↥(L₂ ⊓ L₁) = 2 := by rwa [inf_comm]
    rcases hkey b hb hb2cen with hcen | ⟨s, hsL, hscen, hbs⟩
    · have hbL₁ : b ∈ L₁ := central_mem_of_card_inf hcomm' hZ₂ hinf hb hcen
      exact hL₁ (L₁.mul_mem ha hbL₁)
    · have hsL₁ : s ∈ L₁ := central_mem_of_card_inf hcomm' hZ₂ hinf hsL hscen
      have hcb : ⁅c₀, b⁆ ∈ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ := by
        have hcu : ⁅c₀, a * b⁆ ∈ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top c₀) hu
        have hy : ⁅c₀, b⁆ ∈ L₂ := by
          simp only [commutatorElement_def]
          exact L₂.mul_mem (L₂.mul_mem (L₂.mul_mem hc₀ hb) (L₂.inv_mem hc₀)) (L₂.inv_mem hb)
        rwa [commutator_mul_of_commute_left (hcomm a ha c₀ hc₀).symm (hcomm a ha _ hy)] at hcu
      have hconj := hNn.conj_mem _ hcb c₀
      have hbN : b ∈ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ := by
        rw [hbs]
        exact Subgroup.mul_mem _ (hL₁ hsL₁) hconj
      exact Subgroup.mul_mem _ (hL₁ ha) hbN
  exact le_commutator_of_barOf_le z hUC (isFour_orderOf h4) (hUN.trans (commutator_top_le_barOf z))

end G2ThreeGlue

section Final

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem Stage2Ctx.lemma23e (h : Stage2Ctx G z k S) : Lemma23e z k S := by
  intro U hUS h4 hnorm
  have hUL : U ≤ LC z := h.data.base.four_le U hUS h4 hnorm
  by_cases hr : k = Kind.m12 ∨ (k = Kind.g2 ∧ ¬ G2Big z S)
  · refine ⟨le_inf hUL ?_, fun hk hg => ?_⟩
    · rcases hr with hm | ⟨hg2, hnb⟩
      · subst hm
        have hd := h.data
        cases hd with
        | m12 hM => exact h.m12_res hM hUS h4 hnorm
      · subst hg2
        have hd := h.data
        cases hd with
        | g2 hg => exact hg.res_three hnb hUS h4 hnorm
    · exfalso
      rcases hr with hm | ⟨hg2, hnb⟩
      · exact hk hm
      · exact hnb (hg hg2)
  · obtain ⟨h1, h2⟩ := lemma23e_of_LBar_le h hUS h4 hnorm (h.LBar_le_commutator hr hUS h4 hnorm)
    exact ⟨h1, fun _ _ => h2⟩

end Final

end CFSG.GH74.GLS.Stage2.Local
