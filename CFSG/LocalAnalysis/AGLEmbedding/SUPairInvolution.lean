module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbedding.SUPair

open Subgroup

variable {Y : Type} [Group Y]

structure Heis27 (A Z : Subgroup Y) : Prop where
  card : Nat.card A = 27
  le : Z ≤ A
  card_center : Nat.card Z = 3
  central : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z
  comm_mem : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ Z
  center_le : ∀ c ∈ A, (∀ a ∈ A, c * a = a * c) → c ∈ Z
  cube : ∀ a ∈ A, a ^ 3 = 1
  nonabelian : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a

variable {A Z : Subgroup Y}

theorem eq_one_of_cube_of_sq {c : Y} (h3 : c ^ 3 = 1) (h2 : c ^ 2 = 1) : c = 1 := by
  calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem eq_of_conj_eq_mul (hA : Heis27 A Z) {u x c : Y} (hu2 : u ^ 2 = 1)
    (huZ : ∀ z ∈ Z, u * z = z * u) (hc : c ∈ Z) (h : u * x * u⁻¹ = x * c) : u * x * u⁻¹ = x := by
  have h2 : u ^ 2 * x * (u ^ 2)⁻¹ = x * c * c := by
    calc u ^ 2 * x * (u ^ 2)⁻¹ = u * (u * x * u⁻¹) * u⁻¹ := by rw [sq]; group
      _ = u * (x * c) * u⁻¹ := by rw [h]
      _ = (u * x * u⁻¹) * (u * c * u⁻¹) := by group
      _ = x * c * c := by rw [h, huZ c hc]; group
  rw [hu2] at h2
  have hcc : c ^ 2 = 1 := by
    have : x * c * c = x := by rw [← h2]; group
    rw [sq]
    simpa [mul_assoc] using this
  have hc1 : c = 1 := eq_one_of_cube_of_sq (hA.cube c (hA.le hc)) hcc
  rw [h, hc1, mul_one]

theorem mul_comm_mod (hA : Heis27 A Z) {x y : Y} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ c ∈ Z, y * x = x * y * c := by
  refine ⟨(x * y)⁻¹ * (y * x), ?_, by group⟩
  have := hA.comm_mem _ (inv_mem hy) _ (inv_mem hx)
  have heq : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by group
  rw [heq]
  exact this

theorem centralizes_or_le_commutator [Finite Y] (hA : Heis27 A Z) {u : Y} (hu2 : u ^ 2 = 1)
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A) (huZ : ∀ z ∈ Z, u * z = z * u) :
    (∀ a ∈ A, u * a = a * u) ∨ A ≤ ⁅A, zpowers u⁆ := by
  classical
  have huinv : u⁻¹ = u := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hu2]
  set w : Y → Y := fun a => a * (u * a * u⁻¹) with hw
  set v : Y → Y := fun a => a⁻¹ * (u * a * u⁻¹) with hv
  have hwA : ∀ a ∈ A, w a ∈ A := fun a ha => A.mul_mem ha (huA a ha)
  have hvA : ∀ a ∈ A, v a ∈ A := fun a ha => A.mul_mem (A.inv_mem ha) (huA a ha)
  have hsq : ∀ a, a ^ 2 = w a * (v a)⁻¹ := fun a => by simp only [hw, hv, sq]; group
  have hconj2 : ∀ g, u * (u * g * u⁻¹) * u⁻¹ = g := by
    intro g
    rw [show u * (u * g * u⁻¹) * u⁻¹ = u ^ 2 * g * (u ^ 2)⁻¹ by rw [sq]; group, hu2]
    group
  have hvinv : ∀ a, u * v a * u⁻¹ = (v a)⁻¹ := by
    intro a
    simp only [hv]
    calc u * (a⁻¹ * (u * a * u⁻¹)) * u⁻¹ = u * a⁻¹ * u⁻¹ * (u * (u * a * u⁻¹) * u⁻¹) := by
          group
      _ = u * a⁻¹ * u⁻¹ * a := by rw [hconj2]
      _ = (a⁻¹ * (u * a * u⁻¹))⁻¹ := by group
  have hwfix : ∀ a ∈ A, u * w a * u⁻¹ = w a := by
    intro a ha
    obtain ⟨c, hc, hce⟩ := mul_comm_mod hA ha (huA a ha)
    refine eq_of_conj_eq_mul hA hu2 huZ hc ?_
    calc u * w a * u⁻¹ = (u * a * u⁻¹) * (u * (u * a * u⁻¹) * u⁻¹) := by simp only [hw]; group
      _ = (u * a * u⁻¹) * a := by rw [hconj2]
      _ = w a * c := by simp only [hw]; exact hce
  have hvcomm : ∀ a ∈ A, v a ∈ ⁅A, zpowers u⁆ := by
    intro a ha
    have := commutator_mem_commutator (inv_mem ha) (mem_zpowers u)
    rw [commutatorElement_def, inv_inv] at this
    simpa [hv, mul_assoc] using this
  have hZnt : ∃ z ∈ Z, z ≠ 1 := by
    by_contra h
    push Not at h
    have : Z = ⊥ := (eq_bot_iff_forall Z).mpr h
    have := hA.card_center
    rw [‹Z = ⊥›, card_bot] at this
    omega
  by_cases hV : ∀ a ∈ A, v a ∈ Z
  ·
    left
    intro a ha
    have h1 : u * a * u⁻¹ = a := by
      refine eq_of_conj_eq_mul hA hu2 huZ (hV a ha) ?_
      simp only [hv]
      group
    calc u * a = u * a * u⁻¹ * u := by group
      _ = a * u := by rw [h1]
  by_cases hW : ∀ a ∈ A, w a ∈ Z
  ·
    right
    push Not at hV
    set C := ⁅A, zpowers u⁆ with hC
    have hCA : C ≤ A := by
      rw [hC, commutator_le]
      intro a ha g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      rw [commutatorElement_def]
      have hk : u ^ k * a⁻¹ * (u ^ k)⁻¹ ∈ A := by
        have hk' : ∀ n : ℕ, ∀ b ∈ A, u ^ n * b * (u ^ n)⁻¹ ∈ A := by
          intro n
          induction n with
          | zero => intro b hb; simpa using hb
          | succ n ih =>
            intro b hb
            have := huA _ (ih b hb)
            rw [pow_succ']
            simpa [mul_assoc] using this
        rcases k with n | n
        · simpa using hk' n _ (inv_mem ha)
        · have h2 : u ^ (Int.negSucc n) = u ^ (n + 1) := by
            rw [zpow_negSucc, ← inv_pow, huinv]
          rw [h2]
          exact hk' (n + 1) _ (inv_mem ha)
      have := A.mul_mem ha hk
      simpa [mul_assoc] using this
    have hdecomp : ∀ a ∈ A, ∃ z ∈ Z, ∃ c ∈ C, a = z * c := by
      intro a ha
      have h4 : a = (a ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hA.cube a ha, one_mul]
      have hwz := hW a ha
      refine ⟨w a * w a, Z.mul_mem hwz hwz, (v a)⁻¹ * (v a)⁻¹,
        C.mul_mem (C.inv_mem (hvcomm a ha)) (C.inv_mem (hvcomm a ha)), ?_⟩
      have hc : ∀ g ∈ A, w a * g = g * w a := fun g hg => hA.central _ hwz g hg
      have := hc _ (A.inv_mem (hvA a ha))
      calc a = (a ^ 2) ^ 2 := h4
        _ = (w a * (v a)⁻¹) ^ 2 := by rw [← hsq a]
        _ = w a * ((v a)⁻¹ * w a) * (v a)⁻¹ := by rw [sq]; group
        _ = w a * (w a * (v a)⁻¹) * (v a)⁻¹ := by rw [← this]
        _ = w a * w a * ((v a)⁻¹ * (v a)⁻¹) := by group
    have hZC : Z ≤ C := by
      by_contra hn
      apply absurd hA.nonabelian
      push Not
      intro a ha b hb
      obtain ⟨z₁, hz₁, c₁, hc₁, rfl⟩ := hdecomp a ha
      obtain ⟨z₂, hz₂, c₂, hc₂, rfl⟩ := hdecomp b hb
      have hcm : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ Z := hA.comm_mem _ (hCA hc₁) _ (hCA hc₂)
      have hcC : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ C :=
        C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)
      have h1 : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ = 1 := by
        by_contra hne
        apply hn
        intro z hz
        have hzp : Nat.card Z = 3 := hA.card_center
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hzz : zpowers (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) = Z := by
          have hle : zpowers (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) ≤ Z := zpowers_le.mpr hcm
          refine eq_of_le_of_card_ge hle ?_
          rw [hzp, Nat.card_zpowers]
          have hdvd : orderOf (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) ∣ 3 :=
            orderOf_dvd_of_pow_eq_one (hA.cube _ (hA.le hcm))
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hne
          · rw [h]
        rw [← hzz] at hz
        exact (zpowers_le.mpr hcC) hz
      have hcc : c₁ * c₂ = c₂ * c₁ := by
        calc c₁ * c₂ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ * (c₂ * c₁) := by group
          _ = c₂ * c₁ := by rw [h1, one_mul]
      have e1 := hA.central z₁ hz₁ _ (hCA hc₂)
      have e2 := hA.central z₂ hz₂ _ (hCA hc₁)
      have e3 := hA.central z₁ hz₁ _ (hA.le hz₂)
      calc z₁ * c₁ * (z₂ * c₂) = z₁ * (c₁ * z₂) * c₂ := by group
        _ = z₁ * (z₂ * c₁) * c₂ := by rw [← e2]
        _ = z₁ * z₂ * (c₁ * c₂) := by group
        _ = z₂ * z₁ * (c₂ * c₁) := by rw [e3, hcc]
        _ = z₂ * (z₁ * c₂) * c₁ := by group
        _ = z₂ * (c₂ * z₁) * c₁ := by rw [e1]
        _ = z₂ * c₂ * (z₁ * c₁) := by group
    intro a ha
    obtain ⟨z, hz, c, hc, rfl⟩ := hdecomp a ha
    exact C.mul_mem (hZC hz) hc
  ·
    exfalso
    push Not at hV hW
    obtain ⟨a, ha, hva⟩ := hV
    obtain ⟨b, hb, hwb⟩ := hW
    set x := w b with hx
    have hxA : x ∈ A := hwA b hb
    have hxfix : u * x * u⁻¹ = x := hwfix b hb
    set B : Subgroup Y := A ⊓ centralizer {u} with hB
    have hmemB : ∀ g ∈ A, u * g * u⁻¹ = g → g ∈ B := by
      intro g hg hfix
      refine ⟨hg, mem_centralizer_singleton_iff.mpr ?_⟩
      exact (by calc u * g = u * g * u⁻¹ * u := by group
        _ = g * u := by rw [hfix] : u * g = g * u).symm
    have hBA : B ≤ A := inf_le_left
    have hZB : Z ≤ B := fun z hz => ⟨hA.le hz, mem_centralizer_singleton_iff.mpr (huZ z hz).symm⟩
    have hxB : x ∈ B := hmemB x hxA hxfix
    have haB : a ∉ B := by
      intro haB
      have : u * a * u⁻¹ = a := by
        have := mem_centralizer_singleton_iff.mp haB.2
        calc u * a * u⁻¹ = a * u * u⁻¹ := by rw [this]
          _ = a := by group
      apply hva
      simp only [hv]
      rw [this, inv_mul_cancel]
      exact one_mem Z
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hBcard : Nat.card B = 9 := by
      have hdvd : Nat.card B ∣ 27 := hA.card ▸ card_dvd_of_le hBA
      have h3 : 3 ∣ Nat.card B := hA.card_center ▸ card_dvd_of_le hZB
      have hne27 : Nat.card B ≠ 27 := by
        intro h27
        exact haB ((eq_of_le_of_card_ge hBA (by rw [h27, hA.card])) ▸ ha)
      have hne3 : Nat.card B ≠ 3 := by
        intro h3'
        have hZBe : Z = B := eq_of_le_of_card_ge hZB (by rw [h3', hA.card_center])
        exact hwb (hZBe ▸ hxB)
      have : Nat.card B ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h
      · rw [h] at h3; norm_num at h3
      · exact absurd h hne3
      · exact h
      · exact absurd h hne27
    have hBab : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := by
      intro g hg h hh
      have hcomm := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := ↥B)
        (by rw [hBcard]; norm_num)
      have := hcomm ⟨g, hg⟩ ⟨h, hh⟩
      simpa using congrArg Subtype.val this
    have hxinv : ∀ y ∈ A, u * y * u⁻¹ = y⁻¹ → x * y = y * x := by
      intro y hy hyinv
      set c := x * y * x⁻¹ * y⁻¹ with hc
      have hcZ : c ∈ Z := hA.comm_mem _ hxA _ hy
      have huc : u * c * u⁻¹ = c⁻¹ := by
        have e : u * c * u⁻¹ = x * y⁻¹ * x⁻¹ * y := by
          calc u * c * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) * (u * x * u⁻¹)⁻¹ *
                (u * y * u⁻¹)⁻¹ := by rw [hc]; group
            _ = x * y⁻¹ * x⁻¹ * y := by rw [hxfix, hyinv, inv_inv]
        rw [e]
        have hcy := hA.central c hcZ y hy
        have hxy : x * y * x⁻¹ = c * y := by rw [hc]; group
        calc x * y⁻¹ * x⁻¹ * y = (x * y * x⁻¹)⁻¹ * y := by group
          _ = (c * y)⁻¹ * y := by rw [hxy]
          _ = (y * c)⁻¹ * y := by rw [hcy]
          _ = c⁻¹ := by group
      have hc2 : c ^ 2 = 1 := by
        have h1 : u * c * u⁻¹ = c := by
          rw [huZ c hcZ]
          group
        rw [huc] at h1
        rw [sq]
        nth_rewrite 2 [← h1]
        exact mul_inv_cancel c
      have hc1 : c = 1 := eq_one_of_cube_of_sq (hA.cube c (hA.le hcZ)) hc2
      calc x * y = c * (y * x) := by rw [hc]; group
        _ = y * x := by rw [hc1, one_mul]
    have hxcen : ∀ g ∈ A, x * g = g * x := by
      intro g hg
      have h1 : x * w g = w g * x := hBab x hxB (w g) (hmemB _ (hwA g hg) (hwfix g hg))
      have h2 : x * v g = v g * x := hxinv (v g) (hvA g hg) (hvinv g)
      have h3 : x * g ^ 2 = g ^ 2 * x := by
        rw [hsq g]
        have h2' : x * (v g)⁻¹ = (v g)⁻¹ * x := by
          calc x * (v g)⁻¹ = (v g)⁻¹ * (v g * x) * (v g)⁻¹ := by group
            _ = (v g)⁻¹ * (x * v g) * (v g)⁻¹ := by rw [h2]
            _ = (v g)⁻¹ * x := by group
        calc x * (w g * (v g)⁻¹) = (x * w g) * (v g)⁻¹ := by group
          _ = w g * (x * (v g)⁻¹) := by rw [h1]; group
          _ = w g * (v g)⁻¹ * x := by rw [h2']; group
      have h4 : g = (g ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hA.cube g hg, one_mul]
      rw [h4]
      exact ((Commute.pow_right (h3 : Commute x (g ^ 2)) 2)).eq
    exact hwb (hA.center_le x hxA hxcen)

end CFSG.AGLEmbedding.SUPair
