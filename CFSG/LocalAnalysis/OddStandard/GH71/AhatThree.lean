module

public import CFSG.LocalAnalysis.OddStandard.GH71.AhatFix
public import CFSG.LocalAnalysis.OddStandard.GH71.AhatU

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

theorem mem_iff_of_shape {F : Set (Fin 11)}
    (hF : (∀ x : Fin 11, x.val < 8 → (x ∈ F ↔ (0 : Fin 11) ∈ F)) ∧
      ((9 : Fin 11) ∈ F ↔ (8 : Fin 11) ∈ F)) (x : Fin 11) :
    x ∈ F ↔ (x.val < 8 ∧ (0 : Fin 11) ∈ F) ∨ ((x = 8 ∨ x = 9) ∧ (8 : Fin 11) ∈ F) ∨
      (x = 10 ∧ (10 : Fin 11) ∈ F) := by
  by_cases hx : x.val < 8
  · have h8 : ¬ (x = 8 ∨ x = 9) := by
      rintro (rfl | rfl) <;> exact absurd hx (by decide)
    have h10 : x ≠ 10 := by
      rintro rfl
      exact absurd hx (by decide)
    rw [hF.1 x hx]
    simp only [hx, h8, h10, true_and, false_and, or_false]
  · rcases (by decide : ∀ y : Fin 11, ¬ y.val < 8 → y = 8 ∨ y = 9 ∨ y = 10) x hx with
      rfl | rfl | rfl
    · simp only [hx, false_and, true_or, true_and, false_or]
      exact ⟨fun h => Or.inl h, fun h => h.elim id fun h' => absurd h'.1 (by decide)⟩
    · simp only [hx, false_and, or_true, true_and, false_or, hF.2]
      exact ⟨fun h => Or.inl h, fun h => h.elim id fun h' => absurd h'.1 (by decide)⟩
    · simp only [hx, false_and, false_or, true_and]
      exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd h'.1 (by decide)) id⟩

theorem mod3_of_shape {F : Set (Fin 11)}
    (hF : (∀ x : Fin 11, x.val < 8 → (x ∈ F ↔ (0 : Fin 11) ∈ F)) ∧
      ((9 : Fin 11) ∈ F ↔ (8 : Fin 11) ∈ F)) (hmod : Nat.card F ≡ 2 [MOD 3]) :
    (0 : Fin 11) ∈ F ∨ ((8 : Fin 11) ∈ F ∧ (10 : Fin 11) ∉ F) := by
  by_cases a : (0 : Fin 11) ∈ F
  · exact Or.inl a
  right
  have hm := mem_iff_of_shape hF
  by_cases b : (8 : Fin 11) ∈ F <;> by_cases c : (10 : Fin 11) ∈ F
  · rw [card_eq_of_iff (fun x : Fin 11 => x = 8 ∨ x = 9 ∨ x = 10)
      (fun x => by rw [hm x]; simp [a, b, c, or_assoc])] at hmod
    exact absurd hmod (by decide)
  · exact ⟨b, c⟩
  · rw [card_eq_of_iff (fun x : Fin 11 => x = 10) (fun x => by rw [hm x]; simp [a, b, c])] at hmod
    exact absurd hmod (by decide)
  · rw [card_eq_of_iff (fun _ : Fin 11 => False) (fun x => by rw [hm x]; simp [a, b, c])] at hmod
    exact absurd hmod (by decide)

theorem fix_of_three {Q : Subgroup (Perm (Fin 11))} (hQ : IsPGroup 3 Q)
    (hN : ∀ p ∈ P0 11, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q) :
    ∀ q ∈ Q, ∀ x : Fin 11, x.val < 8 → q x = x := by
  have hN' : ∀ p ∈ P0 11, ∀ q ∈ Q, p⁻¹ * q * p ∈ Q := fun p hp q hq => by
    simpa using hN p⁻¹ (inv_mem hp) q hq
  have hF := shape (F := fixS Q) (fun k x hx => fixS_apply (hN' _ (xo_mem k)) hx)
    (fun x hx => fixS_apply (hN' _ g1_mem) hx)
  suffices h0 : (0 : Fin 11) ∈ fixS Q from fun q hq x hx => (hF.1 x hx).2 h0 q hq
  by_contra h0
  obtain ⟨h8, -⟩ := (mod3_of_shape hF (card_fixS_modEq hQ)).resolve_left h0
  have h9 : (9 : Fin 11) ∈ fixS Q := hF.2.2 h8
  set Q₁₀ : Subgroup (Perm (Fin 11)) := Q ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)
  have hQ₁₀ : IsPGroup 3 Q₁₀ := hQ.to_le inf_le_left
  have hN₁₀ : ∀ p ∈ P0 11, p 10 = 10 → ∀ q ∈ Q₁₀, p⁻¹ * q * p ∈ Q₁₀ := by
    intro p hp hp10 q hq
    refine ⟨hN' p hp q hq.1, ?_⟩
    have hq10 : q 10 = 10 := hq.2
    have hpi : p⁻¹ 10 = 10 := by rw [Perm.inv_eq_iff_eq, hp10]
    show (p⁻¹ * q * p) 10 = 10
    simp only [Perm.mul_apply, hp10, hq10, hpi]
  have hF₁₀ := shape (F := fixS Q₁₀)
    (fun k x hx => fixS_apply (hN₁₀ _ (xo_mem k) (by revert k; decide)) hx)
    (fun x hx => fixS_apply (hN₁₀ _ g1_mem (by decide)) hx)
  have h8' : (8 : Fin 11) ∈ fixS Q₁₀ := fun q hq => h8 q hq.1
  have h10' : (10 : Fin 11) ∈ fixS Q₁₀ := fun q hq => hq.2
  have h0' : (0 : Fin 11) ∈ fixS Q₁₀ := by
    rcases mod3_of_shape hF₁₀ (card_fixS_modEq hQ₁₀) with h | ⟨-, h⟩
    · exact h
    · exact absurd h10' h
  have hone : ∀ q ∈ Q₁₀, q = 1 := fun q hq => Equiv.ext fun x => by
    have hx : x ∈ fixS Q₁₀ := by
      rw [mem_iff_of_shape hF₁₀ x]
      rcases (by decide : ∀ y : Fin 11, y.val < 8 ∨ y = 8 ∨ y = 9 ∨ y = 10) x with
        h | h | h | h
      · exact Or.inl ⟨h, h0'⟩
      · exact Or.inr (Or.inl ⟨Or.inl h, h8'⟩)
      · exact Or.inr (Or.inl ⟨Or.inr h, h8'⟩)
      · exact Or.inr (Or.inr ⟨h, h10'⟩)
    exact hx q hq
  have hcen : ∀ e ∈ P0 11, (∀ y : Fin 11, e y = y → y = 8 ∨ y = 9 ∨ y = 10) → e 10 = 10 →
      ∀ q ∈ Q, q * e = e * q → q = 1 := by
    intro e he hfix he10 q hq hqe
    have hq10 : e (q 10) = q 10 := by rw [apply_comm hqe.symm 10, he10]
    refine hone q ⟨hq, ?_⟩
    show q 10 = 10
    rcases hfix _ hq10 with h | h | h
    · exact absurd (q.injective (h.trans (h8 q hq).symm)) (by decide)
    · exact absurd (q.injective (h.trans (h9 q hq).symm)) (by decide)
    · exact h
  have hinv : ∀ e ∈ P0 11, e * e = 1 → (∀ y : Fin 11, e y = y → y = 8 ∨ y = 9 ∨ y = 10) →
      e 10 = 10 → ∀ q ∈ Q, e * q * e⁻¹ = q⁻¹ := fun e he hee hfix he10 =>
    conj_eq_inv_of_fpf hee (fun q hq => hN e he q hq) fun q hq h =>
      hcen e he hfix he10 q hq (mul_inv_eq_iff_eq_mul.1 h).symm
  apply h0
  intro q hq
  have i1 := hinv u0 u0_mem (by decide) (by decide) (by decide) q hq
  have i2 := hinv g3 g3_mem (by decide) (by decide) (by decide) q hq
  have hc : (u0 * g3) * q * (u0 * g3)⁻¹ = q := by
    calc (u0 * g3) * q * (u0 * g3)⁻¹ = u0 * (g3 * q * g3⁻¹) * u0⁻¹ := by group
      _ = (u0 * q * u0⁻¹)⁻¹ := by rw [i2]; group
      _ = q := by rw [i1, inv_inv]
  rw [hcen (u0 * g3) (mul_mem u0_mem g3_mem) (by decide) (by decide) q hq
    (mul_inv_eq_iff_eq_mul.1 hc).symm]
  rfl

variable {K : Type} [Group K]

theorem le_zpowers_x0 (C : CoverSetup 11 K) {S : Subgroup K} (hSP : S = (P0 11).comap C.ρ)
    {x₀ : K} (hx₀ : C.ρ x₀ = t3) (h3 : orderOf x₀ = 3) {W : Subgroup K} (hW : IsPGroup 3 W)
    (hWS : S ≤ normalizer (W : Set K)) : W ≤ zpowers x₀ := by
  have hN : ∀ p ∈ P0 11, ∀ q ∈ W.map C.ρ, p * q * p⁻¹ ∈ W.map C.ρ := by
    intro p hp q hq
    obtain ⟨s, hs, rfl⟩ := exists_lift_mem C hSP hp
    obtain ⟨w, hw, rfl⟩ := hq
    exact ⟨s * w * s⁻¹, (mem_normalizer_iff.1 (hWS hs) w).1 hw, by simp only [map_mul, map_inv]⟩
  intro w hw
  refine mem_zpowers_x0 C hx₀ h3 (mem_zpowers_t3 (C.sign_ρ w)
    (fix_of_three (hW.map C.ρ) hN (C.ρ w) ⟨w, hw, rfl⟩)) ?_
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have hk' : w ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hk')

theorem eq_zpowers_x0 [Finite K] (C : CoverSetup 11 K) {S : Subgroup K}
    (hSP : S = (P0 11).comap C.ρ) {x₀ : K} (hx₀ : C.ρ x₀ = t3) (h3 : orderOf x₀ = 3)
    {X : Subgroup K} (hX : Nat.card X = 3) (hXS : S ≤ normalizer (X : Set K)) :
    X = zpowers x₀ :=
  Subgroup.eq_of_le_of_card_ge
    (le_zpowers_x0 C hSP hx₀ h3 (IsPGroup.of_card (n := 1) (by rw [hX, pow_one])) hXS)
    (by rw [Nat.card_zpowers, h3, hX])

theorem exists_std [Finite K] {S : Subgroup K} (hK : IsDoubleCoverOfAlt K 11) (hS : IsPGroup 2 S)
    (hc : Nat.card S = 2 ^ 8) : ∃ (C : CoverSetup 11 K) (x₀ : K),
      S = (P0 11).comap C.ρ ∧ C.ρ x₀ = t3 ∧ orderOf x₀ = 3 := by
  obtain ⟨C, hSP⟩ := exists_frame hK hS hc
  obtain ⟨x₀, hx₀, h3⟩ := exists_x0 C
  exact ⟨C, x₀, hSP, hx₀, h3⟩

theorem specB1 : SpecB1 := by
  intro K _ _ S hK hS hc
  obtain ⟨C, x₀, hSP, hx₀, h3⟩ := exists_std hK hS hc
  exact ⟨zpowers x₀, by rw [Nat.card_zpowers, h3],
    fun s hs => mem_normalizer_x0 C hx₀ h3 (comm_u0_of_mem (rho_mem C hSP hs)),
    fun W hW hWS => le_zpowers_x0 C hSP hx₀ h3 hW hWS⟩

end CFSG.OddStandard.GH71.AhatB
