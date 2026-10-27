module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitTenCore

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type} [CommGroup V]

section Chain

theorem card_eq_card_fixV_mul_sq_of_conj (hV : ∀ v : V, v ^ 2 = 1) {z x g : MulAut V}
    (hz3 : z ^ 3 = 1) (hx3 : x ^ 3 = 1) (hzx : z * x = x * z) (hz1 : z ≠ 1) (hx1 : x ≠ 1)
    (hxf : fixV (Subgroup.zpowers x) = ⊥) (hgz : g * z * g⁻¹ = z) (hgx : g * x * g⁻¹ = x⁻¹) :
    Nat.card V = Nat.card (fixV (Subgroup.zpowers z)) *
      Nat.card (fixV (Subgroup.zpowers (z * x))) ^ 2 := by
  have hy := notMem_zpowers_of_conj hx3 hx1 hgz hgx
  have h := card_eq_card_fixV_mul_card_fixV hV hz3 hx3 hzx hz1 hy hxf
  have hconj : g * (z * x) * g⁻¹ = z * x ^ 2 := by
    have hinv : x⁻¹ = x ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx3]
    calc g * (z * x) * g⁻¹ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group
      _ = z * x ^ 2 := by rw [hgz, hgx, hinv]
  rw [← hconj, card_fixV_zpowers_conj] at h
  rw [h, pow_two, mul_assoc]

theorem mul_pow_three_eq_one_of_commute {z x : MulAut V} (hz3 : z ^ 3 = 1) (hx3 : x ^ 3 = 1)
    (hzx : z * x = x * z) : (z * x) ^ 3 = 1 := by
  rw [(show Commute z x from hzx).mul_pow, hz3, hx3, one_mul]

theorem mul_ne_one_of_conj {z x g : MulAut V} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hgz : g * z * g⁻¹ = z) (hgx : g * x * g⁻¹ = x⁻¹) : z * x ≠ 1 := by
  intro h
  apply notMem_zpowers_of_conj hx3 hx1 hgz hgx
  rw [show x = z⁻¹ from eq_inv_of_mul_eq_one_right h]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z)

variable [Finite V]

omit [CommGroup V] in
theorem exists_card_subgroup_eq_two_pow {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (S : Subgroup V) : ∃ i, Nat.card S = 2 ^ i := by
  have hdvd : Nat.card S ∣ 2 ^ rk V := by
    rw [← card_eq_two_pow_rk hV]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨i, hi⟩

theorem exists_card_fixV_eq_four_pow (hV : ∀ v : V, v ^ 2 = 1) {x z : MulAut V}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxf : fixV (Subgroup.zpowers x) = ⊥)
    (hxz : x * z = z * x) : ∃ k, Nat.card (fixV (Subgroup.zpowers z)) = 2 ^ (2 * k) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
  have hst : Subgroup.zpowers x ≤ stabSub (fixV (Subgroup.zpowers z)) := by
    refine B1.le_stabSub_of_invariant fun k hk w hw => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [mem_fixV_zpowers_iff] at hw ⊢
    have hcomm : Commute (x ^ j) z := (show Commute x z from hxz).zpow_left j
    have h1 : (x ^ j) (z w) = z ((x ^ j) w) := congrArg (fun φ : MulAut V => φ w) hcomm.eq
    rw [hw] at h1
    exact h1.symm
  have hmod := card_modEq_card_inf_fixV hP3 hst
  rw [hxf, inf_bot_eq, Subgroup.card_bot] at hmod
  obtain ⟨i, hi⟩ := exists_card_subgroup_eq_two_pow hV (fixV (Subgroup.zpowers z))
  have hev : Even i := Proving.two_pow_mod_three_even i (by rw [← hi]; exact hmod)
  obtain ⟨k, rfl⟩ := hev
  exact ⟨k, by rw [hi, two_mul]⟩

theorem one_lt_card_of_mulAut_ne_one {x : MulAut V} (hx : x ≠ 1) : 1 < Nat.card V := by
  by_contra hle
  have : Subsingleton V := (Finite.card_le_one_iff_subsingleton).1 (by omega)
  exact hx (MulEquiv.ext fun v => Subsingleton.elim _ _)

theorem exp_eq_of_card_eq {D a b : ℕ} (h : 2 ^ D = 2 ^ a * (2 ^ b) ^ 2) : D = a + 2 * b := by
  rw [← pow_mul, ← pow_add, mul_comm b 2] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem two_pow_sixteen_le_card_of_four (hV : ∀ v : V, v ^ 2 = 1)
    {x₁ x₂ x₃ x₄ g₂ g₃ g₄ : MulAut V} (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1) (h₃ : x₃ ^ 3 = 1)
    (h₄ : x₄ ^ 3 = 1) (c₁₂ : x₁ * x₂ = x₂ * x₁) (c₁₃ : x₁ * x₃ = x₃ * x₁)
    (c₁₄ : x₁ * x₄ = x₄ * x₁) (c₂₃ : x₂ * x₃ = x₃ * x₂) (c₂₄ : x₂ * x₄ = x₄ * x₂)
    (c₃₄ : x₃ * x₄ = x₄ * x₃) (f₁ : fixV (Subgroup.zpowers x₁) = ⊥)
    (f₂ : fixV (Subgroup.zpowers x₂) = ⊥) (f₃ : fixV (Subgroup.zpowers x₃) = ⊥)
    (f₄ : fixV (Subgroup.zpowers x₄) = ⊥) (hx₁ : x₁ ≠ 1)
    (g₂₁ : g₂ * x₁ * g₂⁻¹ = x₁) (g₂₂ : g₂ * x₂ * g₂⁻¹ = x₂⁻¹)
    (g₃₁ : g₃ * (x₁ * x₂) * g₃⁻¹ = x₁ * x₂) (g₃₃ : g₃ * x₃ * g₃⁻¹ = x₃⁻¹)
    (g₄₁ : g₄ * (x₁ * x₂ * x₃) * g₄⁻¹ = x₁ * x₂ * x₃) (g₄₄ : g₄ * x₄ * g₄⁻¹ = x₄⁻¹) :
    2 ^ 16 ≤ Nat.card V := by
  have hV1 := one_lt_card_of_mulAut_ne_one hx₁
  have hx₂1 := ne_one_of_fixV_eq_bot hV1 f₂
  have hx₃1 := ne_one_of_fixV_eq_bot hV1 f₃
  have hx₄1 := ne_one_of_fixV_eq_bot hV1 f₄
  have e₂ := card_eq_card_fixV_mul_sq_of_conj hV h₁ h₂ c₁₂ hx₁ hx₂1 f₂ g₂₁ g₂₂
  have hz₂3 := mul_pow_three_eq_one_of_commute h₁ h₂ c₁₂
  have hz₂1 := mul_ne_one_of_conj (z := x₁) h₂ hx₂1 g₂₁ g₂₂
  have hz₂c : x₁ * x₂ * x₃ = x₃ * (x₁ * x₂) :=
    (Commute.mul_left (show Commute x₁ x₃ from c₁₃) (show Commute x₂ x₃ from c₂₃)).eq
  have e₃ := card_eq_card_fixV_mul_sq_of_conj hV hz₂3 h₃ hz₂c hz₂1 hx₃1 f₃ g₃₁ g₃₃
  have hz₃3 := mul_pow_three_eq_one_of_commute hz₂3 h₃ hz₂c
  have hz₃1 := mul_ne_one_of_conj (z := x₁ * x₂) h₃ hx₃1 g₃₁ g₃₃
  have hz₃c : x₁ * x₂ * x₃ * x₄ = x₄ * (x₁ * x₂ * x₃) :=
    (Commute.mul_left (Commute.mul_left (show Commute x₁ x₄ from c₁₄)
      (show Commute x₂ x₄ from c₂₄)) (show Commute x₃ x₄ from c₃₄)).eq
  have e₄ := card_eq_card_fixV_mul_sq_of_conj hV hz₃3 h₄ hz₃c hz₃1 hx₄1 f₄ g₄₁ g₄₄
  have hx₁z : x₁ * (x₁ * x₂ * x₃ * x₄) = x₁ * x₂ * x₃ * x₄ * x₁ :=
    ((((Commute.refl x₁).mul_right (show Commute x₁ x₂ from c₁₂)).mul_right
      (show Commute x₁ x₃ from c₁₃)).mul_right (show Commute x₁ x₄ from c₁₄)).eq
  obtain ⟨k, hk⟩ := exists_card_fixV_eq_four_pow hV h₁ hx₁ f₁ hx₁z
  rw [f₁, Subgroup.card_bot, one_mul] at e₂
  obtain ⟨a, ha⟩ := exists_card_subgroup_eq_two_pow hV (fixV (Subgroup.zpowers (x₁ * x₂)))
  obtain ⟨b, hb⟩ := exists_card_subgroup_eq_two_pow hV (fixV (Subgroup.zpowers (x₁ * x₂ * x₃)))
  have hD := card_eq_two_pow_rk hV
  rw [ha, hD] at e₂
  rw [ha, hb, hD] at e₃
  rw [hb, hk, hD] at e₄
  have k₂ : rk V = 0 + 2 * a := exp_eq_of_card_eq (by rw [pow_zero, one_mul]; exact e₂)
  have k₃ := exp_eq_of_card_eq e₃
  have k₄ := exp_eq_of_card_eq e₄
  have hD1 : 1 ≤ rk V := by
    by_contra h0
    rw [hD, show rk V = 0 by omega, pow_zero] at hV1
    exact lt_irrefl _ hV1
  rw [hD]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem two_pow_thirtytwo_le_card_of_five (hV : ∀ v : V, v ^ 2 = 1)
    {x₁ x₂ x₃ x₄ x₅ g₂ g₃ g₄ g₅ : MulAut V} (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1)
    (h₃ : x₃ ^ 3 = 1) (h₄ : x₄ ^ 3 = 1) (h₅ : x₅ ^ 3 = 1) (c₁₂ : x₁ * x₂ = x₂ * x₁)
    (c₁₃ : x₁ * x₃ = x₃ * x₁) (c₁₄ : x₁ * x₄ = x₄ * x₁) (c₁₅ : x₁ * x₅ = x₅ * x₁)
    (c₂₃ : x₂ * x₃ = x₃ * x₂) (c₂₄ : x₂ * x₄ = x₄ * x₂) (c₂₅ : x₂ * x₅ = x₅ * x₂)
    (c₃₄ : x₃ * x₄ = x₄ * x₃) (c₃₅ : x₃ * x₅ = x₅ * x₃) (c₄₅ : x₄ * x₅ = x₅ * x₄)
    (f₁ : fixV (Subgroup.zpowers x₁) = ⊥) (f₂ : fixV (Subgroup.zpowers x₂) = ⊥)
    (f₃ : fixV (Subgroup.zpowers x₃) = ⊥) (f₄ : fixV (Subgroup.zpowers x₄) = ⊥)
    (f₅ : fixV (Subgroup.zpowers x₅) = ⊥) (hx₁ : x₁ ≠ 1)
    (g₂₁ : g₂ * x₁ * g₂⁻¹ = x₁) (g₂₂ : g₂ * x₂ * g₂⁻¹ = x₂⁻¹)
    (g₃₁ : g₃ * (x₁ * x₂) * g₃⁻¹ = x₁ * x₂) (g₃₃ : g₃ * x₃ * g₃⁻¹ = x₃⁻¹)
    (g₄₁ : g₄ * (x₁ * x₂ * x₃) * g₄⁻¹ = x₁ * x₂ * x₃) (g₄₄ : g₄ * x₄ * g₄⁻¹ = x₄⁻¹)
    (g₅₁ : g₅ * (x₁ * x₂ * x₃ * x₄) * g₅⁻¹ = x₁ * x₂ * x₃ * x₄) (g₅₅ : g₅ * x₅ * g₅⁻¹ = x₅⁻¹) :
    2 ^ 32 ≤ Nat.card V := by
  have hV1 := one_lt_card_of_mulAut_ne_one hx₁
  have hx₂1 := ne_one_of_fixV_eq_bot hV1 f₂
  have hx₃1 := ne_one_of_fixV_eq_bot hV1 f₃
  have hx₄1 := ne_one_of_fixV_eq_bot hV1 f₄
  have hx₅1 := ne_one_of_fixV_eq_bot hV1 f₅
  have e₂ := card_eq_card_fixV_mul_sq_of_conj hV h₁ h₂ c₁₂ hx₁ hx₂1 f₂ g₂₁ g₂₂
  have hz₂3 := mul_pow_three_eq_one_of_commute h₁ h₂ c₁₂
  have hz₂1 := mul_ne_one_of_conj (z := x₁) h₂ hx₂1 g₂₁ g₂₂
  have hz₂c : x₁ * x₂ * x₃ = x₃ * (x₁ * x₂) :=
    (Commute.mul_left (show Commute x₁ x₃ from c₁₃) (show Commute x₂ x₃ from c₂₃)).eq
  have e₃ := card_eq_card_fixV_mul_sq_of_conj hV hz₂3 h₃ hz₂c hz₂1 hx₃1 f₃ g₃₁ g₃₃
  have hz₃3 := mul_pow_three_eq_one_of_commute hz₂3 h₃ hz₂c
  have hz₃1 := mul_ne_one_of_conj (z := x₁ * x₂) h₃ hx₃1 g₃₁ g₃₃
  have hz₃c : x₁ * x₂ * x₃ * x₄ = x₄ * (x₁ * x₂ * x₃) :=
    (Commute.mul_left (Commute.mul_left (show Commute x₁ x₄ from c₁₄)
      (show Commute x₂ x₄ from c₂₄)) (show Commute x₃ x₄ from c₃₄)).eq
  have e₄ := card_eq_card_fixV_mul_sq_of_conj hV hz₃3 h₄ hz₃c hz₃1 hx₄1 f₄ g₄₁ g₄₄
  have hz₄3 := mul_pow_three_eq_one_of_commute hz₃3 h₄ hz₃c
  have hz₄1 := mul_ne_one_of_conj (z := x₁ * x₂ * x₃) h₄ hx₄1 g₄₁ g₄₄
  have hz₄c : x₁ * x₂ * x₃ * x₄ * x₅ = x₅ * (x₁ * x₂ * x₃ * x₄) :=
    (Commute.mul_left (Commute.mul_left (Commute.mul_left (show Commute x₁ x₅ from c₁₅)
      (show Commute x₂ x₅ from c₂₅)) (show Commute x₃ x₅ from c₃₅))
      (show Commute x₄ x₅ from c₄₅)).eq
  have e₅ := card_eq_card_fixV_mul_sq_of_conj hV hz₄3 h₅ hz₄c hz₄1 hx₅1 f₅ g₅₁ g₅₅
  have hx₁z : x₁ * (x₁ * x₂ * x₃ * x₄ * x₅) = x₁ * x₂ * x₃ * x₄ * x₅ * x₁ :=
    (((((Commute.refl x₁).mul_right (show Commute x₁ x₂ from c₁₂)).mul_right
      (show Commute x₁ x₃ from c₁₃)).mul_right (show Commute x₁ x₄ from c₁₄)).mul_right
      (show Commute x₁ x₅ from c₁₅)).eq
  obtain ⟨k, hk⟩ := exists_card_fixV_eq_four_pow hV h₁ hx₁ f₁ hx₁z
  rw [f₁, Subgroup.card_bot, one_mul] at e₂
  obtain ⟨a, ha⟩ := exists_card_subgroup_eq_two_pow hV (fixV (Subgroup.zpowers (x₁ * x₂)))
  obtain ⟨b, hb⟩ := exists_card_subgroup_eq_two_pow hV (fixV (Subgroup.zpowers (x₁ * x₂ * x₃)))
  obtain ⟨d, hd⟩ :=
    exists_card_subgroup_eq_two_pow hV (fixV (Subgroup.zpowers (x₁ * x₂ * x₃ * x₄)))
  have hD := card_eq_two_pow_rk hV
  rw [ha, hD] at e₂
  rw [ha, hb, hD] at e₃
  rw [hb, hd, hD] at e₄
  rw [hd, hk, hD] at e₅
  have k₂ : rk V = 0 + 2 * a := exp_eq_of_card_eq (by rw [pow_zero, one_mul]; exact e₂)
  have k₃ := exp_eq_of_card_eq e₃
  have k₄ := exp_eq_of_card_eq e₄
  have k₅ := exp_eq_of_card_eq e₅
  have hD1 : 1 ≤ rk V := by
    by_contra h0
    rw [hD, show rk V = 0 by omega, pow_zero] at hV1
    exact lt_irrefl _ hV1
  rw [hD]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Chain

variable [Finite V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem two_pow_sixteen_le_card (hV : ∀ v : V, v ^ 2 = 1) (hn : 12 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥) :
    2 ^ 16 ≤ Nat.card V := by
  let ι : Fin 12 ↪ Fin n := Fin.castLEEmb hn
  let ρ : alternatingGroup (Fin 12) →* ↥H := (altPreInv hψ hA).comp (altLift ι)
  have hρ : ∀ σ, ψ (ρ σ) = viaEmbedding (σ : Perm (Fin 12)) ι := fun σ =>
    (apply_altPreInv hψ hA _).trans (coe_altLift ι σ)
  let ρ' : alternatingGroup (Fin 12) →* MulAut V := H.subtype.comp ρ
  let c₁ : alternatingGroup (Fin 12) :=
    ⟨swap 0 1 * swap 0 2, by rw [mem_alternatingGroup]; decide⟩
  let c₂ : alternatingGroup (Fin 12) :=
    ⟨swap 3 4 * swap 3 5, by rw [mem_alternatingGroup]; decide⟩
  let c₃ : alternatingGroup (Fin 12) :=
    ⟨swap 6 7 * swap 6 8, by rw [mem_alternatingGroup]; decide⟩
  let c₄ : alternatingGroup (Fin 12) :=
    ⟨swap 9 10 * swap 9 11, by rw [mem_alternatingGroup]; decide⟩
  let d₂ : alternatingGroup (Fin 12) :=
    ⟨swap 4 5 * swap 6 7, by rw [mem_alternatingGroup]; decide⟩
  let d₃ : alternatingGroup (Fin 12) :=
    ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 7 8, by rw [mem_alternatingGroup]; decide⟩
  let d₄ : alternatingGroup (Fin 12) :=
    ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 10 11, by rw [mem_alternatingGroup]; decide⟩
  have hf : ∀ {a b c : Fin 12}, a ≠ b → a ≠ c → b ≠ c →
      ∀ hm : swap a b * swap a c ∈ alternatingGroup (Fin 12),
        fixV (Subgroup.zpowers (ρ' ⟨_, hm⟩)) = ⊥ := by
    intro a b c hab hac hbc hm
    exact h3 (ρ ⟨_, hm⟩) (by rw [hρ]; exact isThreeCycle_viaEmbedding ι hab hac hbc)
  have hx₁ : ρ' c₁ ≠ 1 := by
    intro h
    have h1 : ρ c₁ = 1 := Subtype.ext h
    have h2 := hρ c₁
    rw [h1, map_one] at h2
    exact (isThreeCycle_viaEmbedding ι (a := (0 : Fin 12)) (b := 1) (c := 2) (by decide)
      (by decide) (by decide)).ne_one h2.symm
  refine two_pow_sixteen_le_card_of_four hV (x₁ := ρ' c₁) (x₂ := ρ' c₂) (x₃ := ρ' c₃)
    (x₄ := ρ' c₄) (g₂ := ρ' d₂) (g₃ := ρ' d₃) (g₄ := ρ' d₄) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hf (by decide) (by decide) (by decide) _) (hf (by decide) (by decide) (by decide) _)
    (hf (by decide) (by decide) (by decide) _) (hf (by decide) (by decide) (by decide) _) hx₁
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, show c₁ ^ 3 = 1 by decide, map_one]
  · rw [← map_pow, show c₂ ^ 3 = 1 by decide, map_one]
  · rw [← map_pow, show c₃ ^ 3 = 1 by decide, map_one]
  · rw [← map_pow, show c₄ ^ 3 = 1 by decide, map_one]
  · rw [← map_mul, ← map_mul, show c₁ * c₂ = c₂ * c₁ by decide]
  · rw [← map_mul, ← map_mul, show c₁ * c₃ = c₃ * c₁ by decide]
  · rw [← map_mul, ← map_mul, show c₁ * c₄ = c₄ * c₁ by decide]
  · rw [← map_mul, ← map_mul, show c₂ * c₃ = c₃ * c₂ by decide]
  · rw [← map_mul, ← map_mul, show c₂ * c₄ = c₄ * c₂ by decide]
  · rw [← map_mul, ← map_mul, show c₃ * c₄ = c₄ * c₃ by decide]
  · rw [← map_inv, ← map_mul, ← map_mul, show d₂ * c₁ * d₂⁻¹ = c₁ by decide]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, show d₂ * c₂ * d₂⁻¹ = c₂⁻¹ by decide]
  · rw [← map_mul, ← map_inv, ← map_mul, ← map_mul,
      show d₃ * (c₁ * c₂) * d₃⁻¹ = c₁ * c₂ by decide]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, show d₃ * c₃ * d₃⁻¹ = c₃⁻¹ by decide]
  · rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
      show d₄ * (c₁ * c₂ * c₃) * d₄⁻¹ = c₁ * c₂ * c₃ by decide]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, show d₄ * c₄ * d₄⁻¹ = c₄⁻¹ by decide]

theorem two_pow_thirtytwo_le_card (hV : ∀ v : V, v ^ 2 = 1) (hn : 15 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥) :
    2 ^ 32 ≤ Nat.card V := by
  let ι : Fin 15 ↪ Fin n := Fin.castLEEmb hn
  let ρ : alternatingGroup (Fin 15) →* ↥H := (altPreInv hψ hA).comp (altLift ι)
  have hρ : ∀ σ, ψ (ρ σ) = viaEmbedding (σ : Perm (Fin 15)) ι := fun σ =>
    (apply_altPreInv hψ hA _).trans (coe_altLift ι σ)
  let ρ' : alternatingGroup (Fin 15) →* MulAut V := H.subtype.comp ρ
  let c₁ : alternatingGroup (Fin 15) :=
    ⟨swap 0 1 * swap 0 2, by rw [mem_alternatingGroup]; decide⟩
  let c₂ : alternatingGroup (Fin 15) :=
    ⟨swap 3 4 * swap 3 5, by rw [mem_alternatingGroup]; decide⟩
  let c₃ : alternatingGroup (Fin 15) :=
    ⟨swap 6 7 * swap 6 8, by rw [mem_alternatingGroup]; decide⟩
  let c₄ : alternatingGroup (Fin 15) :=
    ⟨swap 9 10 * swap 9 11, by rw [mem_alternatingGroup]; decide⟩
  let c₅ : alternatingGroup (Fin 15) :=
    ⟨swap 12 13 * swap 12 14, by rw [mem_alternatingGroup]; decide⟩
  let d₂ : alternatingGroup (Fin 15) :=
    ⟨swap 4 5 * swap 6 7, by rw [mem_alternatingGroup]; decide⟩
  let d₃ : alternatingGroup (Fin 15) :=
    ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 7 8, by rw [mem_alternatingGroup]; decide⟩
  let d₄ : alternatingGroup (Fin 15) :=
    ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 10 11, by rw [mem_alternatingGroup]; decide⟩
  let d₅ : alternatingGroup (Fin 15) :=
    ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 13 14, by rw [mem_alternatingGroup]; decide⟩
  have hf : ∀ {a b c : Fin 15}, a ≠ b → a ≠ c → b ≠ c →
      ∀ hm : swap a b * swap a c ∈ alternatingGroup (Fin 15),
        fixV (Subgroup.zpowers (ρ' ⟨_, hm⟩)) = ⊥ := by
    intro a b c hab hac hbc hm
    exact h3 (ρ ⟨_, hm⟩) (by rw [hρ]; exact isThreeCycle_viaEmbedding ι hab hac hbc)
  have hx₁ : ρ' c₁ ≠ 1 := by
    intro h
    have h1 : ρ c₁ = 1 := Subtype.ext h
    have h2 := hρ c₁
    rw [h1, map_one] at h2
    exact (isThreeCycle_viaEmbedding ι (a := (0 : Fin 15)) (b := 1) (c := 2) (by decide)
      (by decide) (by decide)).ne_one h2.symm
  refine two_pow_thirtytwo_le_card_of_five hV (x₁ := ρ' c₁) (x₂ := ρ' c₂) (x₃ := ρ' c₃)
    (x₄ := ρ' c₄) (x₅ := ρ' c₅) (g₂ := ρ' d₂) (g₃ := ρ' d₃) (g₄ := ρ' d₄) (g₅ := ρ' d₅)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hf (by decide) (by decide) (by decide) _) (hf (by decide) (by decide) (by decide) _)
    (hf (by decide) (by decide) (by decide) _) (hf (by decide) (by decide) (by decide) _)
    (hf (by decide) (by decide) (by decide) _) hx₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, show c₁ ^ 3 = 1 by decide, map_one]
  · rw [← map_pow, show c₂ ^ 3 = 1 by decide, map_one]
  · rw [← map_pow, show c₃ ^ 3 = 1 by decide, map_one]
  · rw [← map_pow, show c₄ ^ 3 = 1 by decide, map_one]
  · rw [← map_pow, show c₅ ^ 3 = 1 by decide, map_one]
  · rw [← map_mul, ← map_mul, show c₁ * c₂ = c₂ * c₁ by decide]
  · rw [← map_mul, ← map_mul, show c₁ * c₃ = c₃ * c₁ by decide]
  · rw [← map_mul, ← map_mul, show c₁ * c₄ = c₄ * c₁ by decide]
  · rw [← map_mul, ← map_mul, show c₁ * c₅ = c₅ * c₁ by decide]
  · rw [← map_mul, ← map_mul, show c₂ * c₃ = c₃ * c₂ by decide]
  · rw [← map_mul, ← map_mul, show c₂ * c₄ = c₄ * c₂ by decide]
  · rw [← map_mul, ← map_mul, show c₂ * c₅ = c₅ * c₂ by decide]
  · rw [← map_mul, ← map_mul, show c₃ * c₄ = c₄ * c₃ by decide]
  · rw [← map_mul, ← map_mul, show c₃ * c₅ = c₅ * c₃ by decide]
  · rw [← map_mul, ← map_mul, show c₄ * c₅ = c₅ * c₄ by decide]
  · rw [← map_inv, ← map_mul, ← map_mul, show d₂ * c₁ * d₂⁻¹ = c₁ by decide]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, show d₂ * c₂ * d₂⁻¹ = c₂⁻¹ by decide]
  · rw [← map_mul, ← map_inv, ← map_mul, ← map_mul,
      show d₃ * (c₁ * c₂) * d₃⁻¹ = c₁ * c₂ by decide]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, show d₃ * c₃ * d₃⁻¹ = c₃⁻¹ by decide]
  · rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
      show d₄ * (c₁ * c₂ * c₃) * d₄⁻¹ = c₁ * c₂ * c₃ by decide]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, show d₄ * c₄ * d₄⁻¹ = c₄⁻¹ by decide]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
      show d₅ * (c₁ * c₂ * c₃ * c₄) * d₅⁻¹ = c₁ * c₂ * c₃ * c₄ by decide]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, show d₅ * c₅ * d₅⁻¹ = c₅⁻¹ by decide]


theorem card_fixV_pow_four_le_of_fpf (hV : ∀ v : V, v ^ 2 = 1) (hn : 8 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {a : ↥H} (ha2 : (a : MulAut V) ^ 2 = 1) (hfpf : ∀ i, ψ a i ≠ i) :
    Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) ^ 4 ≤ Nat.card V ^ 3 := by
  classical
  by_cases hV1 : 1 < Nat.card V
  swap
  · have h1 : Nat.card V = 1 := le_antisymm (by omega) Nat.card_pos
    have h2 : Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) ≤ 1 :=
      h1 ▸ Subgroup.card_le_card_group _
    rw [h1]
    calc Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) ^ 4 ≤ 1 ^ 4 :=
          Nat.pow_le_pow_left h2 4
      _ = 1 ^ 3 := by norm_num
  have hππ : ∀ i, ψ a (ψ a i) = i := fun i => by
    have := congrArg (fun τ : Perm (Fin n) => τ i) (apply_mul_apply_eq_one (ψ := ψ) ha2)
    simpa [Perm.mul_apply] using this
  set p₁ : Fin n := ⟨0, by omega⟩
  obtain ⟨p₃, hp₃⟩ := exists_notMem_of_card_lt ({p₁, ψ a p₁} : Finset (Fin n))
    (by have := Finset.card_le_two (a := p₁) (b := ψ a p₁); omega)
  obtain ⟨p₅, hp₅⟩ := exists_notMem_of_card_lt ({p₁, ψ a p₁, p₃, ψ a p₃} : Finset (Fin n))
    (by have := Finset.card_le_four (a := p₁) (b := ψ a p₁) (c := p₃) (d := ψ a p₃); omega)
  obtain ⟨u, hu⟩ := exists_notMem_of_card_lt
    ({p₁, ψ a p₁, p₃, ψ a p₃, p₅, ψ a p₅} : Finset (Fin n))
    (by
      have := Finset.card_le_six (a := p₁) (b := ψ a p₁) (c := p₃) (d := ψ a p₃) (e := p₅)
        (f := ψ a p₅)
      omega)
  obtain ⟨v, hv⟩ := exists_notMem_of_card_lt
    (insert u ({p₁, ψ a p₁, p₃, ψ a p₃, p₅, ψ a p₅} : Finset (Fin n)))
    (by
      have h1 := Finset.card_insert_le u ({p₁, ψ a p₁, p₃, ψ a p₃, p₅, ψ a p₅} : Finset (Fin n))
      have := Finset.card_le_six (a := p₁) (b := ψ a p₁) (c := p₃) (d := ψ a p₃) (e := p₅)
        (f := ψ a p₅)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₃ hp₅ hu hv
  obtain ⟨h31, h32⟩ := hp₃
  obtain ⟨h51, h52, h53, h54⟩ := hp₅
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ := hu
  obtain ⟨hvu, hv1, hv2, hv3, hv4, hv5, hv6⟩ := hv
  have inj : ∀ {i j}, ψ a i = ψ a j → i = j := fun h => (ψ a).injective h
  have q12 : p₁ ≠ ψ a p₁ := (hfpf p₁).symm
  have q13 : p₁ ≠ p₃ := fun h => h31 h.symm
  have q15 : p₁ ≠ p₅ := fun h => h51 h.symm
  have q35 : p₃ ≠ p₅ := fun h => h53 h.symm
  have r12 : ψ a p₁ ≠ ψ a p₃ := fun h => q13 (inj h)
  have r13 : ψ a p₁ ≠ ψ a p₅ := fun h => q15 (inj h)
  have r35 : ψ a p₃ ≠ ψ a p₅ := fun h => q35 (inj h)
  have s1 : ψ a p₃ ≠ p₁ := fun h => h32 (by rw [← h, hππ])
  have s2 : ψ a p₅ ≠ p₁ := fun h => h52 (by rw [← h, hππ])
  have s3 : ψ a p₅ ≠ p₃ := fun h => h54 (by rw [← h, hππ])
  have s4 : ψ a p₁ ≠ p₅ := fun h => h52 h.symm
  have s5 : ψ a p₁ ≠ p₃ := fun h => h32 h.symm
  have s6 : ψ a p₃ ≠ p₅ := fun h => h54 h.symm
  set ξ₁ := swap p₁ p₃ * swap p₁ p₅ with hξ₁
  have hξ₁3 : ξ₁.IsThreeCycle := isThreeCycle_swap_mul_swap_same q13 q15 q35
  have hξ₂ : ψ a * ξ₁ * (ψ a)⁻¹ = swap (ψ a p₁) (ψ a p₃) * swap (ψ a p₁) (ψ a p₅) :=
    conj_swap_mul_swap _ _ _ _
  set γ := swap (ψ a p₃) (ψ a p₅) * swap u v with hγ
  have hγA : γ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap r35, sign_swap (Ne.symm hvu)]
    decide
  obtain ⟨x₁, hx₁⟩ := hA hξ₁3.mem_alternatingGroup
  obtain ⟨g, hg⟩ := hA hγA
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ↥H, x₂ = a * x₁ * a⁻¹ := ⟨_, rfl⟩
  have hψx₂ : ψ x₂ = swap (ψ a p₁) (ψ a p₃) * swap (ψ a p₁) (ψ a p₅) := by
    rw [hx₂, map_mul, map_mul, map_inv, hx₁, hξ₂]
  have hξ₂3 : (ψ x₂).IsThreeCycle := by
    rw [hx₂, map_mul, map_mul, map_inv, hx₁]
    exact isThreeCycle_conj hξ₁3 _
  have hfix₂ : ∀ i, i ≠ ψ a p₁ → i ≠ ψ a p₃ → i ≠ ψ a p₅ → ψ x₂ i = i := fun i h1 h2 h3 => by
    rw [hψx₂, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
  have hfixγ : ∀ i, i ≠ ψ a p₃ → i ≠ ψ a p₅ → i ≠ u → i ≠ v → ψ g i = i := fun i h1 h2 h3 h4 => by
    rw [hg, hγ, Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
  have c₁₂ : (x₁ : MulAut V) * x₂ = x₂ * x₁ := by
    refine (coe_eq_coe_of_apply_eq hψ (h₁ := x₁ * x₂) (h₂ := x₂ * x₁) ?_)
    rw [map_mul, map_mul, hx₁]
    exact (commute_swap_mul_swap (hfix₂ p₁ q12 s1.symm s2.symm)
      (hfix₂ p₃ s5.symm (hfpf p₃).symm s3.symm) (hfix₂ p₅ s4.symm s6.symm (hfpf p₅).symm)).symm
  have g₁ : (g : MulAut V) * x₁ * (g : MulAut V)⁻¹ = x₁ := by
    refine (coe_eq_coe_of_apply_eq hψ (h₁ := g * x₁ * g⁻¹) (h₂ := x₁) ?_)
    rw [map_mul, map_mul, map_inv, hx₁]
    have hc := commute_swap_mul_swap (a := p₁) (b := p₃) (c := p₅)
      (hfixγ p₁ s1.symm s2.symm (Ne.symm hu1) (Ne.symm hv1))
      (hfixγ p₃ (hfpf p₃).symm s3.symm (Ne.symm hu3) (Ne.symm hv3))
      (hfixγ p₅ s6.symm (hfpf p₅).symm (Ne.symm hu5) (Ne.symm hv5))
    rw [hc, mul_inv_cancel_right]
  have g₂ : (g : MulAut V) * x₂ * (g : MulAut V)⁻¹ = (x₂ : MulAut V)⁻¹ := by
    refine (coe_eq_coe_of_apply_eq hψ (h₁ := g * x₂ * g⁻¹) (h₂ := x₂⁻¹) ?_)
    rw [map_mul, map_mul, map_inv, map_inv, hψx₂, conj_swap_mul_swap,
      hfixγ _ r12 r13 (Ne.symm hu2) (Ne.symm hv2), hg, hγ]
    simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne (Ne.symm hu4) (Ne.symm hv4), swap_apply_left,
      swap_apply_of_ne_of_ne (Ne.symm hu6) (Ne.symm hv6), swap_apply_right, mul_inv_rev, swap_inv,
      swap_inv]
  have h₁ : (x₁ : MulAut V) ^ 3 = 1 := by
    have : x₁ ^ 3 = 1 := hψ (by rw [map_pow, hx₁, map_one, ← hξ₁3.orderOf, pow_orderOf_eq_one])
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have h₂ : (x₂ : MulAut V) ^ 3 = 1 := by
    have : x₂ ^ 3 = 1 := hψ (by rw [map_pow, map_one, ← hξ₂3.orderOf, pow_orderOf_eq_one])
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have f₁ := h3 x₁ (hx₁ ▸ hξ₁3)
  have f₂ := h3 x₂ hξ₂3
  have hX₁ : (x₁ : MulAut V) ≠ 1 := ne_one_of_fixV_eq_bot hV1 f₁
  have hX₂ : (x₂ : MulAut V) ≠ 1 := ne_one_of_fixV_eq_bot hV1 f₂
  have hy₂ := notMem_zpowers_of_conj h₂ hX₂ g₁ g₂
  have hcard := card_eq_card_fixV_mul_card_fixV hV h₁ h₂ c₁₂ hX₁ hy₂ f₂
  have hconj : (g : MulAut V) * (x₁ * x₂) * (g : MulAut V)⁻¹ =
      (x₁ : MulAut V) * (x₂ : MulAut V) ^ 2 := by
    have hinv : (x₂ : MulAut V)⁻¹ = (x₂ : MulAut V) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', h₂]
    calc (g : MulAut V) * (x₁ * x₂) * (g : MulAut V)⁻¹ =
          ((g : MulAut V) * x₁ * (g : MulAut V)⁻¹) * ((g : MulAut V) * x₂ * (g : MulAut V)⁻¹) := by
          group
      _ = (x₁ : MulAut V) * (x₂ : MulAut V) ^ 2 := by rw [g₁, g₂, hinv]
  have hcc : Nat.card (fixV (Subgroup.zpowers ((x₁ : MulAut V) * (x₂ : MulAut V) ^ 2))) =
      Nat.card (fixV (Subgroup.zpowers ((x₁ : MulAut V) * (x₂ : MulAut V)))) := by
    rw [← hconj, card_fixV_zpowers_conj]
  rw [f₁, Subgroup.card_bot, one_mul, ← hcc] at hcard
  have hainv : (a : MulAut V)⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  have hprod : (x₁ : MulAut V) * (x₂ : MulAut V) ^ 2 =
      ((x₁ : MulAut V) * (a : MulAut V) * (x₁ : MulAut V)⁻¹) * (a : MulAut V) := by
    have hinv : (x₂ : MulAut V) ^ 2 = (x₂ : MulAut V)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, h₂]
    rw [hinv, hx₂]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, hainv]
    group
  rw [hprod] at hcard
  set y : MulAut V := (x₁ : MulAut V) * (a : MulAut V) * (x₁ : MulAut V)⁻¹ with hy
  have hle : fixV (Subgroup.zpowers (a : MulAut V)) ⊓ fixV (Subgroup.zpowers y) ≤
      fixV (Subgroup.zpowers (y * (a : MulAut V))) := fun w hw => by
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    rw [mem_fixV_zpowers_iff] at hw1 hw2 ⊢
    rw [MulAut.mul_apply, hw1, hw2]
  have hcy : Nat.card (fixV (Subgroup.zpowers y)) =
      Nat.card (fixV (Subgroup.zpowers (a : MulAut V))) := card_fixV_zpowers_conj _ _
  have hsup := CFSG.Quasithin.card_sup_mul_card_inf (fixV (Subgroup.zpowers (a : MulAut V)))
    (fixV (Subgroup.zpowers y))
  have hsupV : Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V)) ⊔ fixV (Subgroup.zpowers y)) ≤
      Nat.card V := Subgroup.card_le_card_group _
  have hinf := Subgroup.card_le_of_le hle
  set c := Nat.card (fixV (Subgroup.zpowers (y * (a : MulAut V))))
  set ca := Nat.card (fixV (Subgroup.zpowers (a : MulAut V)))
  rw [hcy] at hsup
  have k1 : ca * ca ≤ c * Nat.card V := by
    calc ca * ca = Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V)) ⊔
            fixV (Subgroup.zpowers y)) *
          Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V)) ⊓ fixV (Subgroup.zpowers y)) :=
          hsup.symm
      _ ≤ Nat.card V * c := Nat.mul_le_mul hsupV hinf
      _ = c * Nat.card V := mul_comm _ _
  calc ca ^ 4 = (ca * ca) * (ca * ca) := by ring
    _ ≤ (c * Nat.card V) * (c * Nat.card V) := Nat.mul_le_mul k1 k1
    _ = (c * c) * Nat.card V * Nat.card V := by ring
    _ = Nat.card V ^ 3 := by rw [← hcard]; ring

theorem card_mul_card_fixV_lt_of_threeCycle (hV : ∀ v : V, v ^ 2 = 1) (hn : 12 ≤ n)
    (hn' : n < 32) (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hB : B ≠ ⊥) (hel : IsElemAbelian2 B) :
    Nat.card B * Nat.card (fixV B) < Nat.card V := by
  classical
  by_contra hcon
  push Not at hcon
  have hbig : 2 ^ n < Nat.card V ∧ n ^ 4 < Nat.card V := by
    rcases Nat.lt_or_ge n 15 with h | h
    · have h16 := two_pow_sixteen_le_card hV hn hψ hA h3
      constructor
      · calc 2 ^ n < 2 ^ 16 := Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ ≤ _ := h16
      · calc n ^ 4 ≤ 14 ^ 4 := Nat.pow_le_pow_left (by omega) 4
          _ < 2 ^ 16 := by norm_num
          _ ≤ _ := h16
    · have h32 := two_pow_thirtytwo_le_card hV h hψ hA h3
      constructor
      · calc 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ ≤ _ := h32
      · calc n ^ 4 ≤ 31 ^ 4 := Nat.pow_le_pow_left (by omega) 4
          _ < 2 ^ 32 := by norm_num
          _ ≤ _ := h32
  have hVpos : 0 < Nat.card V := Nat.card_pos
  obtain ⟨⟨b₀', hb₀'⟩, hb₀'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
  set b₀ : ↥H := ⟨b₀', hBH hb₀'⟩ with hb₀
  have hb₀1 : b₀ ≠ 1 := fun h => hb₀'1 (Subtype.ext (congrArg (fun x : ↥H => (x : MulAut V)) h))
  by_cases hfix : ∃ b : ↥H, (b : MulAut V) ∈ B ∧ b ≠ 1 ∧ ∃ w, ψ b w = w
  ·
    obtain ⟨b, hbB, hb1, w, hw⟩ := hfix
    obtain ⟨u, hu⟩ : ∃ u, ψ b u ≠ u := by
      by_contra h
      push Not at h
      exact hb1 (hψ (by rw [map_one]; exact Equiv.ext h))
    have hsq := card_fixV_sq_of_apply_ne hV hψ hA h3 (hel.2 _ hbB) hu hw
    have hB2 : Nat.card B ≤ 2 ^ (n / 2) := by
      have h1 := CFSG.Quasithin.G11.Harris.Ln2.card_le_of_elemAbelian_perm
        (B := (B.subgroupOf H).map ψ)
        (by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [← map_mul, ← map_mul]
          exact congrArg ψ (Subtype.ext (hel.1 _ hx _ hy)))
        (by
          rintro _ ⟨x, hx, rfl⟩
          exact apply_mul_apply_eq_one (hel.2 _ hx))
      rw [Fintype.card_fin, Subgroup.card_map_of_injective hψ,
        show Nat.card ↥(B.subgroupOf H) = Nat.card B from
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv] at h1
      exact h1
    set c := Nat.card (fixV (Subgroup.zpowers (b : MulAut V))) with hc
    have hle : Nat.card (fixV B) ≤ c := Subgroup.card_le_of_le (fixV_zpowers_le hbB)
    have hVc : Nat.card V ≤ 2 ^ (n / 2) * c := hcon.trans (Nat.mul_le_mul hB2 hle)
    have h1 : Nat.card V * Nat.card V ≤ 2 ^ n * Nat.card V := by
      calc Nat.card V * Nat.card V ≤ (2 ^ (n / 2) * c) * (2 ^ (n / 2) * c) :=
            Nat.mul_le_mul hVc hVc
        _ = 2 ^ (n / 2 + n / 2) * c ^ 2 := by ring
        _ ≤ 2 ^ n * Nat.card V :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) hsq.le
    have h2 := Nat.le_of_mul_le_mul_right h1 hVpos
    omega
  ·
    push Not at hfix
    have hBn : Nat.card B ≤ n := by
      let f : ↥B → Fin n := fun b => ψ ⟨b, hBH b.2⟩ ⟨0, by omega⟩
      have hf : Function.Injective f := by
        intro b₁ b₂ h
        by_contra hne
        set g : ↥H := (⟨b₁, hBH b₁.2⟩ : ↥H)⁻¹ * ⟨b₂, hBH b₂.2⟩ with hg
        have hgB : (g : MulAut V) ∈ B := B.mul_mem (B.inv_mem b₁.2) b₂.2
        have hg1 : g ≠ 1 := fun h' => hne (by
          have h3' : (⟨b₁, hBH b₁.2⟩ : ↥H) = ⟨b₂, hBH b₂.2⟩ := inv_mul_eq_one.1 h'
          exact Subtype.ext (congrArg (fun x : ↥H => (x : MulAut V)) h3'))
        refine hfix g hgB hg1 ⟨0, by omega⟩ ?_
        have h4 : ψ ⟨b₁, hBH b₁.2⟩ ⟨0, by omega⟩ = ψ ⟨b₂, hBH b₂.2⟩ ⟨0, by omega⟩ := h
        rw [hg, map_mul, map_inv, Perm.mul_apply, ← h4, perm_inv_apply_apply]
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_fin] at this
    have hfpf : ∀ i, ψ b₀ i ≠ i := fun i h => hfix b₀ hb₀' hb₀1 i h
    have h4 := card_fixV_pow_four_le_of_fpf hV (by omega) hψ hA h3 (hel.2 _ hb₀') hfpf
    set c := Nat.card (fixV (Subgroup.zpowers (b₀ : MulAut V))) with hc
    have hle : Nat.card (fixV B) ≤ c := Subgroup.card_le_of_le (fixV_zpowers_le hb₀')
    have h1 : Nat.card V ≤ n * c := hcon.trans (Nat.mul_le_mul hBn hle)
    have h2 : Nat.card V * Nat.card V ^ 3 ≤ n ^ 4 * Nat.card V ^ 3 := by
      calc Nat.card V * Nat.card V ^ 3 = Nat.card V ^ 4 := by ring
        _ ≤ (n * c) ^ 4 := Nat.pow_le_pow_left h1 4
        _ = n ^ 4 * c ^ 4 := by ring
        _ ≤ n ^ 4 * Nat.card V ^ 3 := Nat.mul_le_mul_left _ h4
    have h3' := Nat.le_of_mul_le_mul_right h2 (by positivity)
    omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
