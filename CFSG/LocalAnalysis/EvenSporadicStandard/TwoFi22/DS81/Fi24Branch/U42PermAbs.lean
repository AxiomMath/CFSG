module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.SmallIndex

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.SignalizerFunctorTheorem.NonLocalExc

variable {Γ : Type*} [Group Γ]

theorem card_le_card_inf_mul_card (K P : Subgroup Γ) [Finite K] (R : Finset Γ)
    (hR : ∀ x ∈ K, ∃ r ∈ R, x * r⁻¹ ∈ P) :
    Nat.card K ≤ Nat.card ↥(K ⊓ P) * R.card := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  choose f hfR hfP using fun x : K => hR x x.2
  have hfib : ∀ b ∈ R, (Finset.univ.filter fun a : K => f a = b).card ≤ Nat.card ↥(K ⊓ P) := by
    intro b _
    by_cases hne : (Finset.univ.filter fun a : K => f a = b).Nonempty
    · obtain ⟨x0, hx0mem⟩ := hne
      have hx0eq : f x0 = b := (Finset.mem_filter.mp hx0mem).2
      have hfin : (K ⊓ P : Set Γ).Finite :=
        (Set.toFinite (K : Set Γ)).subset (fun x hx => hx.1)
      have hle : ((Finset.univ.filter fun a : K => f a = b) : Set K).ncard ≤
          (K ⊓ P : Set Γ).ncard := by
        refine Set.ncard_le_ncard_of_injOn (fun x : K => (x : Γ) * (x0 : Γ)⁻¹) ?_ ?_ hfin
        · intro a ha
          have ha' : f a = b := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          have hmemK : (a : Γ) * (x0 : Γ)⁻¹ ∈ K := K.mul_mem a.2 (K.inv_mem x0.2)
          have hmemP : (a : Γ) * (x0 : Γ)⁻¹ ∈ P := by
            have h1 : (a : Γ) * (x0 : Γ)⁻¹ =
                ((a : Γ) * (f a)⁻¹) * (((x0 : Γ) * (f x0)⁻¹))⁻¹ := by
              rw [ha', hx0eq]; group
            rw [h1]
            exact P.mul_mem (hfP a) (P.inv_mem (hfP x0))
          exact Subgroup.mem_inf.mpr ⟨hmemK, hmemP⟩
        · intro a _ c _ heq
          exact Subtype.ext (mul_right_cancel heq)
      rw [← Nat.card_coe_set_eq (K ⊓ P : Set Γ), Set.ncard_coe_finset] at hle
      exact hle
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hmain := Finset.card_le_mul_card_image_of_maps_to
    (s := (Finset.univ : Finset K)) (t := R) (f := f) (n := Nat.card ↥(K ⊓ P))
    (fun a _ => hfR a) hfib
  simpa [Nat.card_eq_fintype_card] using hmain

theorem card_le_24_of_not_mem (B P : Subgroup Γ) [Finite B] (hPB : P ≤ B)
    (hnorm : ∀ x ∈ B, ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hP : Nat.card P = 27) (hB : Nat.card B = 648)
    (hexp : ∀ p ∈ P, p ^ 3 = 1) {z : Γ} (hz : ∃ x ∈ P, ∃ y ∈ P, z = x * y * x⁻¹ * y⁻¹)
    (hN : ∀ a ∈ P, a ≠ 1 → a ≠ z → a⁻¹ ≠ z → ∃ R : Finset Γ, R.card ≤ 6 ∧
      ∀ x ∈ B, (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹) → ∃ r ∈ R, x * r⁻¹ ∈ P)
    (K : Subgroup Γ) (hKB : K ≤ B) (hzK : z ∉ K) : Nat.card K ≤ 24 := by
  classical
  obtain ⟨x0, hx0, y0, hy0, hzxy⟩ := hz
  have hzP : z ∈ P := by
    rw [hzxy]
    exact mul_mem (mul_mem (mul_mem hx0 hy0) (inv_mem hx0)) (inv_mem hy0)
  have hfinP : Finite P := Finite.of_injective (Subgroup.inclusion hPB)
    (Subgroup.inclusion_injective hPB)
  have hfinK : Finite K := Finite.of_injective (Subgroup.inclusion hKB)
    (Subgroup.inclusion_injective hKB)
  obtain ⟨S, hS⟩ : ∃ S : Subgroup Γ, S = K ⊓ P := ⟨_, rfl⟩
  have hSK : S ≤ K := hS ▸ inf_le_left
  have hSP : S ≤ P := hS ▸ inf_le_right
  have hmemS : ∀ g, g ∈ S ↔ g ∈ K ∧ g ∈ P := fun g => by rw [hS, Subgroup.mem_inf]
  have hfinS : Finite S := Finite.of_injective (Subgroup.inclusion hSP)
    (Subgroup.inclusion_injective hSP)
  have hSdvd : Nat.card S ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le hSP
    rwa [hP] at this
  obtain ⟨m, hm, hSm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hSdvd
  interval_cases m
  ·
    have hS1 : Nat.card S = 1 := by simpa using hSm
    have hSbot : S = ⊥ := (Subgroup.card_eq_one).1 hS1
    have hinj : Function.Injective (fun kp : K × P =>
        (⟨(kp.1 : Γ) * kp.2, mul_mem (hKB kp.1.2) (hPB kp.2.2)⟩ : B)) := by
      intro kp kp' h
      have h1 : (kp.1 : Γ) * kp.2 = kp'.1 * kp'.2 := congrArg Subtype.val h
      have h2 : ((kp'.1 : Γ))⁻¹ * kp.1 = kp'.2 * (kp.2 : Γ)⁻¹ := by
        have := congrArg (fun g => (kp'.1 : Γ)⁻¹ * g * (kp.2 : Γ)⁻¹) h1
        simpa [mul_assoc] using this
      have h3 : ((kp'.1 : Γ))⁻¹ * kp.1 ∈ S := by
        rw [hmemS]
        refine ⟨mul_mem (inv_mem kp'.1.2) kp.1.2, ?_⟩
        rw [h2]
        exact mul_mem kp'.2.2 (inv_mem kp.2.2)
      rw [hSbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : kp.1 = kp'.1 := Subtype.ext h3.symm
      have h5 : (kp.2 : Γ) = kp'.2 := by
        have : (kp.1 : Γ) * kp.2 = kp.1 * kp'.2 := by rw [h1, ← h3]
        exact mul_left_cancel this
      exact Prod.ext h4 (Subtype.ext h5)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hP, hB] at hle
    omega
  ·
    have hS3 : Nat.card S = 3 := by simpa using hSm
    obtain ⟨a, haS, ha1⟩ : ∃ a ∈ S, a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : S = ⊥ := (Subgroup.eq_bot_iff_forall S).2 hcon
      rw [this] at hS3
      simp at hS3
    have haP : a ∈ P := hSP haS
    have haK : a ∈ K := hSK haS
    have ha3 : a ^ 3 = 1 := hexp a haP
    have haz : a ≠ z := fun h => hzK (h ▸ haK)
    have haz' : a⁻¹ ≠ z := fun h => hzK (h ▸ inv_mem haK)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have hSz : S = Subgroup.zpowers a := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haS) ?_).symm
      rw [hS3, Nat.card_zpowers, hord]
    obtain ⟨R, hRcard, hRmem⟩ := hN a haP ha1 haz haz'
    have hcover : ∀ x ∈ K, ∃ r ∈ R, x * r⁻¹ ∈ P := by
      intro x hx
      refine hRmem x (hKB hx) ?_
      have hb : x * a * x⁻¹ ∈ S := (hmemS _).2 ⟨mul_mem (mul_mem hx haK) (inv_mem hx),
        hnorm x (hKB hx) a haP⟩
      rw [hSz] at hb
      rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers ha3 hb with h | h | h
      · exact absurd (by simpa using h) ha1
      · exact Or.inl h
      · exact Or.inr h
    have hcard := card_le_card_inf_mul_card K P R hcover
    rw [← hS, hS3] at hcard
    omega
  ·
    have hS9 : Nat.card S = 9 := by simpa using hSm
    exact absurd (hSK (hzxy ▸ commutator_mem_of_card_eq_nine hSP hP hS9 hx0 hy0)) hzK
  ·
    have hS27 : Nat.card S = 27 := by simpa using hSm
    have hSP' : S = P := Subgroup.eq_of_le_of_card_ge hSP (by rw [hP, hS27])
    exact absurd (hSK (hSP' ▸ hzP)) hzK

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
