module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6ClosingCore
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SylowCentralizerClosure
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPhi6

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup TauCeti CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

@[expose] def TwoTorusGenOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → 27 ≤ Nat.card K → TwoTorusGen K

@[expose] def AnisotropicOfPowOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r : ℕ), r.Prime → r ≠ 2 → (r : K) ≠ 0 →
    ¬ r ∣ Nat.card K - 1 → AnisotropicOfPow K r

section Arith

theorem dvd_pow_six_sub_one_of_phi6 {r q : ℕ} (hq : 1 ≤ q)
    (hd : (r : ℤ) ∣ (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1) : r ∣ (q ^ 3) ^ 2 - 1 := by
  have h1 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hq)
  rw [← Int.natCast_dvd_natCast, Nat.cast_sub h1]
  push_cast
  have : ((q : ℤ) ^ 3) ^ 2 - 1 =
      ((q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1) * ((q : ℤ) ^ 4 + (q : ℤ) ^ 3 - (q : ℤ) - 1) := by ring
  rw [this]
  exact Dvd.dvd.mul_right hd _

theorem not_dvd_pow_three_sub_one_of_phi6 {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : 1 ≤ q)
    (hd : (r : ℤ) ∣ (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1) : ¬ r ∣ q ^ 3 - 1 := by
  intro h
  have h1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  rw [← Int.natCast_dvd_natCast, Nat.cast_sub h1] at h
  push_cast at h
  have hplus : (r : ℤ) ∣ (q : ℤ) ^ 3 + 1 := by
    have : (q : ℤ) ^ 3 + 1 = ((q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1) * ((q : ℤ) + 1) := by ring
    rw [this]; exact Dvd.dvd.mul_right hd _
  have h2 : (r : ℤ) ∣ 2 := by
    have := dvd_sub hplus h
    simpa using this
  have : r ∣ 2 := by exact_mod_cast h2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)

theorem not_dvd_card_SL2_of_phi6 {r q : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hq : 1 ≤ q)
    (hrq : ¬ r ∣ q) (hd : (r : ℤ) ∣ (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1) :
    ¬ r ∣ (q ^ 2 - 1) * q := by
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    rw [← Int.natCast_dvd_natCast, Nat.cast_sub h1] at h
    push_cast at h
    have h2 : (r : ℤ) ∣ (q : ℤ) - 2 := by
      have := dvd_sub h hd
      have e : (q : ℤ) ^ 2 - 1 - ((q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1) = (q : ℤ) - 2 := by ring
      rwa [e] at this
    have h3 : (r : ℤ) ∣ 3 := by
      have := dvd_sub hd (Dvd.dvd.mul_right h2 ((q : ℤ) + 1))
      have e : (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1 - ((q : ℤ) - 2) * ((q : ℤ) + 1) = 3 := by ring
      rwa [e] at this
    have : r ∣ 3 := by exact_mod_cast h3
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · exact hrq h

theorem card_SL2_eq {F : Type} [Field F] [Finite F] :
    Nat.card (SL(2, F)) = (Nat.card F ^ 2 - 1) * Nat.card F := by
  classical
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Nat.card_eq_fintype_card, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hq1 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have : Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [this, ← mul_assoc, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self (by omega), mul_one]

end Arith


@[expose] def Phi6CoreW (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c,
    r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∃ (E₀ : Subgroup (twistedGroup σ.toRingHom)) (w : twistedGroup σ.toRingHom)
      (P : Sylow r (twistedGroup σ.toRingHom)),
      (∀ x ∈ E₀, x ^ r = 1) ∧ Nat.card E₀ = r ^ 2 ∧ w * w = 1 ∧
      (∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹) ∧ E₀ ≤ (P : Subgroup (twistedGroup σ.toRingHom)) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)),
        ∀ y ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x * y = y * x) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x ^ r = 1 → x ∈ E₀) ∧
      (∃ g : twistedGroup σ.toRingHom, g * w * g⁻¹ = slLong σ.toRingHom hσ (-1) ∧
        (invCentGroup σ.toRingHom hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤ closure (cenGen E₀)) ∧
      (∃ u x₁ : twistedGroup σ.toRingHom, u * u = 1 ∧ u ≠ 1 ∧ x₁ ∈ E₀ ∧ x₁ ≠ 1 ∧
        u * w = w * u ∧ u * x₁ = x₁ * u)


theorem closure_cenGen_eq_top_of_core (hDT : TwoTorusGenOdd) (hAn : AnisotropicOfPowOdd)
    {r : ℕ} (hr5 : 5 ≤ r) (h : Phi6CoreW r) (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσq : ∀ c, σ c = c ^ (ℓ ^ f)) (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (hr : r.Prime) (hrℓ : r ≠ ℓ)
    (hd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    ∃ E₀ : Subgroup (twistedGroup σ.toRingHom), (∀ x ∈ E₀, x ^ r = 1) ∧ Nat.card E₀ = r ^ 2 ∧
      closure (cenGen E₀) = ⊤ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨E₀, w, P, hE₀r, hE₀c, hw2, hwE, hEP, hPab, hΩ, ⟨g, hg, hM⟩,
    ⟨u, x₁, hu2, hu1, hx₁E, hx₁1, huw, hux⟩⟩ := h ℓ f hℓ hℓ2 hf K hK σ hσq hσ hr hrℓ hd
  refine ⟨E₀, hE₀r, hE₀c, ?_⟩
  have hr2 : r ≠ 2 := by omega
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h27 : 27 ≤ Nat.card K := by
    rw [hK]
    have : 3 ≤ ℓ ^ f := le_trans (show 3 ≤ ℓ by have := hℓ.two_le; omega) (Nat.le_self_pow (by omega) ℓ)
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (ℓ ^ f) ^ 3 := Nat.pow_le_pow_left this 3
  have hrK : (r : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ r).1 h0
    exact hrℓ ((Nat.prime_dvd_prime_iff_eq hℓ hr).1 this).symm
  have hrK2 : r ∣ Nat.card K ^ 2 - 1 := by rw [hK]; exact dvd_pow_six_sub_one_of_phi6 hq1 hd
  have hrK1 : ¬ r ∣ Nat.card K - 1 := by
    rw [hK]; exact not_dvd_pow_three_sub_one_of_phi6 hr hr2 hq1 hd
  have hrq : ¬ r ∣ ℓ ^ f := fun h' => hrℓ ((Nat.prime_dvd_prime_iff_eq hr hℓ).1 (hr.dvd_of_dvd_pow h'))
  have hFcard : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hK hσq
  have : Finite (fixedField σ.toRingHom) := Subtype.finite
  have hrF : ¬ r ∣ Nat.card (SL(2, fixedField σ.toRingHom)) := by
    rw [card_SL2_eq, hFcard]
    exact not_dvd_card_SL2_of_phi6 hr hr5 hq1 hrq hd
  have hR : ∀ c ∈ closure (cenGen E₀), c ^ r = 1 → c ≠ 1 →
      Subgroup.centralizer ({c} : Set (twistedGroup σ.toRingHom)) ≤ closure (cenGen E₀) :=
    fun c hc hcr hc1 => CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.centralizer_le_closure_cenGen
      P hEP hPab hΩ hc hcr hc1
  have hx₁H : x₁ ∈ closure (cenGen E₀) := subset_closure ⟨x₁, hx₁E, hx₁1, rfl⟩
  exact eq_top_of_core hσ hℓ hℓ2 hf hK hσq (hDT K hK2 h27) hr hr2 hrℓ hrK2 hrF
    (hAn K r hr hr2 hrK hrK1) hR hw2 hg hM hx₁H (hE₀r x₁ hx₁E) hx₁1 (hwE x₁ hx₁E) hu2 hu1 huw hux


theorem phiPlaneGenAt_neg_of_exists_top {r : ℕ} (hr5 : 5 ≤ r)
    (h : ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      (∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) →
      r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 →
      ∃ E₀ : Subgroup (twistedGroup σ.toRingHom), (∀ x ∈ E₀, x ^ r = 1) ∧ Nat.card E₀ = r ^ 2 ∧
        closure (cenGen E₀) = ⊤) :
    PhiPlaneGenAt (-1) r := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ hr hrℓ hd E hE hEcard
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact r.Prime := ⟨hr⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq2 : 2 ≤ ℓ ^ f :=
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card (σ := σ.toRingHom) hK hσ'
  obtain ⟨E₀, hE₀p, hE₀c, htop⟩ := h ℓ f hℓ hℓ2 hf K hK σ hσ hσ3 hr hrℓ hd
  let ε₁ := Inner.twistedEquivRoot σ hK2 hq2 hK hσ
  let E_Y : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := E₀.map ε₁.toMonoidHom
  have hEYc : Nat.card E_Y = r ^ 2 := by
    rw [Subgroup.card_map_of_injective ε₁.injective]
    exact hE₀c
  have hEYp : ∀ x ∈ E_Y, x ^ r = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE₀p y hy, map_one]
  have hEYtop : closure (cenGen E_Y) = ⊤ := by
    have h1 : closure (cenGen E_Y) = (closure (cenGen E₀)).map ε₁.toMonoidHom := by
      rw [cenGen_map, MonoidHom.map_closure]
      rfl
    rw [h1, htop]
    exact Subgroup.map_top_of_surjective _ ε₁.surjective
  have hshape := CFSG.RankThree.PartOne.K128.sylowShape_D4_36 (ℓ := ℓ) hf K hK σ hσ (ε := -1)
    (Or.inr rfl) hr (by omega) hd
  exact Inner.closure_cenGen_eq_top_of_conj_plane hshape E_Y hEYp hEYc hEYtop E
    (fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx) hEcard

theorem phiPlaneGenAt_neg_of_core (hDT : TwoTorusGenOdd) (hAn : AnisotropicOfPowOdd) {r : ℕ}
    (hr5 : 5 ≤ r) (h : Phi6CoreW r) : PhiPlaneGenAt (-1) r :=
  phiPlaneGenAt_neg_of_exists_top hr5 fun ℓ f hℓ hℓ2 hf K _ _ hK σ hσq hσ hr hrℓ hd =>
    closure_cenGen_eq_top_of_core hDT hAn hr5 h ℓ f hℓ hℓ2 hf K hK σ hσq hσ hr hrℓ hd

theorem seitzExcAnisotropicTrialityOdd_of_core (hDT : TwoTorusGenOdd) (hAn : AnisotropicOfPowOdd)
    (h : ∀ r, 5 ≤ r → Phi6CoreW r) : SeitzExcAnisotropicTrialityOdd :=
  seitzExcAnisotropicTrialityOdd_of_phi6 fun r hr5 => phiPlaneGenAt_neg_of_core hDT hAn hr5 (h r hr5)

theorem seitzExcAnisotropicForAt_trialityOdd_handback_of_core (hDT : TwoTorusGenOdd)
    (hAn : AnisotropicOfPowOdd) (h : ∀ r, 5 ≤ r → Phi6CoreW r)
    (h63 : PhiFramePlaneGenAt (-1) 3) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback_of_phi6
    (fun r hr5 => phiPlaneGenAt_neg_of_core hDT hAn hr5 (h r hr5)) h63

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
