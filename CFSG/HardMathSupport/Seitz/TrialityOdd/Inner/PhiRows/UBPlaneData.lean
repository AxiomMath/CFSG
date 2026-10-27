module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBSL3
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBSinger
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBCentralizerL
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylTwist

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped MatrixGroups commutatorElement

section UBPlaneData


variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem not_dvd_pred_of_dvd_phi3 {r q : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hq : 1 ≤ q)
    (hrd : r ∣ q ^ 2 + q + 1) : ¬ r ∣ q - 1 := by
  intro h
  obtain ⟨k, hk⟩ := h
  have hq' : q = r * k + 1 := by omega
  have h3 : r ∣ 3 := by
    have : q ^ 2 + q + 1 = r * (r * k ^ 2 + 3 * k) + 3 := by
      rw [hq']; ring
    rw [this] at hrd
    exact (Nat.dvd_add_right (Dvd.intro _ rfl)).1 hrd
  exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3)

theorem odd_of_dvd_phi3 {r q : ℕ} (hr : r.Prime) (hrd : r ∣ q ^ 2 + q + 1) : r ≠ 2 := by
  rintro rfl
  have : Even (q ^ 2 + q + 1) := even_iff_two_dvd.2 hrd
  have h2 : Even (q ^ 2 + q) := by
    have : q ^ 2 + q = q * (q + 1) := by ring
    rw [this]
    exact Nat.even_mul_succ_self q
  have h3 : Odd (q ^ 2 + q + 1) := h2.add_one
  exact (Nat.not_even_iff_odd.2 h3) this

theorem exists_unit_of_orderOf {q r : ℕ} (hr : r.Prime) (hK : Nat.card K = q ^ 3) (hq : 1 ≤ q)
    (hrd : r ∣ q ^ 2 + q + 1) : ∃ t : Kˣ, orderOf t = r := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card Kˣ = q ^ 3 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hdvd : r ∣ Nat.card Kˣ := by
    rw [hcard]
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    have e : (k + 1) ^ 3 - 1 = k * ((k + 1) ^ 2 + (k + 1) + 1) := by
      have : (k + 1) ^ 3 = k * ((k + 1) ^ 2 + (k + 1) + 1) + 1 := by ring
      omega
    rw [e]
    exact Dvd.dvd.mul_left hrd _
  exact exists_prime_orderOf_dvd_card' r hdvd

include hσ in
theorem exists_explicit_plane (hcen : Subgroup.center (twistedGroup σ) = ⊥) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hrd : r ∣ q ^ 2 + q + 1) :
    ∃ (t : Kˣ) (c : twistedGroup σ), (t : K) * σ t * σ (σ t) = 1 ∧ orderOf t = r ∧
      orderOf (slShort σ hσ (HSL t)) = r ∧ orderOf c = r ∧
      c ∈ longSub 6 (hexGroup (twistedX σ)) ∧
      (∀ l ∈ longSub 6 (hexGroup (twistedX σ)),
        l * slShort σ hσ (HSL t) = slShort σ hσ (HSL t) * l) ∧
      (∀ θ ∈ longSub 6 (hexGroup (twistedX σ)),
        (∀ l ∈ longSub 6 (hexGroup (twistedX σ)), θ * l = l * θ) → θ ^ 3 = 1) ∧
      (∀ a ∈ longSub 6 (hexGroup (twistedX σ)), ∀ b ∈ longSub 6 (hexGroup (twistedX σ)),
        a * c = c * a → b * c = c * b → a * b = b * a) ∧
      (∀ P : Subgroup (twistedGroup σ), ⁅P, P⁆ = P →
        P ≤ Subgroup.centralizer {slShort σ hσ (HSL t)} →
          P ≤ longSub 6 (hexGroup (twistedX σ))) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨t, htord⟩ := exists_unit_of_orderOf hr hK (by omega) hrd
  have htr : (t : K) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← htord, pow_orderOf_eq_one, Units.val_one]
  have hnorm : (t : K) * σ t * σ (σ t) = 1 := by
    obtain ⟨k, hk⟩ := hrd
    have e : (t : K) * σ t * σ (σ t) = (t : K) ^ (q ^ 2 + q + 1) := by
      rw [hσq, hσq, ← pow_mul]
      rw [← pow_succ', ← pow_add]
      congr 1
      ring
    rw [e, hk, pow_mul, htr, one_pow]
  have hr2 : r ≠ 2 := odd_of_dvd_phi3 hr hrd
  have ht1 : (t : K) ≠ 1 := by
    intro h
    have : t = 1 := Units.ext h
    rw [this, orderOf_one] at htord
    exact hr.one_lt.ne htord
  have ht2 : (t : K) ^ 2 ≠ 1 := by
    intro h
    have h' : t ^ 2 = 1 := Units.ext (by simpa using h)
    have := orderOf_dvd_of_pow_eq_one h'
    rw [htord] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  have htr' : t ^ r = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
  have hzpow : (slShort σ hσ (HSL t)) ^ r = 1 := by
    rw [← map_pow, CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_pow, htr',
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_one', map_one]
  have hz1 : slShort σ hσ (HSL t) ≠ 1 := by
    intro h
    have h1 := slShort_HSL_fix_d4X_zero hσ t ht2 (1 : K) (by rw [h]; simp)
    have h2 : d4X hσ 0 (1 : K) = d4X hσ 0 (0 : K) := h1.trans (d4X_zero_zero hσ).symm
    have h3 : (1 : K) = 0 := d4X_injective hσ 0 h2
    exact one_ne_zero h3
  have hzord : orderOf (slShort σ hσ (HSL t)) = r := orderOf_eq_prime hzpow hz1
  have hFcard : Nat.card (fixedField σ) = q := card_fixedField_of_cube σ hq hK hσq
  have : Finite (fixedField σ) := Subtype.finite
  have : Module.Finite (fixedField σ) K := Module.Finite.of_finite
  have hfin : Module.finrank (fixedField σ) K = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := fixedField σ) (V := K)
    rw [hK, hFcard] at h
    exact (Nat.pow_right_injective hq h).symm
  have hrq : ¬ r ∣ Nat.card (fixedField σ) - 1 := by
    rw [hFcard]
    exact not_dvd_pred_of_dvd_phi3 hr hr3 (by omega) hrd
  obtain ⟨m, hmr, hmc, hmcomm⟩ := exists_singer_matrix hfin hr hrq (t : K) htr ht1
  obtain ⟨ρ, hrange, hker⟩ := exists_sl3_range hσ
  have hr3' : ¬ r ∣ 3 := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)
  have hcop : Nat.Coprime 3 r := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hr).2 hr3')
  have hcen3 : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (fixedField σ),
      g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (fixedField σ)) → g ^ 3 = 1 := by
    intro g hg
    obtain ⟨l, hl, hlg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
    simp only [Fintype.card_fin] at hl
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hlg, ← map_pow, hl, map_one]
    rfl
  have hcL : ρ m ∈ longSub 6 (hexGroup (twistedX σ)) := by
    rw [← hrange]; exact ⟨m, rfl⟩
  have hcr : (ρ m) ^ r = 1 := by rw [← map_pow, hmr, map_one]
  have hc1 : ρ m ≠ 1 := fun h => hmc (hker (MonoidHom.mem_ker.2 h))
  have hcord : orderOf (ρ m) = r := orderOf_eq_prime hcr hc1
  refine ⟨t, ρ m, hnorm, htord, hzord, hcord, hcL, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1
      (longSub_le_centralizer_slShort_HSL hσ t hnorm hl)
  · intro θ hθ hcent
    have hq3 := SpecialLinear.isQuasisimple 2 (fixedField σ) le_rfl
    have hφker : (ρ.rangeRestrict).ker ≤ Subgroup.center SL(3, fixedField σ) := by
      rw [MonoidHom.ker_rangeRestrict]; exact hker
    have hcenter := center_eq_map_center_of_isQuasisimple hq3 ρ.rangeRestrict_surjective hφker
    have hθr : θ ∈ ρ.range := by rw [hrange]; exact hθ
    have hcentθ : (⟨θ, hθr⟩ : ↥ρ.range) ∈ Subgroup.center ↥ρ.range := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hg : (g : twistedGroup σ) ∈ longSub 6 (hexGroup (twistedX σ)) := by
        rw [← hrange]; exact g.2
      exact (hcent _ hg).symm
    rw [hcenter] at hcentθ
    obtain ⟨g, hg, hgφ⟩ := hcentθ
    have hθg : ρ g = θ := congrArg Subtype.val hgφ
    rw [← hθg, ← map_pow, hcen3 g hg, map_one]
  · intro a ha b hb hac hbc
    have key : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (fixedField σ),
        ρ g * ρ m = ρ m * ρ g → g * m = m * g := by
      intro g hg
      set k := g * m * g⁻¹ * m⁻¹ with hkdef
      have hk : k ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, hkdef]
        simp only [map_mul, map_inv]
        rw [hg]
        group
      have hkc := hker hk
      have hkcomm : ∀ x, x * k = k * x := Subgroup.mem_center_iff.1 hkc
      have hgm : g * m * g⁻¹ = k * m := by rw [hkdef]; group
      have h1 : (g * m * g⁻¹) ^ r = 1 := by rw [conj_pow, hmr]; group
      have h2 : (k * m) ^ r = k ^ r := by
        rw [Commute.mul_pow (show Commute k m from (hkcomm m).symm), hmr, mul_one]
      have hkr : k ^ r = 1 := by rw [← h2, ← hgm]; exact h1
      have hk3 := hcen3 k hkc
      have hk1 : k = 1 := by
        have := (pow_gcd_eq_one (a := k)).2 ⟨hk3, hkr⟩
        rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
      rw [hk1] at hgm
      have : g * m = m * g := by
        rw [one_mul] at hgm
        exact mul_inv_eq_iff_eq_mul.1 hgm
      exact this
    obtain ⟨γ, rfl⟩ : a ∈ ρ.range := by rw [hrange]; exact ha
    obtain ⟨δ, rfl⟩ : b ∈ ρ.range := by rw [hrange]; exact hb
    have hγ := key γ hac
    have hδ := key δ hbc
    rw [← map_mul, ← map_mul, hmcomm γ δ hγ hδ]
  · intro P hP hPz
    exact perfect_le_longSub_of_le_centralizer hσ hcen t hnorm ht2 hP hPz

end UBPlaneData

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
