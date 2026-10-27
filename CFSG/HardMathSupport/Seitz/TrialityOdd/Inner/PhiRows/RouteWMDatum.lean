module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJTwisted
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWNoPlaneJ
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6ClosingCore
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCentralizer

set_option linter.unusedSectionVars false

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

section Abstract

variable {G : Type*} [Group G]

theorem not_both_stabilize_line {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {c a b w : G}
    (hcr : c ^ r = 1) (hc1 : c ≠ 1) (hw : w * c * w⁻¹ = c⁻¹) (hab : a * b * a⁻¹ * b⁻¹ = w)
    (ha : a * c * a⁻¹ ∈ zpowers c) (hb : b * c * b⁻¹ ∈ zpowers c) : False := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hconj : ∀ (x : G) (k : ℤ), x * c ^ k * x⁻¹ = (x * c * x⁻¹) ^ k := fun x k => by
    simp
  have hwk : ∀ k : ℤ, w * c ^ k * w⁻¹ = (c ^ k)⁻¹ := fun k => by
    rw [hconj w k, hw, inv_zpow]
  have e1 : a * b * c * (a * b)⁻¹ = c ^ (j * i) := by
    calc a * b * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
      _ = a * c ^ j * a⁻¹ := by rw [← hj]
      _ = (a * c * a⁻¹) ^ j := hconj a j
      _ = c ^ (i * j) := by rw [← hi, ← zpow_mul]
      _ = c ^ (j * i) := by rw [mul_comm]
  have e2 : b * a * c * (b * a)⁻¹ = c ^ (i * j) := by
    calc b * a * c * (b * a)⁻¹ = b * (a * c * a⁻¹) * b⁻¹ := by group
      _ = b * c ^ i * b⁻¹ := by rw [← hi]
      _ = (b * c * b⁻¹) ^ i := hconj b i
      _ = c ^ (j * i) := by rw [← hj, ← zpow_mul]
      _ = c ^ (i * j) := by rw [mul_comm]
  have hab' : a * b = w * (b * a) := by
    have : w * (b * a) = a * b := by
      rw [← hab]; group
    exact this.symm
  have e3 : a * b * c * (a * b)⁻¹ = (c ^ (i * j))⁻¹ := by
    rw [hab', mul_inv_rev]
    calc w * (b * a) * c * ((b * a)⁻¹ * w⁻¹) = w * ((b * a) * c * (b * a)⁻¹) * w⁻¹ := by group
      _ = w * c ^ (i * j) * w⁻¹ := by rw [e2]
      _ = (c ^ (i * j))⁻¹ := hwk _
  rw [e1, mul_comm j i] at e3
  have e4 : c ^ (2 * (i * j)) = 1 := by
    have : c ^ (i * j) = (c ^ (i * j))⁻¹ := e3
    rw [two_mul, zpow_add]
    nth_rewrite 1 [this]
    simp
  have hord : orderOf c = r := by
    have hdvd : orderOf c ∣ r := orderOf_dvd_of_pow_eq_one hcr
    rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hc1
    · exact h
  have hr_dvd : (r : ℤ) ∣ 2 * (i * j) := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 e4
  have hrp : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  have hr2' : ¬ (r : ℤ) ∣ 2 := by
    intro h
    have := Int.natCast_dvd_natCast.1 (by exact_mod_cast h : (r : ℤ) ∣ ((2 : ℕ) : ℤ))
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  have hij : (r : ℤ) ∣ i * j := (hrp.dvd_or_dvd hr_dvd).resolve_left hr2'
  have hone : ∀ k : ℤ, (r : ℤ) ∣ k → c ^ k = 1 := fun k hk =>
    orderOf_dvd_iff_zpow_eq_one.1 (by rw [hord]; exact hk)
  rcases hrp.dvd_or_dvd hij with h | h
  · have : a * c * a⁻¹ = 1 := by rw [← hi]; exact hone i h
    exact hc1 (mul_left_cancel ((mul_inv_eq_one.1 this).trans (mul_one a).symm))
  · have : b * c * b⁻¹ = 1 := by rw [← hj]; exact hone j h
    exact hc1 (mul_left_cancel ((mul_inv_eq_one.1 this).trans (mul_one b).symm))

theorem closure_pair_eq {r : ℕ} (hr : r.Prime) {E : Subgroup G} {c c' : G} (hcE : c ∈ E)
    (hc'E : c' ∈ E) (hexp : ∀ x ∈ E, x ^ r = 1) (hcard : Nat.card E = r ^ 2) (hc1 : c ≠ 1)
    (hc' : c' ∉ zpowers c) : closure ({c, c'} : Set G) = E := by
  have hle : closure ({c, c'} : Set G) ≤ E := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact hcE
    · exact hc'E
  have hord : orderOf c = r := by
    have hdvd : orderOf c ∣ r := orderOf_dvd_of_pow_eq_one (hexp c hcE)
    rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hc1
    · exact h
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hr.ne_zero)
  have hfinC : Finite (closure ({c, c'} : Set G)) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hZ : zpowers c ≤ closure ({c, c'} : Set G) :=
    zpowers_le.2 (subset_closure (by simp))
  have hZcard : Nat.card (zpowers c) = r := by rw [Nat.card_zpowers, hord]
  have hdvd1 : Nat.card (closure ({c, c'} : Set G)) ∣ r ^ 2 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hdvd2 : r ∣ Nat.card (closure ({c, c'} : Set G)) := by
    rw [← hZcard]
    exact Subgroup.card_dvd_of_le hZ
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hr).1 hdvd1
  have hk1 : k ≠ 1 := by
    rintro rfl
    have h1 : Nat.card (closure ({c, c'} : Set G)) ≤ Nat.card (zpowers c) := by
      rw [hkc, hZcard, pow_one]
    have h2 := Subgroup.eq_of_le_of_card_ge hZ h1
    exact hc' (h2 ▸ subset_closure (by simp))
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : r ∣ 1 := by simpa [hkc] using hdvd2
    exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  have hk2 : k = 2 := by omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hkc, hk2, hcard]

end Abstract

section Main

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.ClassicalInvolution.G2D4Models
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem M_le_of_phi6_datum
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hq5 : 5 ≤ ℓ ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrq : r ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1)
    (E₀ : Subgroup (twistedGroup σ.toRingHom)) (hexp : ∀ x ∈ E₀, x ^ r = 1)
    (hcard : Nat.card E₀ = r ^ 2) (w : twistedGroup σ.toRingHom)
    (hinv : ∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹) (g : twistedGroup σ.toRingHom)
    (hg : g * w * g⁻¹ = slLong σ.toRingHom hσ (-1))
    (D : Subgroup (twistedGroup σ.toRingHom)) (hDs : IsSimpleGroup D) (hDperf : ⁅D, D⁆ = D)
    (hDc : Nat.card D = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) / 2) (hDw : ∀ x ∈ D, x * w = w * x)
    (hDJ : ∀ x ∈ D, g * x * g⁻¹ ∈ JTw σ.toRingHom)
    (c : twistedGroup σ.toRingHom) (hcE : c ∈ E₀) (hc1 : c ≠ 1)
    (hcJ : g * c * g⁻¹ ∈ JTw σ.toRingHom) (a b : twistedGroup σ.toRingHom)
    (haE : ∀ x ∈ E₀, a * x * a⁻¹ ∈ E₀) (hbE : ∀ x ∈ E₀, b * x * b⁻¹ ∈ E₀)
    (haM : g * a * g⁻¹ ∈ invCentGroup σ.toRingHom hσ)
    (hbM : g * b * g⁻¹ ∈ invCentGroup σ.toRingHom hσ) (hab : a * b * a⁻¹ * b⁻¹ = w) :
    ∃ ν, (ν = a ∨ ν = b) ∧
      (invCentGroup σ.toRingHom hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤
        D ⊔ D.map (MulAut.conj ν).toMonoidHom := by
  classical
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hKm : (-1 : Kˣ) ≠ 1 := by
    intro h
    apply h2K
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hrange := range_twistedIncl_eq_of_card (σ := σ.toRingHom) hK2 hq2 hK hσq
  have hC₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤
      (twistedIncl σ.toRingHom).range := hrange.ge
  have hgF : ∀ y : twistedGroup σ.toRingHom,
      twistedIncl σ.toRingHom y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun y => hrange ▸ ⟨y, rfl⟩
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => hσ c
  set τ := slLong σ.toRingHom hσ (-1) with hτ
  set D' : Subgroup (twistedGroup σ.toRingHom) := D.map (MulAut.conj g).toMonoidHom with hD'
  have hD'simple : IsSimpleGroup D' :=
    MulEquiv.isSimpleGroup (Subgroup.equivMapOfInjective D (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  have hD'card : Nat.card D' = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) / 2 := by
    rw [← hDc]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective D (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  have hD'J : D' ≤ JTw σ.toRingHom := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDJ x hx
  have hD'perf : ⁅D', D'⁆ = D' := by
    rw [hD', ← Subgroup.map_commutator, hDperf]
  have hD'τ : ∀ y ∈ D', y * τ = τ * y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg]
    have := hDw x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [this]
      _ = g * w * g⁻¹ * (g * x * g⁻¹) := by group
  have hD'M : D' ≤ invCentGroup σ.toRingHom hσ :=
    perfect_centralizer_le_invCentGroup hσ hKm hC₀ hgF hD'τ hD'perf
  have transport : ∀ ν : twistedGroup σ.toRingHom,
      invCentGroup σ.toRingHom hσ ≤ D' ⊔ D'.map (MulAut.conj (g * ν * g⁻¹)).toMonoidHom →
      (invCentGroup σ.toRingHom hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤
        D ⊔ D.map (MulAut.conj ν).toMonoidHom := by
    intro ν h
    rintro _ ⟨m, hm, rfl⟩
    have hm' := h hm
    have hle : D' ⊔ D'.map (MulAut.conj (g * ν * g⁻¹)).toMonoidHom ≤
        (D ⊔ D.map (MulAut.conj ν).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      refine sup_le ?_ ?_
      · exact Subgroup.map_mono le_sup_left
      · rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
        refine ⟨ν * d * ν⁻¹,
          (le_sup_right : D.map (MulAut.conj ν).toMonoidHom ≤ D ⊔ D.map (MulAut.conj ν).toMonoidHom)
            ⟨d, hd, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    obtain ⟨y, hy, hym⟩ := hle hm'
    have : (MulAut.conj g⁻¹).toMonoidHom m = y := by
      rw [← hym]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  have hJ_or : ∀ ν : twistedGroup σ.toRingHom, g * ν * g⁻¹ ∈ invCentGroup σ.toRingHom hσ →
      g * ν * g⁻¹ ∉ JTw σ.toRingHom →
      (invCentGroup σ.toRingHom hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤
        D ⊔ D.map (MulAut.conj ν).toMonoidHom := by
    intro ν hνM hνJ
    rcases goursatJ_twisted hℓ hℓ2 hf hq5 hK σ hσq hσ D' hD'simple hD'card hD'M hD'J
      (g * ν * g⁻¹) hνM with h | h
    · exact absurd h hνJ
    · exact transport ν h
  by_cases hJa : g * a * g⁻¹ ∈ JTw σ.toRingHom
  · by_cases hJb : g * b * g⁻¹ ∈ JTw σ.toRingHom
    · exfalso
      have hwc : w * c * w⁻¹ = c⁻¹ := hinv c hcE
      have hnot : ¬ (a * c * a⁻¹ ∈ zpowers c ∧ b * c * b⁻¹ ∈ zpowers c) := fun ⟨h1, h2⟩ =>
        not_both_stabilize_line hr (by omega) (hexp c hcE) hc1 hwc hab h1 h2
      have hplane : ∃ c'' ∈ E₀, c'' ∉ zpowers c ∧ g * c'' * g⁻¹ ∈ JTw σ.toRingHom := by
        by_cases h1 : a * c * a⁻¹ ∈ zpowers c
        · refine ⟨b * c * b⁻¹, hbE c hcE, fun h2 => hnot ⟨h1, h2⟩, ?_⟩
          have : g * (b * c * b⁻¹) * g⁻¹ =
              (g * b * g⁻¹) * (g * c * g⁻¹) * (g * b * g⁻¹)⁻¹ := by group
          rw [this]
          exact mul_mem (mul_mem hJb hcJ) (inv_mem hJb)
        · refine ⟨a * c * a⁻¹, haE c hcE, h1, ?_⟩
          have : g * (a * c * a⁻¹) * g⁻¹ =
              (g * a * g⁻¹) * (g * c * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
          rw [this]
          exact mul_mem (mul_mem hJa hcJ) (inv_mem hJa)
      obtain ⟨c'', hc''E, hc''Z, hc''J⟩ := hplane
      have hE0 := closure_pair_eq hr hcE hc''E hexp hcard hc1 hc''Z
      have hEJ : E₀.map (MulAut.conj g).toMonoidHom ≤ JTw σ.toRingHom := by
        rw [← hE0, MonoidHom.map_closure]
        refine closure_le _ |>.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl
        · exact hcJ
        · exact hc''J
      refine no_plane_in_JTw hℓ hℓ2 hf (by omega) hK σ hσq hσ3 hr hr5 hrq
        (E₀.map (MulAut.conj g).toMonoidHom) hEJ ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hexp x hx, map_one]
      · rw [← hcard]
        exact (Nat.card_congr (Subgroup.equivMapOfInjective E₀ (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toEquiv).symm
    · exact ⟨b, Or.inr rfl, hJ_or b hbM hJb⟩
  · exact ⟨a, Or.inl rfl, hJ_or a haM hJa⟩

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
