module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6TorusFull
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.InvolConjTransport
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore
public import CFSG.Dihedral.Glauberman.DicksonMaxTrace

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup TauCeti CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.TwistedD4
  CFSG.ClassicalInvolution.G2D4Models CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open scoped MatrixGroups

@[expose] def TwoTorusGen (K : Type) [Field K] : Prop :=
  ∀ E₁ D : GL (Fin 2) K, (∀ a : K, ((E₁ : Matrix (Fin 2) (Fin 2) K).charpoly).eval a ≠ 0) →
    (∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) ^ 2 = c • 1) →
    (¬ ∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) = c • 1) →
    (D : Matrix (Fin 2) (Fin 2) K) * E₁ ≠ E₁ * D →
    Subgroup.closure ({B : SL(2, K) | (E₁ : Matrix (Fin 2) (Fin 2) K) * B = B * E₁} ∪
      {B : SL(2, K) | (D : Matrix (Fin 2) (Fin 2) K) * B = B * D}) = ⊤

@[expose] def AnisotropicOfPow (K : Type) [Field K] (r : ℕ) : Prop :=
  ∀ E : GL (Fin 2) K, (∃ c : K, (E : Matrix (Fin 2) (Fin 2) K) ^ r = c • 1) →
    (¬ ∃ c : K, (E : Matrix (Fin 2) (Fin 2) K) = c • 1) →
    ∀ a : K, ((E : Matrix (Fin 2) (Fin 2) K).charpoly).eval a ≠ 0

section GLFacts

variable {K : Type} [Field K]

theorem glConjSL_eq_self_of_scalar {D : GL (Fin 2) K} {c : K}
    (hc : (D : Matrix (Fin 2) (Fin 2) K) = c • 1) (C : SL(2, K)) : glConjSL D C = C := by
  apply Subtype.ext
  rw [glConjSL_coe]
  have hcomm : (D : Matrix (Fin 2) (Fin 2) K) * C = C * D := by
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [hcomm, Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one]

theorem scalar_of_glConjSL_eq_self {D : GL (Fin 2) K} (h : ∀ C : SL(2, K), glConjSL D C = C) :
    ∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
  obtain ⟨c, -, hc⟩ := exists_scalar_of_glConjSL_eq (D := 1) (E := D)
    (fun C => by rw [glConjSL_one, h])
  exact ⟨c, by rw [hc, Units.val_one]⟩

end GLFacts

section Model

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem exists_glConj_of_mem_SProd {z : twistedGroup σ} (hz : z ∈ SProd σ hσ) :
    ∃ D : GL (Fin 2) K, ∀ C : SL(2, K), z * slB σ hσ C * z⁻¹ = slB σ hσ (glConjSL D C) := by
  obtain ⟨t, ht, A, B, rfl⟩ := hz
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, -, hs⟩ := torus_conj_slB hσ hb
  exact ⟨_, pair_prod_conj2 (slLong_comm_slB hσ) hs A B⟩

include hσ in
theorem conj_pow_slB {z : twistedGroup σ} {D : GL (Fin 2) K}
    (hD : ∀ C : SL(2, K), z * slB σ hσ C * z⁻¹ = slB σ hσ (glConjSL D C)) (n : ℕ)
    (C : SL(2, K)) : z ^ n * slB σ hσ C * (z ^ n)⁻¹ = slB σ hσ (glConjSL (D ^ n) C) := by
  induction n generalizing C with
  | zero => simp [glConjSL_one]
  | succ n ih =>
    rw [pow_succ', mul_inv_rev, pow_succ', glConjSL_mul]
    calc z * z ^ n * slB σ hσ C * ((z ^ n)⁻¹ * z⁻¹)
        = z * (z ^ n * slB σ hσ C * (z ^ n)⁻¹) * z⁻¹ := by group
      _ = slB σ hσ (glConjSL D (glConjSL (D ^ n) C)) := by rw [ih, hD]

include hσ in
theorem exists_slLong_of_scalar_action {z : twistedGroup σ} (hz : z ∈ SProd σ hσ)
    {D : GL (Fin 2) K}
    (hD : ∀ C : SL(2, K), z * slB σ hσ C * z⁻¹ = slB σ hσ (glConjSL D C))
    (hs : ∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) = c • 1) :
    ∃ A : SL(2, fixedField σ), z = slLong σ hσ A := by
  obtain ⟨c, hc⟩ := hs
  refine exists_slLong_of_centralizes_slB hσ hz fun C => ?_
  have h := hD C
  rw [glConjSL_eq_self_of_scalar hc] at h
  calc z * slB σ hσ C = z * slB σ hσ C * z⁻¹ * z := by group
    _ = slB σ hσ C * z := by rw [h]

include hσ in
theorem scalar_pow_of_pow_eq_one {z : twistedGroup σ} {D : GL (Fin 2) K}
    (hD : ∀ C : SL(2, K), z * slB σ hσ C * z⁻¹ = slB σ hσ (glConjSL D C)) {n : ℕ}
    (hn : z ^ n = 1) : ∃ c : K, ((D ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
  refine scalar_of_glConjSL_eq_self fun C => ?_
  apply slB_injective hσ
  rw [← conj_pow_slB hσ hD n C, hn]
  group

end Model

section Group

variable {G : Type*} [Group G]

theorem mem_conj_map_iff {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_centralizer_conj_iff {g c y : G} :
    y ∈ Subgroup.centralizer ({g * c * g⁻¹} : Set G) ↔
      g⁻¹ * y * g ∈ Subgroup.centralizer ({c} : Set G) := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * y * g * c = g⁻¹ * (y * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * y) * g := by rw [h]
      _ = c * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * y := by group

theorem rclosure_map_conj {r : ℕ} {H : Subgroup G}
    (hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 → Subgroup.centralizer ({c} : Set G) ≤ H) (g : G) :
    ∀ c ∈ H.map (MulAut.conj g).toMonoidHom, c ^ r = 1 → c ≠ 1 →
      Subgroup.centralizer ({c} : Set G) ≤ H.map (MulAut.conj g).toMonoidHom := by
  intro c hc hcr hc1 y hy
  rw [mem_conj_map_iff] at hc ⊢
  have hc0r : (g⁻¹ * c * g) ^ r = 1 := by
    rw [show g⁻¹ * c * g = g⁻¹ * c * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hcr]; group
  have hc01 : g⁻¹ * c * g ≠ 1 := fun h => hc1 (by
    calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  apply hR _ hc hc0r hc01
  have hy' : y ∈ Subgroup.centralizer ({g * (g⁻¹ * c * g) * g⁻¹} : Set G) := by
    rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group]
  exact mem_centralizer_conj_iff.1 hy'

theorem eq_one_of_pow_two_of_pow_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : G}
    (h2 : x ^ 2 = 1) (hr' : x ^ r = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h2' : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hr'
  have hcop : Nat.Coprime 2 r :=
    (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2)
  have : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h1 h2'
    rwa [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem eq_one_of_pow_prime_of_not_dvd [Finite G] {r : ℕ} (hr : r.Prime) {x : G}
    (hx : x ^ r = 1) (hrG : ¬ r ∣ Nat.card G) : x = 1 := by
  rcases (Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hx) with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ orderOf_dvd_natCard x) hrG

end Group

section SL2

variable {F : Type} [Field F] [Finite F]

theorem SL2_eq_one_or_neg_one_of_mul_self (h2 : (2 : F) ≠ 0) {A : SL(2, F)} (hA : A * A = 1) :
    A = 1 ∨ A = -1 :=
  CFSG.Glauberman.Dickson.MaxTrace.eq_one_or_neg_of_mul_self h2 hA

end SL2

section Main

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem range_twistedIncl_eq_of_card (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    (twistedIncl σ).range = graphFixedRootGroup TwistTag.D4 K σ := by
  rw [twistedIncl, MonoidHom.range_comp, Subgroup.range_subtype]
  exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
    hK2 hq hK hσq

include hσ in
theorem centralizer_tauL_le (hK2 : ringChar K ≠ 2) (hKm : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ ringChar K)
    (hrK2 : r ∣ Nat.card K ^ 2 - 1) {H : Subgroup (twistedGroup σ)}
    (hM : invCentGroup σ hσ ≤ H)
    (hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 → Subgroup.centralizer ({c} : Set (twistedGroup σ)) ≤ H) :
    Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) ≤ H := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨m₀, hm₀⟩ := exists_orderOf_eq_prime_SL2 (K := K) hrK2
  have hc : slB σ hσ m₀ ∈ H := hM (Subgroup.mem_sup_right ⟨m₀, rfl⟩)
  have hcr : slB σ hσ m₀ ^ r = 1 := by rw [← map_pow, ← hm₀, pow_orderOf_eq_one, map_one]
  have hc1 : slB σ hσ m₀ ≠ 1 := by
    intro h
    have : m₀ = 1 := slB_injective hσ (by rw [h, map_one])
    rw [this, orderOf_one] at hm₀
    exact hr.one_lt.ne hm₀
  have htr := trace_sq_ne_four_of_orderOf hr hr2 hrp hm₀
  have hSP := SProd_le_of_invCentGroup_le hσ hK2 hM htr (hR _ hc hcr hc1)
  intro y hy
  exact hSP (mem_SProd_of_centralizes hσ hKm hC₀ hgF
    (Subgroup.mem_centralizer_singleton_iff.1 hy))

include hσ in
theorem centralizer_le_of_core (hK2 : ringChar K ≠ 2) (hKm : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ ringChar K)
    (hrK2 : r ∣ Nat.card K ^ 2 - 1) {H : Subgroup (twistedGroup σ)}
    (hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 → Subgroup.centralizer ({c} : Set (twistedGroup σ)) ≤ H)
    {v g : twistedGroup σ} (hg : g * v * g⁻¹ = slLong σ hσ (-1))
    (hM : (invCentGroup σ hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤ H) :
    Subgroup.centralizer ({v} : Set (twistedGroup σ)) ≤ H := by
  set H' := H.map (MulAut.conj g).toMonoidHom with hH'
  have hM' : invCentGroup σ hσ ≤ H' := by
    intro m hm
    rw [hH', mem_conj_map_iff]
    apply hM
    rw [mem_conj_map_iff, inv_inv]
    simpa [mul_assoc] using hm
  have hCτ := centralizer_tauL_le hσ hK2 hKm hC₀ hgF hr hr2 hrp hrK2 hM'
    (rclosure_map_conj hR g)
  intro y hy
  have hy' : g * y * g⁻¹ ∈ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) := by
    rw [← hg, mem_centralizer_conj_iff]
    simpa [mul_assoc] using hy
  have := hCτ hy'
  rw [hH', mem_conj_map_iff] at this
  simpa [mul_assoc] using this

include hσ in
theorem conj_inv_slB {z : twistedGroup σ} {D : GL (Fin 2) K}
    (hD : ∀ C : SL(2, K), z * slB σ hσ C * z⁻¹ = slB σ hσ (glConjSL D C)) (C : SL(2, K)) :
    z⁻¹ * slB σ hσ C * z = slB σ hσ (glConjSL D⁻¹ C) := by
  have h := hD (glConjSL D⁻¹ C)
  rw [← glConjSL_mul, mul_inv_cancel, glConjSL_one] at h
  rw [← h]
  group

include hσ in
theorem eq_top_of_core {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσq : ∀ c, σ c = c ^ (p ^ f))
    (hDT : TwoTorusGen K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hrK2 : r ∣ Nat.card K ^ 2 - 1) (hrF : ¬ r ∣ Nat.card (SL(2, fixedField σ)))
    (hAn : AnisotropicOfPow K r) {H : Subgroup (twistedGroup σ)}
    (hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 → Subgroup.centralizer ({c} : Set (twistedGroup σ)) ≤ H)
    {w g : twistedGroup σ} (hw2 : w * w = 1) (hg : g * w * g⁻¹ = slLong σ hσ (-1))
    (hM : (invCentGroup σ hσ).map (MulAut.conj g⁻¹).toMonoidHom ≤ H)
    {x₁ u : twistedGroup σ} (hx₁H : x₁ ∈ H) (hx₁r : x₁ ^ r = 1) (hx₁1 : x₁ ≠ 1)
    (hwx : w * x₁ * w⁻¹ = x₁⁻¹) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huw : u * w = w * u)
    (hux : u * x₁ = x₁ * u) : H = ⊤ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hKm : (-1 : Kˣ) ≠ 1 := by
    intro h
    apply h2K
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have h7 : 7 ≤ Nat.card K := by
    rw [hK]
    calc 7 ≤ 2 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq2 3
  have hrange := range_twistedIncl_eq_of_card (σ := σ) hK2 hq2 hK hσq
  have hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range := hrange.ge
  have hgF : ∀ y : twistedGroup σ, twistedIncl σ y ∈ graphFixedRootGroup TwistTag.D4 K σ :=
    fun y => hrange ▸ ⟨y, rfl⟩
  have hrpK : r ≠ ringChar K := by rw [ringChar.eq K p]; exact hrp
  have h2F : (2 : fixedField σ) ≠ 0 := by
    intro h
    apply h2K
    have := congrArg (fixedField σ).subtype h
    rwa [map_ofNat, map_zero] at this
  have hτ2 : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : slLong σ hσ (-1) ≠ 1 := by
    intro h
    have h' : (-1 : SL(2, fixedField σ)) = 1 := slLong_injective hσ (by rw [h, map_one])
    exact neg_one_ne_one_SL2_of_two_ne_zero h2F h'
  have hconj : ∀ v : twistedGroup σ, v * v = 1 → v ≠ 1 →
      ∃ g : twistedGroup σ, g * v * g⁻¹ = slLong σ hσ (-1) := fun v hv hv1 =>
    exists_conj_eq_of_involutions_td4 hp hp2 hf K hK σ hσq hv hτ2 hv1 hτ1
  have hx₁inv : x₁ ≠ x₁⁻¹ := by
    intro h
    apply hx₁1
    refine eq_one_of_pow_two_of_pow_prime hr hr2 ?_ hx₁r
    calc x₁ ^ 2 = x₁ * x₁ := sq x₁
      _ = x₁ * x₁⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel x₁
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, one_mul, inv_one, mul_one] at hwx
    exact hx₁inv hwx
  have huw' : u ≠ w := by
    intro h
    rw [← h] at hwx
    apply hx₁inv
    rw [← hwx, hux]
    group
  have hCw := centralizer_le_of_core hσ hK2 hKm hC₀ hgF hr hr2 hrpK hrK2 hR hg hM
  obtain ⟨g₂, hg₂⟩ := hconj u hu2 hu1
  set H₂ := H.map (MulAut.conj g₂).toMonoidHom with hH₂
  have hR₂ := rclosure_map_conj hR g₂
  set τ := slLong σ hσ (-1) with hτ
  set w₂ := g₂ * w * g₂⁻¹ with hw₂
  set x₂ := g₂ * x₁ * g₂⁻¹ with hx₂
  have hw₂τ : w₂ * τ = τ * w₂ := by
    rw [hw₂, ← hg₂]
    calc g₂ * w * g₂⁻¹ * (g₂ * u * g₂⁻¹) = g₂ * (w * u) * g₂⁻¹ := by group
      _ = g₂ * (u * w) * g₂⁻¹ := by rw [huw]
      _ = g₂ * u * g₂⁻¹ * (g₂ * w * g₂⁻¹) := by group
  have hx₂τ : x₂ * τ = τ * x₂ := by
    rw [hx₂, ← hg₂]
    calc g₂ * x₁ * g₂⁻¹ * (g₂ * u * g₂⁻¹) = g₂ * (x₁ * u) * g₂⁻¹ := by group
      _ = g₂ * (u * x₁) * g₂⁻¹ := by rw [hux]
      _ = g₂ * u * g₂⁻¹ * (g₂ * x₁ * g₂⁻¹) := by group
  have hw₂S : w₂ ∈ SProd σ hσ := mem_SProd_of_centralizes hσ hKm hC₀ hgF hw₂τ
  have hx₂S : x₂ ∈ SProd σ hσ := mem_SProd_of_centralizes hσ hKm hC₀ hgF hx₂τ
  have hw₂2 : w₂ ^ 2 = 1 := by
    rw [sq, hw₂]
    calc g₂ * w * g₂⁻¹ * (g₂ * w * g₂⁻¹) = g₂ * (w * w) * g₂⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  have hx₂r : x₂ ^ r = 1 := by rw [hx₂, conj_pow, hx₁r]; group
  have hx₂1 : x₂ ≠ 1 := by
    intro h
    apply hx₁1
    calc x₁ = g₂⁻¹ * x₂ * g₂ := by rw [hx₂]; group
      _ = 1 := by rw [h]; group
  have hwx₂ : w₂ * x₂ * w₂⁻¹ = x₂⁻¹ := by
    rw [hw₂, hx₂]
    calc g₂ * w * g₂⁻¹ * (g₂ * x₁ * g₂⁻¹) * (g₂ * w * g₂⁻¹)⁻¹ = g₂ * (w * x₁ * w⁻¹) * g₂⁻¹ := by
          group
      _ = (g₂ * x₁ * g₂⁻¹)⁻¹ := by rw [hwx]; group
  obtain ⟨D, hD⟩ := exists_glConj_of_mem_SProd hσ hw₂S
  obtain ⟨E, hE⟩ := exists_glConj_of_mem_SProd hσ hx₂S
  have hFfin : Finite (SL(2, fixedField σ)) := by
    have := Fintype.ofFinite K
    have : Finite (fixedField σ) := Subtype.finite
    have := Fintype.ofFinite (fixedField σ)
    infer_instance
  have hAr : ∀ A : SL(2, fixedField σ), A ^ r = 1 → A = 1 := fun A hA =>
    eq_one_of_pow_prime_of_not_dvd hr hA hrF
  have hD2 : ∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) ^ 2 = c • 1 := by
    obtain ⟨c, hc⟩ := scalar_pow_of_pow_eq_one hσ hD hw₂2
    exact ⟨c, by rwa [Units.val_pow_eq_pow_val] at hc⟩
  have hDs : ¬ ∃ c : K, (D : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
    intro hs
    obtain ⟨A, hA⟩ := exists_slLong_of_scalar_action hσ hw₂S hD hs
    have hAA : A * A = 1 := by
      apply slLong_injective hσ
      rw [map_mul, ← hA, map_one, ← sq]
      exact hw₂2
    rcases SL2_eq_one_or_neg_one_of_mul_self h2F hAA with h | h
    · apply hw1
      have : w₂ = 1 := by rw [hA, h, map_one]
      calc w = g₂⁻¹ * w₂ * g₂ := by rw [hw₂]; group
        _ = 1 := by rw [this]; group
    · apply huw'
      have : w₂ = g₂ * u * g₂⁻¹ := by rw [hA, h, hg₂]
      have h' : g₂ * w * g₂⁻¹ = g₂ * u * g₂⁻¹ := this
      have := mul_right_cancel (mul_left_cancel h')
      exact this.symm
  have hEpow : ∃ c : K, (E : Matrix (Fin 2) (Fin 2) K) ^ r = c • 1 := by
    obtain ⟨c, hc⟩ := scalar_pow_of_pow_eq_one hσ hE hx₂r
    exact ⟨c, by rwa [Units.val_pow_eq_pow_val] at hc⟩
  have hEs : ¬ ∃ c : K, (E : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
    intro hs
    obtain ⟨A, hA⟩ := exists_slLong_of_scalar_action hσ hx₂S hE hs
    apply hx₂1
    rw [hA, hAr A (slLong_injective hσ (by rw [map_pow, ← hA, hx₂r, map_one])), map_one]
  have hEan := hAn E hEpow hEs
  have hDE : (D : Matrix (Fin 2) (Fin 2) K) * E ≠ E * D := by
    intro hcomm
    have hDEg : D * E = E * D := Units.ext hcomm
    have hDED : D * E * D⁻¹ = E := by rw [hDEg, mul_assoc, mul_inv_cancel, mul_one]
    have hEE : ∀ C : SL(2, K), glConjSL E⁻¹ C = glConjSL E C := by
      intro C
      apply slB_injective hσ
      calc slB σ hσ (glConjSL E⁻¹ C) = x₂⁻¹ * slB σ hσ C * x₂⁻¹⁻¹ := by
            rw [inv_inv, conj_inv_slB hσ hE C]
        _ = (w₂ * x₂ * w₂⁻¹) * slB σ hσ C * (w₂ * x₂ * w₂⁻¹)⁻¹ := by rw [hwx₂]
        _ = w₂ * (x₂ * (w₂⁻¹ * slB σ hσ C * w₂) * x₂⁻¹) * w₂⁻¹ := by group
        _ = w₂ * (x₂ * slB σ hσ (glConjSL D⁻¹ C) * x₂⁻¹) * w₂⁻¹ := by
            rw [conj_inv_slB hσ hD C]
        _ = w₂ * slB σ hσ (glConjSL E (glConjSL D⁻¹ C)) * w₂⁻¹ := by rw [hE]
        _ = slB σ hσ (glConjSL D (glConjSL E (glConjSL D⁻¹ C))) := hD _
        _ = slB σ hσ (glConjSL E C) := by rw [← glConjSL_mul, ← glConjSL_mul, hDED]
    have hsq : ∀ C : SL(2, K), x₂ ^ 2 * slB σ hσ C = slB σ hσ C * x₂ ^ 2 := by
      intro C
      have h := conj_pow_slB hσ hE 2 C
      rw [sq E, glConjSL_mul, ← hEE C, ← glConjSL_mul, mul_inv_cancel, glConjSL_one] at h
      calc x₂ ^ 2 * slB σ hσ C = x₂ ^ 2 * slB σ hσ C * (x₂ ^ 2)⁻¹ * x₂ ^ 2 := by group
        _ = slB σ hσ C * x₂ ^ 2 := by rw [h]
    obtain ⟨A, hA⟩ := exists_slLong_of_centralizes_slB hσ (pow_mem hx₂S 2) hsq
    have hA1 : A = 1 := hAr A (slLong_injective hσ (by
      rw [map_pow, ← hA, ← pow_mul, mul_comm, pow_mul, hx₂r, one_pow, map_one]))
    apply hx₂1
    refine eq_one_of_pow_two_of_pow_prime hr hr2 ?_ hx₂r
    rw [hA, hA1, map_one]
  have hgen := hDT E D hEan hD2 hDs hDE
  have hx₂H : x₂ ∈ H₂ := by
    rw [hH₂, mem_conj_map_iff]
    simpa [hx₂, mul_assoc] using hx₁H
  have hCx₂ := hR₂ x₂ hx₂H hx₂r hx₂1
  have hCw₂ : Subgroup.centralizer ({w₂} : Set (twistedGroup σ)) ≤ H₂ := by
    intro y hy
    rw [hH₂, mem_conj_map_iff]
    exact hCw (mem_centralizer_conj_iff.1 hy)
  have hcl : Subgroup.closure
      ({B : SL(2, K) | (E : Matrix (Fin 2) (Fin 2) K) * B = B * E} ∪
        {B : SL(2, K) | (D : Matrix (Fin 2) (Fin 2) K) * B = B * D}) ≤ H₂.comap (slB σ hσ) := by
    rw [Subgroup.closure_le]
    rintro B (hB | hB)
    · show slB σ hσ B ∈ H₂
      apply hCx₂
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : glConjSL E B = B := by
        apply Subtype.ext
        rw [glConjSL_coe, show (E : Matrix (Fin 2) (Fin 2) K) * B = B * E from hB,
          Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one]
      have h := hE B
      rw [hfix] at h
      calc slB σ hσ B * x₂ = x₂ * slB σ hσ B * x₂⁻¹ * x₂ := by rw [h]
        _ = x₂ * slB σ hσ B := by group
    · show slB σ hσ B ∈ H₂
      apply hCw₂
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : glConjSL D B = B := by
        apply Subtype.ext
        rw [glConjSL_coe, show (D : Matrix (Fin 2) (Fin 2) K) * B = B * D from hB,
          Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one]
      have h := hD B
      rw [hfix] at h
      calc slB σ hσ B * w₂ = w₂ * slB σ hσ B * w₂⁻¹ * w₂ := by rw [h]
        _ = w₂ * slB σ hσ B := by group
  have hBle : ∀ B : SL(2, K), slB σ hσ B ∈ H₂ := by
    intro B
    have hB : B ∈ Subgroup.closure
        ({B : SL(2, K) | (E : Matrix (Fin 2) (Fin 2) K) * B = B * E} ∪
          {B : SL(2, K) | (D : Matrix (Fin 2) (Fin 2) K) * B = B * D}) := by
      rw [hgen]; exact Subgroup.mem_top B
    exact hcl hB
  obtain ⟨m₀, hm₀⟩ := exists_orderOf_eq_prime_SL2 (K := K) hrK2
  have hc₀r : slB σ hσ m₀ ^ r = 1 := by rw [← map_pow, ← hm₀, pow_orderOf_eq_one, map_one]
  have hc₀1 : slB σ hσ m₀ ≠ 1 := by
    intro h
    have : m₀ = 1 := slB_injective hσ (by rw [h, map_one])
    rw [this, orderOf_one] at hm₀
    exact hr.one_lt.ne hm₀
  have hCc₀ := hR₂ _ (hBle m₀) hc₀r hc₀1
  have hM₂ : invCentGroup σ hσ ≤ H₂ := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      exact hCc₀ (Subgroup.mem_centralizer_singleton_iff.2 (slLong_comm_slB hσ A m₀))
    · rintro _ ⟨B, rfl⟩
      exact hBle B
  have hCτ := centralizer_tauL_le hσ hK2 hKm hC₀ hgF hr hr2 hrpK hrK2 hM₂ hR₂
  have hCu : Subgroup.centralizer ({u} : Set (twistedGroup σ)) ≤ H := by
    intro y hy
    have hy' : g₂ * y * g₂⁻¹ ∈ Subgroup.centralizer ({τ} : Set (twistedGroup σ)) := by
      rw [← hg₂, mem_centralizer_conj_iff]
      simpa [mul_assoc] using hy
    have := hCτ hy'
    rw [hH₂, mem_conj_map_iff] at this
    simpa [mul_assoc] using this
  have hsup := sup_centralizer_eq_top_td4 hσ hKm h7 hC₀ hgF hconj hu2 hw2 hu1 hw1 huw' huw
  rw [eq_top_iff, ← hsup]
  exact sup_le hCu hCw

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
