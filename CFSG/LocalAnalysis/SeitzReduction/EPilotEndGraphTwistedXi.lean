module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwisted
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Inner

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot

theorem exists_fixed_sum_pow_two_eq_one {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∃ c : K, σ c = c ∧ ∑ i ∈ Finset.range f, c ^ (2 ^ i) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK'])
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hfin : Module.finrank (ZMod 2) K = 2 * f := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK'] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  obtain ⟨b, hb⟩ := Algebra.trace_surjective (ZMod 2) K 1
  have htr := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) K b
  rw [hb, map_one, Nat.card_zmod, hfin] at htr
  refine ⟨b + σ b, ?_, ?_⟩
  · rw [map_add, hσ (σ b), hσ b, ← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card, add_comm]
  · have e : ∀ i, (b + σ b) ^ (2 ^ i) = b ^ (2 ^ i) + b ^ (2 ^ (f + i)) := fun i => by
      rw [add_pow_char_pow, hσ b, ← pow_mul, ← pow_add]
    simp only [e, Finset.sum_add_distrib]
    rw [← Finset.sum_range_add (fun i => b ^ (2 ^ i)) f f, ← two_mul]
    exact htr.symm

section Xi

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem twistedE6_xi_complement (hfe : Even f) :
    ∃ γ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (∀ β ∈ zpowers γ,
        β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* _).range → β = 1) ∧
      (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        ∃ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, ∃ β ∈ zpowers γ,
          α = MulAut.conj g * β) ∧
      ∃ ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
          graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        γ ^ f = MulAut.conj ⟨_, ht⟩ * fieldActor σ σ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK'])
  obtain ⟨Θ, hΘI, hΘF, -, hcard, -, -, -, -⟩ := twistedE6_fieldCoordinate hf K hK σ hσ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hq : 2 ^ f % 3 = 1 := by
    obtain ⟨k, rfl⟩ := hfe
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  obtain ⟨φ, hφ, hordφ, hzφ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * f) hK'
  have hφpow : ∀ (n : ℕ) (c : K), (φ ^ n) c = c ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => intro c; rw [pow_zero, pow_zero, pow_one]; rfl
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm 2 (2 ^ n)]
  have hφf : φ ^ f = σ := RingEquiv.ext fun c => by rw [hφpow, hσ]
  have hφ2f : φ ^ (2 * f) = 1 := by rw [← hordφ, pow_orderOf_eq_one]
  obtain ⟨c, hcσ, hctr⟩ := exists_fixed_sum_pow_two_eq_one hK σ hσ
  obtain ⟨S, hS⟩ : ∃ S : ℕ → K, ∀ n, S n = ∑ i ∈ Finset.range n, (φ ^ i) c :=
    ⟨_, fun _ => rfl⟩
  have hSσ : ∀ n, σ.toRingHom (S n) = S n := fun n => by
    change σ (S n) = _
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (ringEquiv_comm_of_finite σ (φ ^ i) c).symm.trans (congrArg _ hcσ)
  have hmem : ∀ n, pinnedX TwistTag.E6.tag K e6HighestRoot (S n) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := fun n =>
    pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom (S n) (hSσ n)
  obtain ⟨x, hx⟩ : ∃ x : ℕ → graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ∀ n, (x n : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot (S n) :=
    ⟨fun n => ⟨_, hmem n⟩, fun _ => rfl⟩
  have hS0 : S 0 = 0 := by rw [hS, Finset.sum_range_zero]
  have hS1 : S 1 = c := by rw [hS, Finset.sum_range_one, pow_zero]; rfl
  have hSsucc : ∀ n, S (n + 1) = S n + (φ ^ n) c := fun n => by
    rw [hS, hS, Finset.sum_range_succ]
  have hSf : S f = 1 := by
    rw [← hctr, hS]
    exact Finset.sum_congr rfl fun i _ => hφpow i c
  have hS2f : S (2 * f) = 0 := by
    have e : S (2 * f) = S f + S f := by
      rw [hS, hS, two_mul, Finset.sum_range_add]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [pow_add, RingAut.mul_apply, hφf]
        exact (ringEquiv_comm_of_finite σ (φ ^ i) c).symm.trans (congrArg _ hcσ)
    rw [e, CharTwo.add_self_eq_zero]
  have hx0 : x 0 = 1 := Subtype.ext (by rw [hx, hS0, pinnedX_zero]; rfl)
  have hxF : ∀ (δ : K ≃+* K) (n : ℕ),
      ((fieldActor σ δ (x n) : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
        ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot (δ (S n)) :=
    fun δ n => by
      rw [coe_fieldActor, hx]
      exact Units.ext (entrywise_pinnedX δ.toRingHom e6HighestRoot (S n))
  set γ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    MulAut.conj (x 1) * fieldActor σ φ with hγ
  have hγn : ∀ n, γ ^ n = MulAut.conj (x n) * fieldActor σ (φ ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, hx0, map_one, fieldActor_one, mul_one]
    | succ n ih =>
      have hxx : x n * fieldActor σ (φ ^ n) (x 1) = x (n + 1) := Subtype.ext (by
        rw [Subgroup.coe_mul, hxF, hx, hx, ← pinnedX_add, hS1, hSsucc])
      rw [pow_succ, ih, hγ, mul_assoc, ← mul_assoc (fieldActor σ (φ ^ n)), mulAut_mul_conj,
        ← mul_assoc, ← mul_assoc, ← map_mul, hxx, mul_assoc, ← fieldActor_mul, ← pow_succ]
  have hγ2f : γ ^ (2 * f) = 1 := by
    rw [hγn, hφ2f, fieldActor_one, mul_one]
    have : x (2 * f) = 1 := Subtype.ext (by rw [hx, hS2f, pinnedX_zero]; rfl)
    rw [this, map_one]
  have hΘγ : Θ γ = φ := by rw [hγ, map_mul, hΘI, hΘF, one_mul]
  refine ⟨γ, ?_, fun α => ?_, ?_⟩
  ·
    rintro β hβ ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hβ
    have h1 : Θ (γ ^ k) = 1 := by rw [← hy, hΘI]
    rw [map_zpow, hΘγ, ← orderOf_dvd_iff_zpow_eq_one, hordφ] at h1
    obtain ⟨j, rfl⟩ := h1
    rw [zpow_mul, zpow_natCast, hγ2f, one_zpow]
  ·
    obtain ⟨g, δ, rfl⟩ := twistedE6_exists_eq_conj_mul_fieldActor Nat.prime_two hf hq hK σ hσ α
    have hδ : δ ∈ Submonoid.powers φ :=
      mem_powers_iff_mem_zpowers.2 (by rw [hzφ]; exact mem_top δ)
    obtain ⟨n, rfl⟩ := hδ
    refine ⟨g * (x n)⁻¹, γ ^ n, npow_mem_zpowers γ n, ?_⟩
    rw [hγn, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  · have hxf : x f = ⟨_, pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom 1
        (map_one _)⟩ := Subtype.ext (by rw [hx, hSf])
    exact ⟨_, by rw [hγn, hφf, hxf]⟩

end Xi

variable {G : Type*} [Group G] [Finite G] {G₀ : Subgroup G}

end CFSG.SeitzReduction.EPilot
