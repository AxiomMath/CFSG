module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OPNonembed

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {K : Type} [Field K] {n : ℕ}

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (pairedSympForm_isAlt
  pairedSympForm_nondegenerate finrank_standard)

theorem commute_of_isPGroup_of_mem_normalizer [Finite K] [CharP K 2] {H : Type} [Group H]
    (ψ : H →* StatedSp n K) (hψ : Function.Injective ψ) (R : Subgroup H) (hR : IsPGroup 2 R)
    {x : H} (hxN : x ∈ normalizer (R : Set H)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hxℓ : x ^ ℓ = 1)
    (hx1 : x ≠ 1) (hℓK : (ℓ : K) ≠ 0) (hℓq : ¬ ℓ ∣ Nat.card K)
    (hord : ∀ j, 1 ≤ j → j < n → ¬ ℓ ∣ Nat.card K ^ (2 * j) - 1)
    (hord' : ∀ i, 1 ≤ i → i < n → ¬ ℓ ∣ Nat.card K ^ i - 1) {a b : H} (ha : a ∈ R)
    (hb : b ∈ R) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hRbot : R = ⊥
  · subst hRbot
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  set ρ : H →* Module.End K (Fin n ⊕ Fin n → K) := (natRep (StatedSp n K)).comp ψ with hρdef
  have hρ : IsIsometric (spForm n K) ρ := fun h u v => isIsometric_natRep_statedSp n K (ψ h) u v
  have hinj : Function.Injective ρ := (natRep_injective _).comp hψ
  set U := isoSeq (spForm n K) ρ R 1 with hUdef
  have hU : U ≠ ⊥ := isoSeq_one_ne_bot (spForm n K) ρ 2 hρ hinj R hR hRbot
  have hUx : ∀ u ∈ U, opNatEquiv ψ x u ∈ U := fun u hu =>
    apply_mem_isoSeq (spForm n K) ρ hρ R 1 hxN hu
  have hUiso : (spForm n K).IsTotallyIsotropic U := isoSeq_isTotallyIsotropic (spForm n K) ρ R 1
  have hdimV : finrank K (Fin n ⊕ Fin n → K) = 2 * n := finrank_standard
  have hdimU : 2 * finrank K U ≤ 2 * n := by
    have := two_mul_finrank_le_of_isTotallyIsotropic (spForm n K) hUiso
    rwa [hdimV] at this
  have heB : ∀ w a b, CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K n
      (opNatEquiv ψ w a) (opNatEquiv ψ w b) =
        CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K n a b := fun w a b => by
    rw [← spForm_β_eq_pairedSympForm, ← spForm_β_eq_pairedSympForm]
    exact hρ w a b
  have hex : opNatEquiv ψ x ^ ℓ = 1 := by rw [← map_pow, hxℓ, map_one]
  have hex1 : opNatEquiv ψ x ≠ 1 := fun h =>
    hx1 (opNatEquiv_injective hψ (by rw [h, map_one]))
  have hnU : n ≤ finrank K U :=
    le_finrank_of_isometry pairedSympForm_isAlt pairedSympForm_nondegenerate hdimV (heB x) hℓ
      hex hex1 hℓK hℓq hord hord' hU hUx
  have hUperp : (spForm n K).perp U = U := by
    have h1 := finrank_perp_add_finrank (spForm n K) U
    rw [hdimV] at h1
    exact (Submodule.eq_of_le_of_finrank_eq hUiso (by omega)).symm
  have hfix : ∀ g ∈ R, ∀ u ∈ U, ρ g u = u := fun g hg u hu => by
    have := isoSeq_triv (spForm n K) ρ R 0 hg hu
    rwa [isoSeq_zero, Submodule.mem_bot, sub_eq_zero] at this
  have hmove : ∀ g ∈ R, ∀ v, ρ g v - v ∈ U := fun g hg v => by
    have := perp_isoSeq_triv (spForm n K) ρ hρ R 0 hg (v := v)
      (by rw [isoSeq_zero, (spForm n K).perp_bot]; trivial)
    rwa [← hUdef, hUperp] at this
  apply hinj
  refine LinearMap.ext fun v => ?_
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have e1 : ρ a (ρ b v) = ρ a v + (ρ b v - v) := by
    conv_lhs => rw [show ρ b v = v + (ρ b v - v) by abel]
    rw [map_add, hfix a ha _ (hmove b hb v)]
  have e2 : ρ b (ρ a v) = ρ b v + (ρ a v - v) := by
    conv_lhs => rw [show ρ a v = v + (ρ a v - v) by abel]
    rw [map_add, hfix b hb _ (hmove a ha v)]
  rw [e1, e2]
  abel

end CFSG.SeitzReduction.SymplecticPilot
