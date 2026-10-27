module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4D4
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Rest CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem card_sylow_of_central {K : Type} [Group K] [Finite K] (P : Sylow 2 K) {x : K}
    (hxc : ∀ s ∈ (P : Subgroup K), s * x = x * s) :
    Nat.card ↥(P : Subgroup K) = 2 ^ (Nat.card ↥(centralizer ({x} : Set K))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : (P : Subgroup K) ≤ centralizer ({x} : Set K) := fun s hs => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxc s hs
  exact (jm_isSylowOf_of_le P hPC).card_eq

theorem g2_cent_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type} [Group M]
    (hM : LieModel M .G2 0 p f) (z : M) (hz : orderOf z = 2) :
    Nat.card ↥(centralizer ({z} : Set M)) =
      (p ^ f * ((p ^ f) ^ 2 - 1)) * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
  obtain ⟨F, hF, hFin, S, hcard, -⟩ := GHInv.exists_shape_G2 hp hp2 hM z hz
  have hY := Ivk94.shape_card_eq S
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard] at hY
  exact hY

theorem d4_cent_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type} [Group M]
    (hM : LieModel M .trialityD4 0 p f) (z : M) (hz : orderOf z = 2) :
    Nat.card ↥(centralizer ({z} : Set M)) =
      ((p ^ f) ^ 3 * (((p ^ f) ^ 3) ^ 2 - 1)) * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  exact Ivk94.card_centralizer_d4 hp2 hM z hz

theorem g2_sylow_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type} [Group M]
    [Finite M] (hM : LieModel M .G2 0 p f) (P : Sylow 2 M) {x : M} (hx : orderOf x = 2)
    (hxc : ∀ s ∈ (P : Subgroup M), s * x = x * s) :
    Nat.card ↥(P : Subgroup M) =
      2 ^ (((p ^ f * ((p ^ f) ^ 2 - 1)) * (p ^ f * ((p ^ f) ^ 2 - 1))).factorization 2) := by
  rw [card_sylow_of_central P hxc, g2_cent_card hp hp2 hM x hx]

theorem d4_sylow_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type} [Group M]
    [Finite M] (hM : LieModel M .trialityD4 0 p f) (P : Sylow 2 M) {x : M} (hx : orderOf x = 2)
    (hxc : ∀ s ∈ (P : Subgroup M), s * x = x * s) :
    Nat.card ↥(P : Subgroup M) =
      2 ^ ((((p ^ f) ^ 3 * (((p ^ f) ^ 3) ^ 2 - 1)) * (p ^ f * ((p ^ f) ^ 2 - 1))).factorization 2) := by
  rw [card_sylow_of_central P hxc, d4_cent_card hp hp2 hM x hx]

theorem d4_one_class {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type} [Group M]
    (hM : LieModel M .trialityD4 0 p f) :
    ∀ a b : M, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  have : Fact p.Prime := ⟨hp⟩
  have hf := one_le_of_lieModel_D4 hM
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hM
  have hD : D4Data (GaloisField p (3 * f)) (sig0 p f) (p ^ f) := d4Data_sig0 hp2 hf
  have hσ := hD.sigma3
  have key : ∀ a : M, orderOf a = 2 → IsConj (φ a) (τL hσ) := by
    intro a ha
    have hsq : φ a * φ a = 1 ∧ φ a ≠ 1 := by
      refine ⟨?_, ?_⟩
      · rw [← pow_two, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      · intro h
        have : a = 1 := φ.injective (by rw [h, map_one])
        rw [this, orderOf_one] at ha
        exact absurd ha (by norm_num)
    obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf
      hsq.1 (tauL_mul_self hσ) hsq.2 (tauL_ne_one hσ hD.neg_one)
    exact isConj_iff.2 ⟨g, hg⟩
  intro a b ha hb
  exact Ivk47ab.isConj_of_equiv φ ((key a ha).trans (key b hb).symm)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
