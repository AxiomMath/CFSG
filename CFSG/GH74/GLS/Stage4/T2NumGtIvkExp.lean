module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41R

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace Proofs2.Ivk41R

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem sl3_pow_p_eq_one {F : Type} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hp3 : 3 ≤ p)
    (r : Matrix.SpecialLinearGroup (Fin 3) F) (k : ℕ) (hr : r ^ (p ^ k) = 1) : r ^ p = 1 := by
  set M : Matrix (Fin 3) (Fin 3) F := (r : Matrix (Fin 3) (Fin 3) F) with hM
  have hMk : M ^ (p ^ k) = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hr
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hN : (M - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right M), hMk, one_pow, sub_self]
  have hnil : IsNilpotent (M - 1) := ⟨p ^ k, hN⟩
  have hnil' : IsNilpotent (Matrix.toLin' (M - 1)) := (Matrix.isNilpotent_toLin'_iff _).2 hnil
  have hch := IsNilpotent.charpoly_eq_X_pow_finrank hnil'
  have hca := LinearMap.aeval_self_charpoly (Matrix.toLin' (M - 1))
  rw [hch] at hca
  have hfr : Module.finrank F (Fin 3 → F) = 3 := by simp
  rw [hfr] at hca
  simp only [map_pow, Polynomial.aeval_X] at hca
  have h3 : (M - 1) ^ 3 = 0 := by
    have h1 : Matrix.toLinAlgEquiv' (R := F) ((M - 1) ^ 3) = 0 := by
      rw [map_pow]
      exact hca
    exact (map_eq_zero_iff _ (Matrix.toLinAlgEquiv' (R := F)).injective).1 h1
  have hNp : (M - 1) ^ p = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hp3
    rw [pow_add, h3, zero_mul]
  have hMp : M ^ p = 1 := by
    have h1 : (M - 1 + 1) ^ p = (M - 1) ^ p + 1 ^ p := add_pow_char_of_commute p (Commute.one_right _)
    rw [sub_add_cancel, hNp, one_pow, zero_add] at h1
    exact h1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  simpa using hMp

theorem pow_p_of_surjective_coprime {S Q : Type} [Group S] [Group Q] {p : ℕ} [Fact p.Prime]
    (π : S →* Q) (hπ : Function.Surjective π) [Finite π.ker] (hker : Nat.Coprime (Nat.card π.ker) p)
    (hS : ∀ x : S, ∀ k : ℕ, x ^ (p ^ k) = 1 → x ^ p = 1) (y : Q) (k : ℕ) (hy : y ^ (p ^ k) = 1) :
    y ^ p = 1 := by
  obtain ⟨x, rfl⟩ := hπ y
  have hker1 : x ^ (p ^ k) ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have hm : (x ^ (p ^ k)) ^ (Nat.card π.ker) = 1 := by
    have := pow_card_eq_one' (G := ↥π.ker) (x := ⟨x ^ p ^ k, hker1⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (Nat.card π.ker) (orderOf (π x)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hy) (hker.pow_right k)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  set x' : S := (x ^ Nat.card π.ker) ^ t with hx'
  have hx'p : x' ^ (p ^ k) = 1 := by
    have h1 : x' ^ (p ^ k) = ((x ^ (p ^ k)) ^ Nat.card π.ker) ^ t := by
      simp only [hx', ← pow_mul]
      congr 1
      ring
    rw [h1, hm, one_pow]
  have h1 : x' ^ p = 1 := hS x' k hx'p
  have hπx' : π x' = π x := by rw [hx', map_pow, map_pow]; exact ht
  rw [← hπx', ← map_pow, h1, map_one]

theorem exp_p_of_isSLnEps_or_isLnEps {J : Type} [Group J] [Finite J] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : IsSLnEps 3 J 1 (p ^ n) ∨ IsLnEps 3 J 1 (p ^ n)) (r : J) (k : ℕ) (hr : r ^ (p ^ k) = 1) :
    r ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases hJ with (⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h1, -⟩) | (⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h1, -⟩)
  · have hchar : CharP F p := charP_of_natCard_eq_pow hp hcard
    let e' : J ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (specialLinearGroupEquivStatedSL 3 F).symm
    have h1 : (e' r) ^ (p ^ k) = 1 := by rw [← map_pow, hr, map_one]
    have h2 := sl3_pow_p_eq_one hp3 (e' r) k h1
    apply e'.injective
    rw [map_pow, h2, map_one]
  · exact absurd h1 (by norm_num)
  · have hchar : CharP F p := charP_of_natCard_eq_pow hp hcard
    let e' : J ≃* projectiveSL 3 F := e.trans (Lemma41dL3.projEquiv F).symm
    have : Finite (projectiveSL 3 F) := Finite.of_equiv J e'.toEquiv
    have hπ : Function.Surjective (QuotientGroup.mk' (scalars 3 F)) := QuotientGroup.mk'_surjective _
    have hker : Nat.Coprime (Nat.card (QuotientGroup.mk' (scalars 3 F)).ker) p := by
      rw [QuotientGroup.ker_mk']
      exact Lemma41dL3.scalars_coprime hp
    have h1 : (e' r) ^ (p ^ k) = 1 := by rw [← map_pow, hr, map_one]
    have h2 := pow_p_of_surjective_coprime (QuotientGroup.mk' (scalars 3 F)) hπ hker
      (fun x j hx => sl3_pow_p_eq_one hp3 x j hx) (e' r) k h1
    apply e'.injective
    rw [map_pow, h2, map_one]
  · exact absurd h1 (by norm_num)

end Proofs2.Ivk41R

theorem ivk_4_1_R_L3_exp :
    ∀ (J : Type) [Group J] [Finite J] (p n : ℕ), p.Prime → p ≠ 2 →
      (IsSLnEps 3 J 1 (p ^ n) ∨ IsLnEps 3 J 1 (p ^ n)) →
        ∀ z : J, orderOf z = 2 → ∀ X : Subgroup J, X ≤ centralizer ({z} : Set J) → IsPGroup p ↥X →
          Nat.card ↥X = p ^ n →
            ∃ R : Subgroup J, R = CFSG.Open.pCoreOf p (centralizer (X : Set J)) ∧ IsPGroup p ↥R ∧ X ≤ R ∧
              R ≤ centralizer (X : Set J) ∧ Nat.card ↥R = (p ^ n) ^ 3 ∧
              (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧
              (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧ (∀ r ∈ R, z * r * z⁻¹ * r ∈ X) ∧ (∀ r ∈ R, r ^ p ∈ X) := by
  intro J _ _ p n hp hp2 hJ z hz X hXz hXp hXc
  obtain ⟨R, hR, hRp, hXR, hRC, hRcard, hZ, hXc', hcomm, hinv⟩ :=
    Proofs2.ivk_4_1_R_L3 J p n hp hp2 hJ z hz X hXz hXp hXc
  refine ⟨R, hR, hRp, hXR, hRC, hRcard, hZ, hXc', hcomm, hinv, ?_⟩
  intro r hr
  obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
  have hrk : r ^ (p ^ k) = 1 := congrArg Subtype.val hk
  rw [Proofs2.Ivk41R.exp_p_of_isSLnEps_or_isLnEps hp hp2 hJ r k hrk]
  exact X.one_mem

end CFSG.GH74.GLS.IVK
