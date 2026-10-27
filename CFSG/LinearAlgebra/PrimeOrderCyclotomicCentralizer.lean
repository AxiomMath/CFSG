module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveEigen

public section

namespace CFSG.LinearAlgebra.PrimeOrderCyclotomicCentralizer

open Polynomial Matrix

private lemma minpoly_dvd_X_sub_one_of_not_dvd_cyclotomic {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ} [Fact r.Prime]
    (hirr : Irreducible (cyclotomic r K)) {E : Module.End K V} (hE : E ^ r = 1)
    (hΦq : ¬ cyclotomic r K ∣ minpoly K E) : minpoly K E ∣ X - 1 := by
  have hfac : (X : K[X]) ^ r - 1 = (X - 1) * cyclotomic r K := by
    rw [← cyclotomic_prime_mul_X_sub_one K r, mul_comm]
  have hmdvd : minpoly K E ∣ (X - 1) * cyclotomic r K := by
    rw [← hfac]
    exact minpoly.dvd K E (by simp [hE])
  exact ((Irreducible.coprime_iff_not_dvd hirr).mpr hΦq).symm.dvd_of_dvd_mul_right hmdvd

theorem minpoly_eq_cyclotomic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} [Fact r.Prime] (hirr : Irreducible (cyclotomic r K))
    (hdim : Module.finrank K V + 1 = r) {E : Module.End K V} (hE : E ^ r = 1) (hE1 : E ≠ 1) :
    minpoly K E = cyclotomic r K := by
  classical
  have hr : r.Prime := Fact.out
  haveI : Nontrivial (Module.End K V) := ⟨1, E, fun h => hE1 h.symm⟩
  have hint : IsIntegral K E := Algebra.IsIntegral.isIntegral E
  have hq_monic : (minpoly K E).Monic := minpoly.monic hint
  have hq_pos : 0 < (minpoly K E).natDegree := minpoly.natDegree_pos hint
  have hqdeg_le : (minpoly K E).natDegree ≤ Module.finrank K V := by
    have h := natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly E)
      (LinearMap.charpoly_monic E).ne_zero
    rwa [LinearMap.charpoly_natDegree] at h
  have hΦdeg : (cyclotomic r K).natDegree = Module.finrank K V := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hr]
    omega
  by_cases hΦq : cyclotomic r K ∣ minpoly K E
  · refine eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic r K) hq_monic hΦq ?_
    rwa [hΦdeg]
  · exfalso
    have hq_dvd : minpoly K E ∣ X - 1 :=
      minpoly_dvd_X_sub_one_of_not_dvd_cyclotomic hirr hE hΦq
    have hqeq : minpoly K E = X - 1 := by
      have h := eq_of_monic_of_dvd_of_natDegree_le hq_monic (monic_X_sub_C (1 : K)) hq_dvd ?_
      · exact h.symm
      · rw [natDegree_X_sub_C]
        exact hq_pos
    have h0 : aeval E (X - 1 : K[X]) = 0 := by
      rw [← hqeq]
      exact minpoly.aeval K E
    have h1 : E - 1 = 0 := by simpa using h0
    exact hE1 (sub_eq_zero.mp h1)

private noncomputable def centralizerEndHom {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    Subgroup.centralizer ({g} : Set (GL (Fin n) K)) →* Module.End K (Fin n → K) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

private lemma centralizerEndHom_injective {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    Function.Injective (centralizerEndHom g) := fun x y h =>
  Subtype.ext (Units.ext (Matrix.toLinAlgEquiv'.injective h))

private lemma centralizerEndHom_commute {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    ∀ c : Subgroup.centralizer ({g} : Set (GL (Fin n) K)), Commute (centralizerEndHom g c)
      (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) := by
  intro c
  have hc : (g : GL (Fin n) K) * (c : GL (Fin n) K) = (c : GL (Fin n) K) * g :=
    (Subgroup.mem_centralizer_iff.mp c.2) g (by simp)
  have hmat : ((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)
      = (g : Matrix (Fin n) (Fin n) K) * ((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hc.symm
  change Matrix.toLinAlgEquiv' (((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)
    = Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K) *
      Matrix.toLinAlgEquiv' (((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  rw [← map_mul, ← map_mul]
  exact congrArg Matrix.toLinAlgEquiv' hmat

theorem isCyclic_centralizer_of_orderOf_eq {K : Type} [Field K] [Finite K] {r n : ℕ}
    [Fact r.Prime] (hirr : Irreducible (Polynomial.cyclotomic r K)) (hn : n + 1 = r)
    {g : GL (Fin n) K} (hg : orderOf g = r) :
    IsCyclic (Subgroup.centralizer ({g} : Set (GL (Fin n) K))) := by
  classical
  have hr : r.Prime := Fact.out
  let E : Module.End K (Fin n → K) := Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)
  have hgne : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hr.ne_one hg.symm
  have hEne : E ≠ 1 := by
    intro h
    apply hgne
    apply Units.ext
    have h' : Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K) = 1 := h
    rw [← map_one Matrix.toLinAlgEquiv'] at h'
    exact Matrix.toLinAlgEquiv'.injective h'
  have hEr : E ^ r = 1 := by
    have hmat : ((g : Matrix (Fin n) (Fin n) K) ^ r) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
    change (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) ^ r = 1
    rw [← map_pow, hmat, map_one]
  have hdim : Module.finrank K (Fin n → K) + 1 = r := by
    rw [Module.finrank_fin_fun]
    exact hn
  have hminpoly : minpoly K E = cyclotomic r K :=
    minpoly_eq_cyclotomic hirr hdim hEr hEne
  have hdeg : (minpoly K E).natDegree = Module.finrank K (Fin n → K) := by
    rw [hminpoly, Polynomial.natDegree_cyclotomic, Nat.totient_prime hr]
    omega
  exact CFSG.RankThree.PartOne.KCEvenUnitaryFive.isCyclic_of_irreducible_minpoly
    (E := E) (by rw [hminpoly]; exact hirr) hdeg (centralizerEndHom g)
    (centralizerEndHom_injective g) (centralizerEndHom_commute g)

theorem irreducible_cyclotomic_five_zmod_seven :
    Irreducible (Polynomial.cyclotomic 5 (ZMod 7)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 7) (n := 5) (by norm_num)
    dvd_rfl ?_
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime (by norm_num : Nat.Prime 5)]
  rw [← orderOf_units, ZMod.coe_unitOfCoprime, eq_comm, orderOf_eq_iff (by norm_num)]
  refine ⟨?_, ?_⟩
  · decide
  · intro m hm hm0 h
    interval_cases m <;> (revert h; decide)

theorem isCyclic_centralizer_of_orderOf_eq_five {g : GL (Fin 4) (ZMod 7)} (hg : orderOf g = 5) :
    IsCyclic (Subgroup.centralizer ({g} : Set (GL (Fin 4) (ZMod 7)))) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact isCyclic_centralizer_of_orderOf_eq (K := ZMod 7) (r := 5) (n := 4)
    irreducible_cyclotomic_five_zmod_seven (by norm_num) hg

end CFSG.LinearAlgebra.PrimeOrderCyclotomicCentralizer
