module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryPairing

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Polynomial

variable {K : Type*} [Field K]

theorem dualPoly_X_sub_C_twistedA (σ : K →+* K) {ν : K} (hν : ν ≠ 0) :
    dualPoly σ (X - C ν) = X - C (σ ν)⁻¹ := by
  have hs : σ ν ≠ 0 := (map_ne_zero σ).mpr hν
  have hrev : ((X - C ν).map σ).reverse = 1 - C (σ ν) * X := by
    rw [Polynomial.map_sub, map_X, map_C, reverse, natDegree_X_sub_C, reflect_sub,
      reflect_C, ← pow_one (X : K[X]), reflect_monomial, pow_one, revAt_le le_rfl, Nat.sub_self,
      pow_zero, mul_comm]
  rw [dualPoly, hrev, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, inv_neg,
    mul_sub, mul_one, ← mul_assoc, ← C_mul, neg_mul, inv_mul_cancel₀ hs]
  simp only [map_neg, map_one]
  ring

theorem exists_isPrimitiveRoot_twistedA [Finite K] {m : ℕ} (hm : m.Prime)
    (hdvd : m ∣ Nat.card K - 1) : ∃ η : K, IsPrimitiveRoot η m := by
  have : Fact m.Prime := ⟨hm⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) m (by rwa [Nat.card_units])
  exact ⟨u, IsPrimitiveRoot.coe_units_iff.mpr (hu ▸ IsPrimitiveRoot.orderOf u)⟩

theorem exists_eq_X_sub_C_of_mem_primaryFactors {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} {m : ℕ} (hm : 0 < m) {η : K}
    (hη : IsPrimitiveRoot η m) {α ζ : K} (hα : α ^ m = ζ) (hx : aeval x (X ^ m - C ζ) = 0)
    {a : K[X]} (ha : a ∈ primaryFactors x) : ∃ ν : K, a = X - C ν ∧ ν ^ m = ζ := by
  have hdvd : a ∣ X ^ m - C ζ := (mem_primaryFactors.mp ha).2.2.trans (minpoly.dvd K x hx)
  have hspl : (a : K[X]).Splits :=
    (X_pow_sub_C_splits_of_isPrimitiveRoot hη hα).of_dvd (X_pow_sub_C_ne_zero hm ζ) hdvd
  have hdeg := hspl.natDegree_eq_one_of_irreducible (irreducible_of_mem_primaryFactors ha)
  have hlin : a = X - C (-a.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]
    exact (monic_of_mem_primaryFactors ha).eq_X_add_C hdeg
  refine ⟨-a.coeff 0, hlin, ?_⟩
  have hroot : IsRoot (X ^ m - C ζ) (-a.coeff 0) := dvd_iff_isRoot.mp (hlin ▸ hdvd)
  simpa [sub_eq_zero] using hroot

theorem dvd_card_sub_one_of_dvd {p f : ℕ} (hK : UnitaryFieldData p f K) {m : ℕ}
    (hm : m ∣ p ^ f + 1 ∨ m ∣ p ^ f - 1) : m ∣ Nat.card K - 1 := by
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  have hsq : Nat.card K - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    rw [hK.card, pow_mul', ← Nat.sq_sub_sq, one_pow]
  rw [hsq]
  rcases hm with h | h
  · exact h.mul_right _
  · exact h.mul_left _

variable {p f : ℕ} (hK : UnitaryFieldData p f K) [Finite K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
include hK

theorem dualPoly_eq_of_dvd_add_one [Nontrivial V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
    {x : LinearMap.GeneralLinearGroup K V} (H : UnitaryPrimaryData hK.bar B x) {m : ℕ}
    (hm : m.Prime) (hm2 : m ≠ 2) (hmq : m ∣ p ^ f + 1) {ζ : K} (hζ : ζ ^ (p ^ f + 1) = 1)
    (hx : aeval (x : Module.End K V) (X ^ m - C ζ) = 0) :
    ∀ a ∈ primaryFactors (x : Module.End K V), dualPoly hK.bar a = a := by
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hζ
    exact zero_ne_one hζ
  by_cases hroot : ∃ α : K, α ^ m = ζ
  · obtain ⟨α, hα⟩ := hroot
    obtain ⟨η, hη⟩ := exists_isPrimitiveRoot_twistedA hm (dvd_card_sub_one_of_dvd hK (Or.inl hmq))
    intro a ha
    obtain ⟨ν, rfl, hν⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hm.pos hη hα hx ha
    have hν0 : ν ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne_zero] at hν
      exact hζ0 hν.symm
    have hcop : Nat.Coprime m (p ^ f - 1) := by
      refine (Nat.Prime.coprime_iff_not_dvd hm).mpr fun h => hm2 ?_
      have h2 : m ∣ 2 := by
        have := Nat.dvd_sub hmq h
        rwa [show p ^ f + 1 - (p ^ f - 1) = 2 by omega] at this
      exact (Nat.prime_dvd_prime_iff_eq hm Nat.prime_two).mp h2
    have h1 : (ν ^ (p ^ f + 1)) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hν, hζ]
    have h2 : (ν ^ (p ^ f + 1)) ^ (p ^ f - 1) = 1 := by
      have := Fintype.ofFinite K
      rw [← pow_mul, show (p ^ f + 1) * (p ^ f - 1) = Fintype.card K - 1 by
        rw [← Nat.card_eq_fintype_card, hK.card, pow_mul', ← Nat.sq_sub_sq, one_pow]]
      exact FiniteField.pow_card_sub_one_eq_one ν hν0
    have h3 : ν ^ (p ^ f + 1) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    rw [dualPoly_X_sub_C_twistedA _ hν0, hK.bar_apply]
    congr 2
    exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact h3)
  · simp only [not_exists] at hroot
    have hirr := X_pow_sub_C_irreducible_of_prime hm hroot
    have hmin : Irreducible (minpoly K (x : Module.End K V)) := by
      obtain ⟨c, hc⟩ := minpoly.dvd K _ hx
      rcases hirr.isUnit_or_isUnit hc with h | h
      · exact absurd h (minpoly.not_isUnit K _)
      · exact (Associated.symm ⟨h.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩).irreducible
          hirr
    have heq : ∀ b ∈ primaryFactors (x : Module.End K V), b = minpoly K (x : Module.End K V) :=
      fun b hb => eq_of_monic_of_associated (monic_of_mem_primaryFactors hb)
        (minpoly.monic (Algebra.IsIntegral.isIntegral _))
        ((irreducible_of_mem_primaryFactors hb).associated_of_dvd hmin
          (mem_primaryFactors.mp hb).2.2)
    intro a ha
    rw [heq _ (dualPoly_mem_primaryFactors H ha), heq a ha]

theorem exists_dualPoly_eq_of_dvd_sub_one {x : Module.End K V} {m : ℕ} (hm : m.Prime)
    (hmq : m ∣ p ^ f - 1) (hx : aeval x (X ^ m - C (1 : K)) = 0) {a : K[X]}
    (ha : a ∈ primaryFactors x) :
    ∃ ν : K, a = X - C ν ∧ ν ^ m = 1 ∧ dualPoly hK.bar a = X - C ν⁻¹ := by
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot_twistedA hm (dvd_card_sub_one_of_dvd hK (Or.inr hmq))
  obtain ⟨ν, rfl, hν⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hm.pos hη (one_pow m) hx ha
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne_zero] at hν
    exact zero_ne_one hν
  refine ⟨ν, rfl, hν, ?_⟩
  rw [dualPoly_X_sub_C_twistedA _ hν0, hK.bar_apply]
  obtain ⟨k, hk⟩ := hmq
  have hq1 : ν ^ (p ^ f - 1) = 1 := by rw [hk, pow_mul, hν, one_pow]
  have hνq : ν ^ p ^ f = ν := by
    calc ν ^ p ^ f = ν ^ (p ^ f - 1) * ν := by rw [← pow_succ, Nat.sub_add_cancel hq]
      _ = ν := by rw [hq1, one_mul]
  rw [hνq]

end CFSG.AGLEmbedding.ToralCensus
