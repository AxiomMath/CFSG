module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAFactors
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.LinearAlgebra

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel

private theorem scalar_toLinU
    {q f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData q f K}
    {c : Kˣ} (hc : GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n)) :
    ((toLinU h n ⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩ :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) =
      algebraMap K (Module.End K (Fin n → K)) (c : K) := by
  apply LinearMap.ext
  intro v
  rw [toLinU_apply]
  ext i
  simp [Module.algebraMap_end_eq_smul_id, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVecLin, Matrix.toLin'_apply,
    Matrix.scalar_apply]

theorem exists_linear_of_good_unitaryBlock
    {q f p n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData q f K}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ q ^ f + 1)
    {x : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hx : (x : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hn4 : n ≤ 4)
    {a : K[X]} (ha : a ∈ primaryFactors ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (toLinU h n x) ⟨a, ha⟩) :
    ∃ lam : K, a = X - C lam := by
  classical
  haveI : Fact q.Prime := ⟨h.prime⟩
  haveI : CharP K q := h.charP
  haveI := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  set xlin : Module.End K (Fin n → K) :=
    ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) with hxlin
  have hxpow_mem : GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) := by
    rw [← hx]
    exact pow_mem x.2 p
  have hpow : xlin ^ p = algebraMap K (Module.End K (Fin n → K)) (c : K) := by
    have h1 : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ p =
        ((toLinU h n (x ^ p) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) := by
      exact congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
        (g : Module.End K (Fin n → K))) (map_pow (toLinU h n) x p).symm
    rw [hxlin, h1]
    rw [show (x ^ p : primeFormUnitary h (idGram K n)) =
        ⟨GeneralLinearGroup.scalar (Fin n) c, hxpow_mem⟩ from Subtype.ext hx]
    exact scalar_toLinU hxpow_mem
  have haeval : aeval xlin (X ^ p - C (c : K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hpow, sub_self]
  have hmin : minpoly K xlin ∣ X ^ p - C (c : K) := minpoly.dvd K xlin haeval
  have hdvdpoly : a ∣ X ^ p - C (c : K) :=
    (mem_primaryFactors.mp ha).2.2.trans hmin
  set Q := q ^ f with hQ
  have hcardK : Nat.card K = Q ^ 2 := by
    rw [h.card, hQ]
    rw [show 2 * f = f * 2 by omega, pow_mul]
  have hdvdUnits : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hcardK]
    have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero f h.prime.ne_zero)
    have hsub : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
      have h := Nat.sq_sub_sq Q 1
      simpa [pow_two, mul_comm] using h
    rw [hsub]
    exact dvd_mul_of_dvd_right hpdvd (Q - 1)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvdUnits
  have hζprim : IsPrimitiveRoot (ζ : K) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (hζ ▸ IsPrimitiveRoot.orderOf ζ)
  by_cases hc : ∃ lam : K, lam ^ p = (c : K)
  · obtain ⟨lam, hlam⟩ := hc
    obtain ⟨ν, hν, -⟩ :=
      CFSG.AGLEmbedding.ToralCensus.exists_eq_X_sub_C_of_mem_primaryFactors
        hp.pos hζprim hlam haeval ha
    exact ⟨ν, hν⟩
  · have hc' : ∀ b : K, b ^ p ≠ (c : K) := by
      rintro b hb
      exact hc ⟨b, hb⟩
    have hirr : Irreducible (X ^ p - C (c : K)) := X_pow_sub_C_irreducible_of_prime hp hc'
    have hassoc : Associated a (X ^ p - C (c : K)) :=
      (irreducible_of_mem_primaryFactors ha).associated_of_dvd hirr hdvdpoly
    have heq : a = X ^ p - C (c : K) :=
      eq_of_monic_of_associated (monic_of_mem_primaryFactors ha)
        (monic_X_pow_sub_C _ hp.pos.ne') hassoc
    have hdeg : a.natDegree = p := by rw [heq, Polynomial.natDegree_X_pow_sub_C]
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
    have hm2 : 2 ≤ primaryMultiplicity xlin a := hgood.1
    have hdim : Module.finrank K (primaryComponent xlin a) =
        p * primaryMultiplicity xlin a := by
      rw [finrank_primaryComponent, hdeg]
    have hle : Module.finrank K (primaryComponent xlin a) ≤ n := by
      refine (Submodule.finrank_le _).trans_eq ?_
      exact Module.finrank_fin_fun (R := K) (n := n)
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h6 : 6 ≤ p * primaryMultiplicity xlin a := Nat.mul_le_mul hp3 hm2
    omega

end CFSG.LinearAlgebra

end
