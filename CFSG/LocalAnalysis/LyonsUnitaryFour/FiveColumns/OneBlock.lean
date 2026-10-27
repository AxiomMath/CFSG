module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPCentralResidueVanishing
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterResidueCriterion

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

variable {L : Type*} [Group L] [Fintype L]

@[expose] noncomputable def centralGroupElement (ring : Subring ℂ) (c : L)
    (hc : c ∈ Subgroup.center L) : centralCoefficientSubring (G := L) ring :=
  ⟨MonoidAlgebra.single c 1, ⟨fun g => by
      simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs
      · exact ring.one_mem
      · exact ring.zero_mem,
    Subring.mem_center_iff.mpr fun other =>
      ((groupAlgebra_central_of_coeff_conjugation _ (fun element conjugator => by
        simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
        have hiff : c = conjugator * element * conjugator⁻¹ ↔ c = element := by
          constructor
          · intro h
            have h' : conjugator⁻¹ * c * conjugator = element := by rw [h]; group
            have hck : conjugator⁻¹ * c * conjugator = c := by
              rw [Subgroup.mem_center_iff.mp hc conjugator⁻¹, inv_mul_cancel_right]
            exact hck.symm.trans h'
          · rintro rfl
            rw [Subgroup.mem_center_iff.mp hc conjugator, mul_inv_cancel_right]
        by_cases h : c = element
        · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
        · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mp h'))]) other).eq).symm⟩⟩

theorem centralGroupElement_val (ring : Subring ℂ) (c : L) (hc : c ∈ Subgroup.center L) :
    (centralGroupElement ring c hc).val = MonoidAlgebra.single c 1 := rfl

theorem centralCharacterResidueHom_centralGroupElement (basis : FiniteIrreducibleCharacterBasis L)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (c : L) (hc : c ∈ Subgroup.center L) (k : ℕ)
    (hk : c ^ (p ^ k) = 1) (label : basis.index) :
    centralCharacterResidueHom basis ideal label
      (centralGroupElement (localizedComplexIntegerRing ideal) c hc) = 1 := by
  set x := centralCharacterResidueHom basis ideal label
    (centralGroupElement (localizedComplexIntegerRing ideal) c hc) with hx
  have hpow : x ^ (p ^ k) = 1 := by
    rw [hx, ← map_pow]
    have hone : (centralGroupElement (localizedComplexIntegerRing ideal) c hc) ^ (p ^ k) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, centralGroupElement_val, MonoidAlgebra.single_pow, hk, one_pow]
      rfl
    rw [hone, map_one]
  have hzero : (x - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp hzero)

theorem coefficientBlock_eq_univ_of_centralizer_central
    (basis : FiniteIrreducibleCharacterBasis L) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (P : Subgroup L) [P.Normal] (hP : IsPGroup p P)
    (hcent : ∀ c ∈ Subgroup.centralizer (P : Set L),
      c ∈ Subgroup.center L ∧ ∃ k : ℕ, c ^ (p ^ k) = 1)
    (label : basis.index) :
    coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ := by
  set R := localizedComplexIntegerRing ideal with hR
  set Q := Subgroup.centralizer (P : Set L) with hQ
  have hresidue : ∀ θ : basis.index, ∀ v : centralCoefficientSubring (G := L) R,
      centralCharacterResidueHom basis ideal θ v =
        ∑ c : Q, localizedComplexIntegerResidue ideal
          ⟨v.val.coeff c, centralCoefficientSubring_coefficients R v c⟩ := by
    intro θ v
    set v' : centralCoefficientSubring (G := L) R := ∑ c : Q,
      centralCoefficientScalarHom R ⟨v.val.coeff c, centralCoefficientSubring_coefficients R v c⟩ *
        centralGroupElement R (c : L) (hcent c c.2).1 with hv'
    have hval : v'.val = ∑ c' : Q, MonoidAlgebra.single (c' : L) (v.val.coeff c') := by
      rw [hv', AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [Subring.coe_mul, centralGroupElement_val]
      change algebraMap ℂ (MonoidAlgebra ℂ L) (v.val.coeff c') * MonoidAlgebra.single (c' : L) 1 = _
      rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
        RingHom.id_apply, MonoidAlgebra.single_mul_single, one_mul, mul_one]
    have hcoeff : ∀ c : Q, v'.val.coeff c = v.val.coeff c := by
      intro c
      rw [hval, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single c]
      · simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
      · intro c' _ hne
        simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
        rw [ite_eq_right (fun h => hne (Subtype.ext h))]
      · intro h
        exact absurd (Finset.mem_univ c) h
    have hproj : centralSubgroupCoefficientProjection R Q v =
        centralSubgroupCoefficientProjection R Q v' := by
      apply Subtype.ext
      rw [centralSubgroupCoefficientProjection_val, centralSubgroupCoefficientProjection_val]
      ext c
      rw [subgroupCoefficientProjection_coeff, subgroupCoefficientProjection_coeff, hcoeff]
    rw [normal_p_central_residue_determined_by_projection basis ideal p P hP v v' hproj θ, hv',
      map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨k, hk⟩ := (hcent c c.2).2
    rw [map_mul, centralCharacterResidueHom_scalar,
      centralCharacterResidueHom_centralGroupElement basis ideal p (c : L) (hcent c c.2).1 k hk θ,
      mul_one]
  have hsame : ∀ θ : basis.index,
      centralCharacterResidueHom basis ideal θ = centralCharacterResidueHom basis ideal label :=
    fun θ => RingHom.ext fun v => by rw [hresidue θ v, hresidue label v]
  apply Finset.eq_univ_of_forall
  intro θ
  rw [coefficientBlock_mem_iff]
  exact (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label θ).mpr
    (hsame θ).symm

end CFSG.LyonsUnitaryFour
