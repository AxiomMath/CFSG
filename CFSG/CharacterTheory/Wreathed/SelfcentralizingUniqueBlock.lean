module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPCentralResidueVanishing
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerMismatchRestriction
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

universe v

variable {K : Type*} [Group K] [Fintype K]

omit [Fintype K] in
theorem groupAlgebra_central_coeff_conj {L : Type*} [CommRing L] (e : MonoidAlgebra L K)
    (hcentral : ∀ x : MonoidAlgebra L K, Commute e x) (g c : K) :
    e.coeff (c * g * c⁻¹) = e.coeff g := by
  have hequal := congrArg (fun value : MonoidAlgebra L K => value.coeff (c * g))
    (hcentral (MonoidAlgebra.single c 1)).eq
  simpa only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply,
    mul_one, one_mul, inv_mul_cancel_left] using hequal

theorem field_invariant_idempotent_eq_zero_or_one {k : Type*} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (P : Subgroup K) [P.Normal] (hP : IsPGroup p P)
    (hcent : Subgroup.centralizer (P : Set K) ≤ P) (e : MonoidAlgebra k K)
    (hinvariant : subgroupConjugationInvariant P e) (hidem : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  set C := Subgroup.centralizer (P : Set K) with hC
  set π := MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' P) with hπ
  set s : MonoidAlgebra k K := ∑ x : C, MonoidAlgebra.single (x : K) (e.coeff x) with hs
  have hscoeff : ∀ g : K, s.coeff g = if g ∈ C then e.coeff g else 0 := by
    intro g
    rw [hs, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    split_ifs with hg
    · rw [Finset.sum_eq_single ⟨g, hg⟩]
      · simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
      · intro x _ hx
        simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
        rw [ite_eq_right (fun h => hx (Subtype.ext h))]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · refine Finset.sum_eq_zero fun x _ => ?_
      simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [ite_eq_right (fun h : (x : K) = g => hg (h ▸ x.2))]
  have hfix : ∀ y : P, ∀ g ∈ C, (y : K) * g * (y : K)⁻¹ = g := by
    intro y g hg
    rw [Subgroup.mem_centralizer_iff.mp hg y y.2, mul_inv_cancel_right]
  have hmemC : ∀ y : P, ∀ g : K, (y : K) * g * (y : K)⁻¹ ∈ C → g ∈ C := by
    intro y g h
    have e' := hfix ⟨(y : K)⁻¹, P.inv_mem y.2⟩ _ h
    have hg : g = (y : K) * g * (y : K)⁻¹ := by
      rw [← e']
      group
    rw [hg]
    exact h
  have hinv : subgroupConjugationInvariant P (e - s) := by
    intro y g
    rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finsupp.sub_apply, hinvariant y g, hscoeff,
      hscoeff]
    by_cases hg : g ∈ C
    · rw [hfix y g hg]
    · rw [ite_eq_right hg, ite_eq_right (fun h => hg (hmemC y g h))]
  have hzero : ∀ g ∈ C, (e - s).coeff g = 0 := by
    intro g hg
    rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hscoeff, ite_eq_left hg, sub_self]
  have hdiff : π (e - s) = 0 :=
    normal_p_invariant_quotient_zero_of_outside_centralizer p P hP (e - s) hinv hzero
  set c : k := ∑ x : C, e.coeff x with hc
  have hπs : π s = MonoidAlgebra.single 1 c := by
    have hsingle : MonoidAlgebra.single (1 : K ⧸ P) c =
        ∑ x : C, MonoidAlgebra.single (1 : K ⧸ P) (e.coeff x) := by
      rw [hc, ← MonoidAlgebra.singleAddHom_apply, map_sum]
      simp only [MonoidAlgebra.singleAddHom_apply]
    rw [hsingle, hs, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx1 : (QuotientGroup.mk' P) (x : K) = 1 := (QuotientGroup.eq_one_iff _).mpr (hcent x.2)
    rw [hπ, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, hx1]
  have hπe : π e = MonoidAlgebra.single 1 c := by
    rw [← sub_add_cancel e s, map_add, hdiff, zero_add, hπs]
  have hcc : c * c = c := by
    have h := (hidem.map π).eq
    rw [hπe, MonoidAlgebra.single_mul_single, mul_one] at h
    have h' := congrArg (fun value : MonoidAlgebra k (K ⧸ P) => value.coeff 1) h
    simpa only [MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true] using h'
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with hc0 | hc1
  · left
    refine hidem.eq_zero_of_isNilpotent
      (normal_p_quotient_zero_element_nilpotent p P hP e ?_)
    change π e = 0
    rw [hπe, hc0, MonoidAlgebra.single_zero]
  · right
    have hnil : IsNilpotent (1 - e) := by
      refine normal_p_quotient_zero_element_nilpotent p P hP (1 - e) ?_
      change π (1 - e) = 0
      rw [map_sub, map_one, hπe, hc1, MonoidAlgebra.one_def, sub_self]
    exact (sub_eq_zero.mp (hidem.one_sub.eq_zero_of_isNilpotent hnil)).symm

theorem selfcentralizing_central_idempotent_eq_zero_or_one (p : ℕ) [Fact p.Prime]
    (P : Subgroup K) [P.Normal] (hP : IsPGroup p P)
    (hcent : Subgroup.centralizer (P : Set K) ≤ P) (L : Type v) [CommRing L] [IsLocalRing L]
    [CharP (IsLocalRing.ResidueField L) p] (e : MonoidAlgebra L K)
    (hcentral : ∀ x : MonoidAlgebra L K, Commute e x) (hidem : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  set r := MonoidAlgebra.mapRingHom K (IsLocalRing.residue L) with hr
  have hinv : subgroupConjugationInvariant P (r e) := by
    intro y g
    rw [hr, MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom,
      groupAlgebra_central_coeff_conj e hcentral g y]
  have hdetect : ∀ a : L, IsUnit (IsLocalRing.residue L a) ↔ IsUnit a :=
    fun a => isUnit_map_iff (IsLocalRing.residue L) a
  have hprod : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, hidem.eq, sub_self]
  rcases field_invariant_idempotent_eq_zero_or_one p P hP hcent (r e) hinv (hidem.map r) with
    h0 | h1
  · left
    have hu : IsUnit (1 - e) := by
      refine (groupAlgebra_isUnit_iff_residue (IsLocalRing.residue L) hdetect (1 - e)).mp ?_
      rw [map_sub, map_one, ← hr, h0, sub_zero]
      exact isUnit_one
    exact hu.mul_left_eq_zero.mp hprod
  · right
    have hu : IsUnit e := by
      refine (groupAlgebra_isUnit_iff_residue (IsLocalRing.residue L) hdetect e).mp ?_
      rw [← hr, h1]
      exact isUnit_one
    exact (sub_eq_zero.mp (hu.mul_right_eq_zero.mp hprod)).symm

theorem selfcentralizing_unique_block (p : ℕ) [Fact p.Prime] (P : Subgroup K) [P.Normal]
    (hP : IsPGroup p P) (hcent : Subgroup.centralizer (P : Set K) ≤ P)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (basis : FiniteIrreducibleCharacterBasis K) :
    (∀ principal : basis.index, (basis.representation principal).character = 1 →
      coefficientBlock basis (localizedComplexIntegerRing ideal) principal = Finset.univ) ∧
    (∀ label : basis.index,
      coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ) ∧
    ∀ left right : basis.index,
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) left right := by
  let := localizedComplexIntegerRing_residue_charP ideal p
  have hall : ∀ label : basis.index,
      coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ := by
    intro label
    set B := coefficientBlock basis (localizedComplexIntegerRing ideal) label with hB
    have hadm : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) B :=
      coefficientBlock_admissible basis _ label
    set lifted := liftGroupAlgebraCoefficients (localizedComplexIntegerRing ideal)
      (characterSubsetIdempotent basis B) hadm with hlifted
    have hmap : MonoidAlgebra.mapRingHom K (localizedComplexIntegerRing ideal).subtype lifted =
        characterSubsetIdempotent basis B :=
      liftGroupAlgebraCoefficients_map _ _ hadm
    rcases selfcentralizing_central_idempotent_eq_zero_or_one p P hP hcent
      (localizedComplexIntegerRing ideal) lifted
      (lifted_characterSubsetIdempotent_central basis _ B hadm)
      (lifted_characterSubsetIdempotent_idempotent basis _ B hadm) with h0 | h1
    · exfalso
      rw [h0, map_zero, ← characterSubsetIdempotent_empty basis] at hmap
      have hempty : B = ∅ := (characterSubsetIdempotent_injective basis hmap).symm
      have hmem : label ∈ B := coefficientBlock_self_mem basis _ label
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    · rw [h1, map_one, ← characterSubsetIdempotent_univ basis] at hmap
      exact (characterSubsetIdempotent_injective basis hmap).symm
  have hsame : ∀ left right : basis.index,
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) left right := by
    intro left right
    have hmem : right ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) left := by
      rw [hall left]
      exact Finset.mem_univ _
    exact (coefficientBlock_mem_iff _ _ _ _).mp hmem
  exact ⟨fun principal _ => hall principal, hall, hsame⟩

end CFSG.Wreathed
