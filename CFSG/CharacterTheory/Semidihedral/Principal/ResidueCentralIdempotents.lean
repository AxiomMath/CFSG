module

public import CFSG.CharacterTheory.Semidihedral.Principal.NilpotentQuotientIdempotents
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralResidueNilpotence
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalCentralIdempotent
public import CFSG.CharacterTheory.Wreathed.SelfcentralizingUniqueBlock

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section GroupAlgebraCenter

variable {S G : Type*} [CommRing S] [Group G]

theorem mem_center_iff_coeff_conj (x : MonoidAlgebra S G) :
    x ∈ Subring.center (MonoidAlgebra S G) ↔ ∀ g c : G, x.coeff (c * g * c⁻¹) = x.coeff g := by
  constructor
  · intro hx
    exact CFSG.Wreathed.groupAlgebra_central_coeff_conj x
      fun y => (Subring.mem_center_iff.mp hx y).symm
  · intro hx
    rw [Subring.mem_center_iff]
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      ext g
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one]
      have hconj := hx (h⁻¹ * g) h
      rw [show h * (h⁻¹ * g) * h⁻¹ = g * h⁻¹ by group] at hconj
      exact hconj.symm
    | add y z hy hz => rw [add_mul, mul_add, hy, hz]
    | smul r y hy => rw [smul_mul_assoc, mul_smul_comm, hy]

omit [Group G] in
theorem coeff_sum_single [Fintype G] (a : G → S) (g : G) :
    (∑ h, MonoidAlgebra.single h (a h)).coeff g = a g := by
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single g]
  · simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true]
  · intro h _ hhg
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [ite_eq_right hhg]
  · intro h
    exact absurd (Finset.mem_univ g) h

end GroupAlgebraCenter

variable (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
variable {G : Type*} [Group G] [Fintype G]

@[expose] def blockIdempotent (basis : FiniteIrreducibleCharacterBasis G) (label : basis.index) :
    MonoidAlgebra (localizedComplexIntegerRing ideal) G :=
  centralCoefficientLiftHom (localizedComplexIntegerRing ideal)
    (coefficientBlockIdempotent basis (localizedComplexIntegerRing ideal) label)

theorem blockIdempotent_map_subtype (basis : FiniteIrreducibleCharacterBasis G)
    (label : basis.index) :
    MonoidAlgebra.mapRingHom G (localizedComplexIntegerRing ideal).subtype
        (blockIdempotent ideal basis label) =
      characterSubsetIdempotent basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) label) :=
  centralCoefficientLiftHom_map _ _

theorem residueMap_surjective :
    Function.Surjective (MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)) := by
  intro y
  refine ⟨∑ g, MonoidAlgebra.single g (Function.surjInv
    (localizedComplexIntegerResidue_surjective ideal) (y.coeff g)), ?_⟩
  rw [map_sum]
  simp only [MonoidAlgebra.mapRingHom_single, Function.surjInv_eq]
  exact groupAlgebra_sum_single y

theorem centralCoefficientLiftHom_mem_center
    (v : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    centralCoefficientLiftHom (localizedComplexIntegerRing ideal) v ∈
      Subring.center (MonoidAlgebra (localizedComplexIntegerRing ideal) G) := by
  rw [Subring.mem_center_iff]
  intro y
  apply groupAlgebraCoefficientEmbedding_injective (localizedComplexIntegerRing ideal)
  rw [map_mul, map_mul, centralCoefficientLiftHom_map]
  exact (centralCoefficientSubring_commutes _ v _).eq.symm

theorem exists_centralCoefficient_lift (z : MonoidAlgebra (localizedComplexIntegerRing ideal) G)
    (hz : z ∈ Subring.center (MonoidAlgebra (localizedComplexIntegerRing ideal) G)) :
    ∃ v : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal),
      centralCoefficientLiftHom (localizedComplexIntegerRing ideal) v = z := by
  set ι := MonoidAlgebra.mapRingHom G (localizedComplexIntegerRing ideal).subtype
  have hcoeff : ∀ g, (ι z).coeff g = (z.coeff g : ℂ) := fun g => by
    rw [MonoidAlgebra.coeff_mapRingHom]
    rfl
  have hmem : ι z ∈ centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal) := by
    refine Subring.mem_inf.mpr ⟨fun g => by rw [hcoeff]; exact (z.coeff g).2, ?_⟩
    rw [mem_center_iff_coeff_conj]
    intro g c
    rw [hcoeff, hcoeff, (mem_center_iff_coeff_conj z).mp hz g c]
  refine ⟨⟨ι z, hmem⟩, ?_⟩
  apply groupAlgebraCoefficientEmbedding_injective (localizedComplexIntegerRing ideal)
  rw [centralCoefficientLiftHom_map]

theorem idempotent_eq_zero_of_residueMap_eq_zero
    {x : MonoidAlgebra (localizedComplexIntegerRing ideal) G} (hx : IsIdempotentElem x)
    (h0 : MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal) x = 0) : x = 0 := by
  have hdetect : ∀ c, IsUnit (localizedComplexIntegerResidue ideal c) ↔ IsUnit c := by
    intro c
    rw [localizedComplexIntegerResidue_isUnit_iff]
    let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
    exact isUnit_iff_ne_zero
  have hunit : IsUnit (1 - x) := by
    rw [← groupAlgebra_isUnit_iff_residue (localizedComplexIntegerResidue ideal) hdetect,
      map_sub, map_one, h0, sub_zero]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hunit
  have hprod : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
  calc x = x * (1 - x) * ↑u⁻¹ := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    _ = 0 := by rw [hprod, zero_mul]

theorem exists_centralIdempotent_lift (basis : FiniteIrreducibleCharacterBasis G)
    {ē : MonoidAlgebra (ComplexAlgebraicIntegers ⧸ ideal) G}
    (hē : ē ∈ centralIdempotents (MonoidAlgebra (ComplexAlgebraicIntegers ⧸ ideal) G)) :
    ∃ e ∈ centralIdempotents (MonoidAlgebra (localizedComplexIntegerRing ideal) G),
      MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal) e = ē := by
  set R := localizedComplexIntegerRing ideal
  set σ := Function.surjInv (localizedComplexIntegerResidue_surjective ideal)
  set z : MonoidAlgebra R G := ∑ g, MonoidAlgebra.single g (σ (ē.coeff g)) with hz
  have hzcoeff : ∀ g, z.coeff g = σ (ē.coeff g) := coeff_sum_single _
  have hzcen : z ∈ Subring.center (MonoidAlgebra R G) := by
    rw [mem_center_iff_coeff_conj]
    intro g c
    rw [hzcoeff, hzcoeff, (mem_center_iff_coeff_conj ē).mp hē.1 g c]
  have hzred : MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal) z = ē := by
    rw [hz, map_sum]
    simp only [MonoidAlgebra.mapRingHom_single, σ, Function.surjInv_eq]
    exact groupAlgebra_sum_single ē
  obtain ⟨v, hv⟩ := exists_centralCoefficient_lift ideal z hzcen
  have hred : centralCoefficientReductionHom ideal v = ē := by
    change MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)
      (centralCoefficientLiftHom R v) = ē
    rw [hv, hzred]
  have h01 : ∀ χ, centralCharacterResidueHom basis ideal χ v = 0 ∨
      centralCharacterResidueHom basis ideal χ v = 1 := by
    intro χ
    let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    have hzero : centralCoefficientReductionHom ideal (v * v - v) = 0 := by
      rw [map_sub, map_mul, hred, hē.2.eq, sub_self]
    have h := centralCharacterResidueHom_zero_of_coefficient_reduction_zero basis ideal
      (v * v - v) hzero χ
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact h
  set S := Finset.univ.filter fun χ => centralCharacterResidueHom basis ideal χ v = 1 with hS
  have hSadm : characterSubsetAdmissible basis R S := by
    by_cases hex : ∃ χ, centralCharacterResidueHom basis ideal χ v = 1
    · obtain ⟨χ, hχ⟩ := hex
      have h := centralCharacterResidueHom_fiber_admissible basis ideal v χ
      rw [hχ] at h
      exact h
    · push Not at hex
      have hSempty : S = ∅ := by
        ext χ
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact hex χ
      rw [hSempty]
      change characterSubsetIdempotent basis ∅ ∈ _
      rw [characterSubsetIdempotent_empty]
      exact Subring.zero_mem _
  set E := admissibleCharacterSubsetElement basis R S hSadm with hE
  have hEidem : IsIdempotentElem E :=
    Subtype.ext (characterSubsetIdempotent_isIdempotent basis S).eq
  have hres : ∀ χ, centralCharacterResidueHom basis ideal χ (v - E) = 0 := by
    intro χ
    rw [map_sub, hE, centralCharacterResidueHom_subset]
    rcases h01 χ with h | h
    · have hχ : χ ∉ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact zero_ne_one
      rw [h, ite_eq_right hχ, sub_zero]
    · have hχ : χ ∈ S := by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, h]
      rw [h, ite_eq_left hχ, sub_self]
  have hnil := centralCoefficientReductionHom_nilpotent_of_residues_zero basis ideal (v - E) hres
  set Ē := centralCoefficientReductionHom ideal E with hĒ
  have hĒidem : IsIdempotentElem Ē := hEidem.map _
  have hcomm : Commute ē Ē := by
    rw [← hred]
    exact (Commute.all v E).map _
  rw [map_sub, hred] at hnil
  have c1 : Commute ē (1 - Ē) := (Commute.one_right ē).sub_right hcomm
  have c2 : Commute Ē (1 - Ē) := (Commute.one_right Ē).sub_right (Commute.refl Ē)
  have c3 : Commute Ē (1 - ē) := (Commute.one_right Ē).sub_right hcomm.symm
  have h1 : ē * (1 - Ē) = 0 := by
    apply (hē.2.mul_of_commute c1 hĒidem.one_sub).eq_zero_of_isNilpotent
    have hrw : ē * (1 - Ē) = (ē - Ē) * (1 - Ē) := by
      rw [sub_mul _ Ē, mul_sub Ē, mul_one, hĒidem.eq, sub_self, sub_zero]
    rw [hrw]
    exact Commute.isNilpotent_mul_right (c1.sub_left c2) hnil
  have h2 : Ē * (1 - ē) = 0 := by
    apply (hĒidem.mul_of_commute c3 hē.2.one_sub).eq_zero_of_isNilpotent
    have hrw : Ē * (1 - ē) = -(Ē * (ē - Ē)) := by
      rw [mul_sub Ē ē Ē, hĒidem.eq, mul_sub, mul_one, neg_sub]
    rw [hrw]
    exact (Commute.isNilpotent_mul_left (hcomm.symm.sub_right (Commute.refl Ē)) hnil).neg
  have heq : ē = Ē := by
    have e1 : ē = ē * Ē := by rw [mul_sub, mul_one, sub_eq_zero] at h1; exact h1
    have e2 : Ē = Ē * ē := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2
    rw [e1, hcomm.eq, ← e2]
  refine ⟨centralCoefficientLiftHom R E,
    ⟨centralCoefficientLiftHom_mem_center ideal E, hEidem.map _⟩, ?_⟩
  change centralCoefficientReductionHom ideal E = ē
  exact heq.symm

theorem residueMap_bijOn_centralIdempotents (basis : FiniteIrreducibleCharacterBasis G) :
    Set.BijOn (MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal))
      (centralIdempotents (MonoidAlgebra (localizedComplexIntegerRing ideal) G))
      (centralIdempotents (MonoidAlgebra (ComplexAlgebraicIntegers ⧸ ideal) G)) := by
  set ρ := MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)
  refine ⟨fun e he => map_mem_centralIdempotents ρ (residueMap_surjective ideal) he, ?_,
    fun ē hē => exists_centralIdempotent_lift ideal basis hē⟩
  intro e he e' he' hee'
  have hfe : ρ e * ρ e = ρ e := (he.2.map ρ).eq
  have hfe' : ρ e' * ρ e' = ρ e' := (he'.2.map ρ).eq
  have h1 : e * (1 - e') = 0 := by
    refine idempotent_eq_zero_of_residueMap_eq_zero ideal
      (mul_mem_centralIdempotents he (one_sub_mem_centralIdempotents he')).2 ?_
    rw [map_mul, map_sub, map_one, ← hee', mul_sub, mul_one, hfe, sub_self]
  have h2 : e' * (1 - e) = 0 := by
    refine idempotent_eq_zero_of_residueMap_eq_zero ideal
      (mul_mem_centralIdempotents he' (one_sub_mem_centralIdempotents he)).2 ?_
    rw [map_mul, map_sub, map_one, hee', mul_sub, mul_one, hfe', sub_self]
  have h1' : e = e * e' := by rw [mul_sub, mul_one, sub_eq_zero] at h1; exact h1
  have h2' : e' = e' * e := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2
  calc e = e * e' := h1'
    _ = e' * e := (Subring.mem_center_iff.mp he.1 e').symm
    _ = e' := h2'.symm

theorem blockIdempotent_isPrimitive (basis : FiniteIrreducibleCharacterBasis G)
    (label : basis.index) : IsPrimitiveCentralIdempotent (blockIdempotent ideal basis label) := by
  set R := localizedComplexIntegerRing ideal
  set x := coefficientBlockIdempotent basis R label with hx
  have hprim := coefficientBlockIdempotent_primitive basis R label
  refine ⟨⟨centralCoefficientLiftHom_mem_center ideal x, hprim.1.map _⟩, fun h => ?_, ?_⟩
  · apply hprim.2.1
    apply centralCoefficientLiftHom_injective R
    rw [map_zero]
    exact h
  · intro e₁ he₁ e₂ he₂ h12 hsum
    obtain ⟨y₁, hy₁⟩ := exists_centralCoefficient_lift ideal e₁ he₁.1
    have hy₁idem : IsIdempotentElem y₁ := by
      unfold IsIdempotentElem
      apply centralCoefficientLiftHom_injective R
      rw [map_mul, hy₁, he₁.2.eq]
    have hcorner : y₁ * x = y₁ := by
      apply centralCoefficientLiftHom_injective R
      have hsum' : centralCoefficientLiftHom R x = e₁ + e₂ := hsum.symm
      rw [map_mul, hy₁, hsum', mul_add, he₁.2.eq, h12, add_zero]
    rcases hprim.2.2 y₁ hy₁idem hcorner with h | h
    · left
      rw [← hy₁, h, map_zero]
    · right
      have he₁x : e₁ = centralCoefficientLiftHom R x := by rw [← hy₁, h]
      have hsum' : e₁ + e₂ = e₁ := by
        rw [hsum]
        exact he₁x.symm
      exact add_eq_left.mp hsum'

theorem exists_blockIdempotent_eq (basis : FiniteIrreducibleCharacterBasis G)
    {e : MonoidAlgebra (localizedComplexIntegerRing ideal) G}
    (he : IsPrimitiveCentralIdempotent e) : ∃ label, e = blockIdempotent ideal basis label := by
  obtain ⟨⟨hcen, hidem⟩, hne, hdec⟩ := he
  obtain ⟨y, hy⟩ := exists_centralCoefficient_lift ideal e hcen
  have hyidem : IsIdempotentElem y := by
    unfold IsIdempotentElem
    apply centralCoefficientLiftHom_injective (localizedComplexIntegerRing ideal)
    rw [map_mul, hy, hidem.eq]
  obtain ⟨A, hA, -⟩ := central_idempotent_eq_character_subset basis y.val
    (centralCoefficientSubring_commutes (localizedComplexIntegerRing ideal) y)
    (congrArg Subtype.val hyidem.eq)
  have hAadm : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) A := by
    change characterSubsetIdempotent basis A ∈ _
    rw [← hA]
    exact y.property.1
  obtain ⟨χ, hχ⟩ : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    rw [← hy]
    have hy0 : y = 0 := Subtype.ext (by rw [hA, hempty, characterSubsetIdempotent_empty]; rfl)
    rw [hy0, map_zero]
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) χ with hB
  have hBA : B ⊆ A := fun ψ hψ =>
    ((coefficientBlock_mem_iff basis (localizedComplexIntegerRing ideal) χ ψ).mp hψ A hAadm).mp hχ
  have hA2 : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) (A ∩ Bᶜ) :=
    characterSubsetAdmissible_inter basis (localizedComplexIntegerRing ideal) _ _ hAadm
      (characterSubsetAdmissible_compl basis (localizedComplexIntegerRing ideal) _
        (coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) χ))
  set E₁ := coefficientBlockIdempotent basis (localizedComplexIntegerRing ideal) χ with hE₁
  set E₂ := admissibleCharacterSubsetElement basis (localizedComplexIntegerRing ideal) (A ∩ Bᶜ)
    hA2 with hE₂
  have hE₁val : E₁.val = characterSubsetIdempotent basis B := rfl
  have hE₂val : E₂.val = characterSubsetIdempotent basis (A ∩ Bᶜ) := rfl
  have hsum : E₁ + E₂ = y := by
    apply Subtype.ext
    rw [Subring.coe_add, hE₁val, hE₂val, hA,
      ← characterSubsetIdempotent_union_disjoint basis _ _
        (Finset.disjoint_left.mpr fun ψ hψ hψ' => (Finset.mem_compl.mp
          (Finset.mem_inter.mp hψ').2) hψ)]
    congr 1
    ext ψ
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact hBA h
      · exact h
    · intro h
      by_cases hψ : ψ ∈ B
      · exact Or.inl hψ
      · exact Or.inr ⟨h, hψ⟩
  have hmul : E₁ * E₂ = 0 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hE₁val, hE₂val, ← characterSubsetIdempotent_inter]
    have hempty : B ∩ (A ∩ Bᶜ) = ∅ := by
      ext ψ
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.notMem_empty, iff_false, not_and]
      intro h1 _ h2
      exact h2 h1
    rw [hempty, characterSubsetIdempotent_empty]
    rfl
  have hE₁cen : centralCoefficientLiftHom (localizedComplexIntegerRing ideal) E₁ ∈
      centralIdempotents (MonoidAlgebra (localizedComplexIntegerRing ideal) G) :=
    ⟨centralCoefficientLiftHom_mem_center ideal E₁,
      (coefficientBlockIdempotent_isIdempotent basis (localizedComplexIntegerRing ideal) χ).map _⟩
  have hE₂cen : centralCoefficientLiftHom (localizedComplexIntegerRing ideal) E₂ ∈
      centralIdempotents (MonoidAlgebra (localizedComplexIntegerRing ideal) G) :=
    ⟨centralCoefficientLiftHom_mem_center ideal E₂,
      (show IsIdempotentElem E₂ from
        Subtype.ext (characterSubsetIdempotent_isIdempotent basis _).eq).map _⟩
  rcases hdec _ hE₁cen _ hE₂cen (by rw [← map_mul, hmul, map_zero])
      (by rw [← map_add, hsum, hy]) with h | h
  · exfalso
    have hE₁0 : E₁ = 0 := centralCoefficientLiftHom_injective (localizedComplexIntegerRing ideal)
      (by rw [h, map_zero])
    have hval := congrArg Subtype.val hE₁0
    rw [hE₁val] at hval
    have hBempty : B = ∅ := characterSubsetIdempotent_injective basis
      (hval.trans (characterSubsetIdempotent_empty basis).symm)
    have hχB : χ ∈ B := coefficientBlock_self_mem basis (localizedComplexIntegerRing ideal) χ
    rw [hBempty] at hχB
    exact Finset.notMem_empty χ hχB
  · refine ⟨χ, ?_⟩
    have hE₂0 : E₂ = 0 := centralCoefficientLiftHom_injective (localizedComplexIntegerRing ideal)
      (by rw [h, map_zero])
    rw [← hy, ← hsum, hE₂0, add_zero]
    rfl

theorem relative_central_idempotents_reduce_bijectively (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (basis : FiniteIrreducibleCharacterBasis G) :
    CentralIdempotentCorrespondence
        (MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)) ∧
      {e : MonoidAlgebra (ComplexAlgebraicIntegers ⧸ ideal) G | IsPrimitiveCentralIdempotent e} =
        Set.range (fun label => MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)
          (blockIdempotent ideal basis label)) ∧
      ∀ χ ψ, MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)
          (blockIdempotent ideal basis χ) =
            MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)
              (blockIdempotent ideal basis ψ) ↔
        coefficientBlock basis (localizedComplexIntegerRing ideal) χ =
          coefficientBlock basis (localizedComplexIntegerRing ideal) ψ := by
  set R := localizedComplexIntegerRing ideal
  set ρ := MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)
  have hcorr := CentralIdempotentCorrespondence.of_bijOn ρ
    (residueMap_bijOn_centralIdempotents ideal basis)
  refine ⟨hcorr, ?_, ?_⟩
  · ext ē
    constructor
    · intro hē
      obtain ⟨e, he, rfl⟩ := hcorr.primitive_bijOn.surjOn hē
      obtain ⟨label, rfl⟩ := exists_blockIdempotent_eq ideal basis he
      exact ⟨label, rfl⟩
    · rintro ⟨label, rfl⟩
      exact hcorr.primitive_bijOn.mapsTo (blockIdempotent_isPrimitive ideal basis label)
  · intro χ ψ
    constructor
    · intro h
      have hbi := hcorr.bijOn.injOn (blockIdempotent_isPrimitive ideal basis χ).1
        (blockIdempotent_isPrimitive ideal basis ψ).1 h
      have hval := congrArg Subtype.val (centralCoefficientLiftHom_injective R hbi)
      exact characterSubsetIdempotent_injective basis hval
    · intro h
      have hval : coefficientBlockIdempotent basis R χ = coefficientBlockIdempotent basis R ψ :=
        Subtype.ext (by
          change characterSubsetIdempotent basis (coefficientBlock basis R χ) =
            characterSubsetIdempotent basis (coefficientBlock basis R ψ)
          rw [h])
      change ρ (centralCoefficientLiftHom R (coefficientBlockIdempotent basis R χ)) =
        ρ (centralCoefficientLiftHom R (coefficientBlockIdempotent basis R ψ))
      rw [hval]

end CFSG.Semidihedral.Principal
