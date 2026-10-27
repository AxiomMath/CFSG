module

public import CFSG.CharacterTheory.BlockBasics.Defects
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectPrimaryVanishing
public import CFSG.CharacterTheory.Wreathed.CoprimeClassUnitRatio

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section Basis

variable {G : Type*} [Group G] [Fintype G]

theorem localCentralCharacterHom_conjugacyClassSum_mk (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (χ : basis.index) (g : G) :
    (localCentralCharacterHom basis ideal χ
        (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)) : ℂ) =
      ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * (basis.representation χ).character g /
        (basis.representation χ).character 1 :=
  CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis g χ

theorem unit_class_scalar_force_exact_block_defect_of_isUnit
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (χ : basis.index) (g u v : G) (hg : g = u * v) (huv : Commute u v)
    (hu : ∃ k : ℕ, orderOf u = p ^ k) (hv : Nat.Coprime p (orderOf v))
    (hsylow : ∃ S : Sylow p (Subgroup.centralizer ({g} : Set G)),
      (S : Subgroup (Subgroup.centralizer ({g} : Set G))).map
        (Subgroup.centralizer ({g} : Set G)).subtype = Subgroup.zpowers u)
    (hunit : IsUnit (localCentralCharacterHom basis ideal χ
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)))) :
    coefficientBlockDefect basis ideal p χ (Subgroup.zpowers u) := by
  set z := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)
  have hres : centralCharacterResidueHom basis ideal χ z ≠ 0 :=
    (hunit.map (localizedComplexIntegerResidue ideal)).ne_zero
  have hχg : (basis.representation χ).character g ≠ 0 := by
    intro h0
    apply hunit.ne_zero
    apply Subtype.ext
    rw [localCentralCharacterHom_conjugacyClassSum_mk, h0, mul_zero, zero_div]
    rfl
  obtain ⟨D, hD⟩ := coefficientBlockDefect_exists basis ideal p χ
  have hPD : subgroupSubconjugate (Subgroup.zpowers u) D :=
    (block_characters_vanish_outside_defect_primary basis ideal p χ D hD g u v hg huv hu hv).2
      ⟨χ, coefficientBlock_self_mem basis _ χ, hχg⟩
  obtain ⟨S, hS⟩ := hsylow
  exact ⟨⟨ConjClasses.mk g, ⟨g, rfl, S, hS.symm⟩, hres⟩,
    fun Y Q hY hYres => subgroupSubconjugate_trans hPD (hD.2 Y Q hY hYres)⟩

theorem unit_class_scalar_force_exact_block_defect (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (χ : basis.index) (g u v : G)
    (hg : g = u * v) (huv : Commute u v) (hu : ∃ k : ℕ, orderOf u = p ^ k)
    (hv : Nat.Coprime p (orderOf v))
    (hsylow : ∃ S : Sylow p (Subgroup.centralizer ({g} : Set G)),
      (S : Subgroup (Subgroup.centralizer ({g} : Set G))).map
        (Subgroup.centralizer ({g} : Set G)).subtype = Subgroup.zpowers u)
    (hunit : ∃ y : (localizedComplexIntegerRing ideal)ˣ,
      ((y : localizedComplexIntegerRing ideal) : ℂ) =
        ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * (basis.representation χ).character g /
          (basis.representation χ).character 1) :
    coefficientBlockDefect basis ideal p χ (Subgroup.zpowers u) := by
  obtain ⟨y, hy⟩ := hunit
  have hω : localCentralCharacterHom basis ideal χ
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)) = y := by
    apply Subtype.ext
    rw [localCentralCharacterHom_conjugacyClassSum_mk, hy]
  exact unit_class_scalar_force_exact_block_defect_of_isUnit basis ideal p χ g u v hg huv hu hv
    hsylow (hω ▸ y.isUnit)

end Basis

theorem unit_class_scalar_force_exact_block_defect_shared (p : ℕ) (hp : p.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) [CharP (BlocksAlgInt ⧸ m) p] {G : Type}
    [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (g u v : G) (hg : g = u * v)
    (huv : Commute u v) (hu : ∃ k : ℕ, orderOf u = p ^ k) (hv : Nat.Coprime p (orderOf v))
    (hsylow : ∃ S : Sylow p (Subgroup.centralizer ({g} : Set G)),
      (S : Subgroup (Subgroup.centralizer ({g} : Set G))).map
        (Subgroup.centralizer ({g} : Set G)).subtype = Subgroup.zpowers u)
    (hunit : ∃ y : (CFSG.BrauerThirdMainTheorem.Helpers.localCoefficientSubring m hm)ˣ,
      ((y : CFSG.BrauerThirdMainTheorem.Helpers.localCoefficientSubring m hm) : ℂ) =
        ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g / χ 1) :
    ∀ ψ ∈ BlocksBlockOf m G χ,
      CFSG.BrauerThirdMainTheorem.Helpers.blockDefect p m ψ (Subgroup.zpowers u) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨l, rfl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis hχ
  obtain ⟨y, hy⟩ := hunit
  have hle : CFSG.BrauerThirdMainTheorem.Helpers.localCoefficientSubring m hm ≤
      localizedComplexIntegerRing m :=
    (CFSG.BlockBasics.localCoefficientSubring_eq_localized m).le
  have hmain := unit_class_scalar_force_exact_block_defect basis m p l g u v hg huv hu hv hsylow
    ⟨Units.map (Subring.inclusion hle).toMonoidHom y, hy⟩
  have hirr := CFSG.BlockBasics.basis_character_mem_irr basis l
  exact (CFSG.BlockBasics.forall_blockDefect_iff p m hm ⟨_, hirr, rfl⟩
    (CFSG.BrauerThirdMainTheorem.Helpers.mem_blockOf_self m hirr) _).mpr
    ((CFSG.BlockBasics.coefficientBlockDefect_iff basis m p l _).mp hmain)

end CFSG.Semidihedral.Principal
