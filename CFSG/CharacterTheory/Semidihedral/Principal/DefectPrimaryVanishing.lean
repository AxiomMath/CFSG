module

public import CFSG.CharacterTheory.Semidihedral.Principal.CentralizerBrauerDefect
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalSectionIntertwining

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem block_character_section_zero_of_empty_brauer_fiber
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e) (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (label : basis.index)
    (hnone : ∀ θ : localBasis.index, brauerNormalizerCharacterResidueHom ideal p
      (Subgroup.zpowers u) hgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ ≠
        centralCharacterResidueHom basis ideal label)
    (regular : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hregular : Nat.Coprime p (orderOf regular.val)) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label) :
    (basis.representation χ).character
      (((⟨u, element_mem_centralizer_zpowers u⟩ :
        Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹).val = 0 := by
  have hmismatch : ∀ θ ∈ (Finset.univ : Finset localBasis.index),
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ
        (admissibleCharacterSubsetElement basis _
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label)
          (coefficientBlock_admissible basis _ label)) = 0 := by
    intro θ _
    obtain ⟨other, hother⟩ := brauerNormalizer_block_image_exists basis ideal p
      (Subgroup.zpowers u) hgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ
    have hnot : other ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) label := by
      intro hin
      have hsame := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal other
        label).mp (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hin))
      exact hnone θ (hother.trans hsame)
    rw [hother, centralCharacterResidueHom_subset, ite_eq_right hnot]
  have hzero := admissible_mismatch_section_projection_zero basis ideal p u e hu localBasis _
    (coefficientBlock_admissible basis _ label) Finset.univ
    (characterSubsetAdmissible_univ localBasis _) hmismatch regular hregular χ hχ
  have hsum := congrFun (characterSubsetProjection_add_compl localBasis Finset.univ
    (fun member => (basis.representation χ).character member.val)
    (fun element conjugator => Representation.char_conj _ element.val conjugator.val))
    ((⟨u, element_mem_centralizer_zpowers u⟩ :
      Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹
  have hempty : characterSubsetProjection localBasis (Finset.univ : Finset localBasis.index)ᶜ
      (fun member => (basis.representation χ).character member.val) = 0 := by
    rw [Finset.compl_univ]
    simp [characterSubsetProjection]
  rw [Pi.add_apply, hzero, hempty, Pi.zero_apply, zero_add] at hsum
  exact hsum.symm

theorem brauer_fiber_empty_of_not_subconjugate_defect
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (label : basis.index) (D : Subgroup G) (hD : coefficientBlockDefect basis ideal p label D)
    (u : G) (hgroup : IsPGroup p (Subgroup.zpowers u))
    (hnot : ¬ subgroupSubconjugate (Subgroup.zpowers u) D)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (θ : localBasis.index) :
    brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ ≠
        centralCharacterResidueHom basis ideal label := by
  intro hbrauer
  obtain ⟨E, hE⟩ := coefficientBlockDefect_exists localBasis ideal p θ
  have : ((Subgroup.zpowers u).subgroupOf
      (Subgroup.centralizer (Subgroup.zpowers u : Set G))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hPp : IsPGroup p ((Subgroup.zpowers u).subgroupOf
      (Subgroup.centralizer (Subgroup.zpowers u : Set G))) := hgroup.comap_subtype
  have hle : (Subgroup.zpowers u).subgroupOf
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) ≤ E :=
    normal_p_le_coefficientBlockDefect localBasis ideal p _ hPp hE
  have hPC : Subgroup.zpowers u ≤ Subgroup.centralizer (Subgroup.zpowers u : Set G) :=
    Subgroup.zpowers_le.mpr (element_mem_centralizer_zpowers u)
  have hEp : IsPGroup p (E.map (Subgroup.centralizer (Subgroup.zpowers u : Set G)).subtype) :=
    (coefficientBlockDefect_isPGroup localBasis ideal hE).map _
  have hPE : Subgroup.zpowers u ≤
      E.map (Subgroup.centralizer (Subgroup.zpowers u : Set G)).subtype := by
    have hmap := Subgroup.map_mono
      (f := (Subgroup.centralizer (Subgroup.zpowers u : Set G)).subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hPC] at hmap
  have hEC : E.map (Subgroup.centralizer (Subgroup.zpowers u : Set G)).subtype ≤
      Subgroup.centralizer (Subgroup.zpowers u : Set G) := Subgroup.map_subtype_le E
  have hlocal : coefficientBlockDefect localBasis ideal p θ
      ((E.map (Subgroup.centralizer (Subgroup.zpowers u : Set G)).subtype).subgroupOf
        (Subgroup.centralizer (Subgroup.zpowers u : Set G))) := by
    have heq : (E.map (Subgroup.centralizer (Subgroup.zpowers u : Set G)).subtype).subgroupOf
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) = E :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) E
    rw [heq]
    exact hE
  obtain ⟨hall, -⟩ := centralizer_brauer_image_defect_contains_local_defect basis ideal p
    (Subgroup.zpowers u) hgroup _ hEp hPE hEC localBasis θ hlocal label hbrauer
  exact hnot (subgroupSubconjugate_trans (subgroupSubconjugate_of_le hPE) (hall D hD))

theorem block_characters_vanish_outside_defect_primary
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (label : basis.index) (D : Subgroup G) (hD : coefficientBlockDefect basis ideal p label D)
    (g u v : G) (hg : g = u * v) (huv : Commute u v) (hu : ∃ k : ℕ, orderOf u = p ^ k)
    (hv : Nat.Coprime p (orderOf v)) :
    (¬ subgroupSubconjugate (Subgroup.zpowers u) D →
      ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        (basis.representation χ).character g = 0) ∧
    ((∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        (basis.representation χ).character g ≠ 0) →
      subgroupSubconjugate (Subgroup.zpowers u) D) := by
  have hvanish : ¬ subgroupSubconjugate (Subgroup.zpowers u) D →
      ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        (basis.representation χ).character g = 0 := by
    intro hnot χ hχ
    obtain ⟨k, hk⟩ := hu
    have hinv : Subgroup.zpowers u⁻¹ = Subgroup.zpowers u := Subgroup.zpowers_inv
    have hu' : orderOf u⁻¹ ∣ p ^ k := by rw [orderOf_inv, hk]
    have hgroup : IsPGroup p (Subgroup.zpowers u⁻¹) :=
      IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact hu')
    have hnot' : ¬ subgroupSubconjugate (Subgroup.zpowers u⁻¹) D := by
      rw [hinv]
      exact hnot
    obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
      (G := ↥(Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G)))
    have hregmem : v⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (huv.inv_inv.zpow_left n).eq
    have hzero := block_character_section_zero_of_empty_brauer_fiber basis ideal p u⁻¹ k hu'
      hgroup localBasis label
      (brauer_fiber_empty_of_not_subconjugate_defect basis ideal p label D hD u⁻¹ hgroup hnot'
        localBasis) ⟨v⁻¹, hregmem⟩ (by rw [orderOf_inv]; exact hv) χ hχ
    have hpoint : (((⟨u⁻¹, element_mem_centralizer_zpowers u⁻¹⟩ :
        Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G)) * ⟨v⁻¹, hregmem⟩)⁻¹).val = g := by
      change (u⁻¹ * v⁻¹)⁻¹ = g
      rw [mul_inv_rev, inv_inv, inv_inv, hg, huv.eq]
    rw [hpoint] at hzero
    exact hzero
  refine ⟨hvanish, fun ⟨χ, hχ, hne⟩ => ?_⟩
  by_contra hnot
  exact hne (hvanish hnot χ hχ)

theorem block_characters_vanish_of_defect_exponent_prime
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (label : basis.index) (D : Subgroup G) (hD : coefficientBlockDefect basis ideal p label D)
    (hexp : ∀ x ∈ D, x ≠ 1 → orderOf x = p) (g : G) (hg : p ^ 2 ∣ orderOf g) :
    ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      (basis.representation χ).character g = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, v, e, -, -, huv, hprod, hu, hv⟩ := finite_prime_primary_factorization g p hp
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hu
  have hcop : Nat.Coprime (orderOf u) (orderOf v) :=
    Nat.Coprime.coprime_dvd_left hu (Nat.Coprime.pow_left e hv)
  have hord : orderOf g = orderOf u * orderOf v := by
    rw [← hprod]
    exact huv.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hp2 : p ^ 2 ∣ orderOf u := by
    rw [hord] at hg
    exact (Nat.Coprime.pow_left 2 hv).dvd_of_dvd_mul_right hg
  have hnot : ¬ subgroupSubconjugate (Subgroup.zpowers u) D := by
    rintro ⟨c, hc⟩
    have hmem : (MulAut.conj c) u ∈ D :=
      hc (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers u))
    have hord' : orderOf ((MulAut.conj c) u) = orderOf u := MulEquiv.orderOf_eq _ u
    have hle : p ^ 2 ≤ orderOf u := Nat.le_of_dvd (orderOf_pos u) hp2
    have hne : (MulAut.conj c) u ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord'
      have h2 := hp.two_le
      nlinarith
    have hpord := hexp _ hmem hne
    rw [hord'] at hpord
    rw [hpord] at hle
    have h2 := hp.two_le
    nlinarith
  exact (block_characters_vanish_outside_defect_primary basis ideal p label D hD g u v
    hprod.symm huv ⟨k, hk⟩ hv).1 hnot

end CFSG.Semidihedral.Principal
