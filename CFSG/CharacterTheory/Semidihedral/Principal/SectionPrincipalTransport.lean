module

public import CFSG.CharacterTheory.Semidihedral.Principal.SectionInductionIsometry
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalSectionIntertwining
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalProjectionTransport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

theorem inv_mem_centralInvolutionSection {G : Type*} [Group G] {t x : G}
    (hx : x ∈ centralInvolutionSection t) : x⁻¹ ∈ centralInvolutionSection t := by
  obtain ⟨hxC, heven, hpow⟩ := hx
  refine ⟨Subgroup.inv_mem _ hxC, by rwa [orderOf_inv], ?_⟩
  have ht2 : t * t = 1 := by
    rw [← hpow, ← pow_add, ← two_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp heven),
      pow_orderOf_eq_one]
  rw [orderOf_inv, inv_pow, hpow]
  exact inv_eq_of_mul_eq_one_right ht2

theorem mem_zpowers_primary_of_mem_centralInvolutionSection {G : Type*} [Group G] [Finite G]
    {t x u y : G} (hx : x ∈ centralInvolutionSection t) (hy : y ∈ Subgroup.zpowers x⁻¹)
    (hcomm : Commute u y) (hprod : u * y = x⁻¹) (hyodd : Nat.Coprime 2 (orderOf y)) :
    t ∈ Subgroup.zpowers u := by
  obtain ⟨_, heven, hpow⟩ := hx
  have hym : orderOf y ∣ orderOf x := by
    have h := orderOf_dvd_of_mem_zpowers hy
    rwa [orderOf_inv] at h
  have hym2 : orderOf y ∣ orderOf x / 2 := by
    have h2 : orderOf x = orderOf x / 2 * 2 :=
      (Nat.div_mul_cancel (even_iff_two_dvd.mp heven)).symm
    rw [h2] at hym
    exact hyodd.symm.dvd_of_dvd_mul_right hym
  have hy1 : y ^ (orderOf x / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hym2
  have hxu : x = u⁻¹ * y⁻¹ := by
    rw [(hcomm.inv_inv).eq, ← mul_inv_rev, hprod, inv_inv]
  have hkey : ∀ k : ℕ, y ^ k = 1 → x ^ k = u⁻¹ ^ k := by
    intro k hk
    rw [hxu, (hcomm.inv_inv).mul_pow, inv_pow y, hk, inv_one, mul_one]
  rw [← hpow, hkey _ hy1]
  exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers u)) _

theorem finiteIrreducibleCharacterBasis_exists_principal_label {E : Type*} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) :
    ∃ label : basis.index, (basis.representation label).character = 1 := by
  obtain ⟨label, hlabel⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation E) (principalFiniteComplexRepresentation_isIrreducible E)
  exact ⟨label, hlabel.trans (principalFiniteComplexRepresentation_character E)⟩

theorem principalProjection_eq_on_centralInvolutionSection {G : Type*} [Group G] [Fintype G]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G)
    (basisG : FiniteIrreducibleCharacterBasis G) (principalG : basisG.index)
    (hprincipalG : (basisG.representation principalG).character = 1)
    (basisC : FiniteIrreducibleCharacterBasis (Subgroup.centralizer ({t} : Set G)))
    (principalC : basisC.index) (hprincipalC : (basisC.representation principalC).character = 1)
    (f : G → ℂ)
    (hf : ∀ element conjugator : G, f (conjugator * element * conjugator⁻¹) = f element)
    (x : Subgroup.centralizer ({t} : Set G)) (hx : (x : G) ∈ centralInvolutionSection t) :
    characterSubsetProjection basisG
        (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG) f x =
      characterSubsetProjection basisC
        (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)
        (fun y => f y) x := by
  obtain ⟨u, y, n, hu, hy, hcomm, hprod, hun, hyodd⟩ :=
    finite_prime_primary_factorization ((x : G)⁻¹) 2 Nat.prime_two
  have htu : t ∈ Subgroup.zpowers u :=
    mem_zpowers_primary_of_mem_centralInvolutionSection hx hy hcomm hprod hyodd
  have hzC : Subgroup.zpowers (x : G)⁻¹ ≤ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr ((Subgroup.centralizer ({t} : Set G)).inv_mem x.2)
  have huC : u ∈ Subgroup.centralizer ({t} : Set G) := hzC hu
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := hzC hy
  set E := Subgroup.centralizer (Subgroup.zpowers u : Set G)
  have hEC : E ≤ Subgroup.centralizer ({t} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hz h htu
  have hyE : y ∈ E := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hcomm.zpow_left k).eq
  let uC : Subgroup.centralizer ({t} : Set G) := ⟨u, huC⟩
  let yC : Subgroup.centralizer ({t} : Set G) := ⟨y, hyC⟩
  set E' := Subgroup.centralizer (Subgroup.zpowers uC : Set (Subgroup.centralizer ({t} : Set G)))
  have hmemE' : ∀ z : Subgroup.centralizer ({t} : Set G), z ∈ E' ↔ (z : G) ∈ E := by
    intro z
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hz h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have h' := congrArg Subtype.val (hz (uC ^ k) (Subgroup.zpow_mem_zpowers uC k))
      simpa [uC] using h'
    · intro hz h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      apply Subtype.ext
      simpa [uC] using hz (u ^ k) (Subgroup.zpow_mem_zpowers u k)
  have hyE' : yC ∈ E' := (hmemE' yC).mpr hyE
  let ψ : E' ≃* E :=
    { toFun := fun z => ⟨(z : Subgroup.centralizer ({t} : Set G)), (hmemE' z).mp z.2⟩
      invFun := fun w => ⟨⟨w, hEC w.2⟩, (hmemE' _).mpr w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨basisE⟩ := finiteIrreducibleCharacterBasis_exists (G := E)
  obtain ⟨basisE'⟩ := finiteIrreducibleCharacterBasis_exists (G := E')
  obtain ⟨principalE, hprincipalE⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisE
  obtain ⟨principalE', hprincipalE'⟩ :=
    finiteIrreducibleCharacterBasis_exists_principal_label basisE'
  have hyodd' : Nat.Coprime 2 (orderOf (⟨y, hyE⟩ : E).val) := hyodd
  have hG := principal_local_section_projection basisG ideal 2 principalG hprincipalG u n hun
    basisE principalE hprincipalE ⟨y, hyE⟩ hyodd' f hf
  have hun' : orderOf uC ∣ 2 ^ n := by
    rw [Subgroup.orderOf_mk]
    exact hun
  have hyoddC : Nat.Coprime 2 (orderOf (⟨yC, hyE'⟩ : E').val) := by
    change Nat.Coprime 2 (orderOf yC)
    rw [Subgroup.orderOf_mk]
    exact hyodd
  have hC := principal_local_section_projection basisC ideal 2 principalC hprincipalC uC n hun'
    basisE' principalE' hprincipalE' ⟨yC, hyE'⟩ hyoddC (fun z => f z)
    (fun element conjugator => hf element conjugator)
  have hT := principal_projection_transport basisE' basisE (localizedComplexIntegerRing ideal) ψ
    principalE' hprincipalE' principalE hprincipalE
    (fun z => f ((z : Subgroup.centralizer ({t} : Set G)) : G))
    (fun element conjugator => hf element conjugator)
    (((⟨u, element_mem_centralizer_zpowers u⟩ : E) * ⟨y, hyE⟩)⁻¹)
  have hval : ((((⟨u, element_mem_centralizer_zpowers u⟩ : E) * ⟨y, hyE⟩)⁻¹ : E) : G) =
      (x : G) := by
    simp [hprod]
  have hvalC : (((⟨uC, element_mem_centralizer_zpowers uC⟩ : E') * ⟨yC, hyE'⟩)⁻¹ : E').val =
      x := by
    apply Subtype.ext
    simp [uC, yC, hprod]
  have hsymm : ψ.symm (((⟨u, element_mem_centralizer_zpowers u⟩ : E) * ⟨y, hyE⟩)⁻¹) =
      ((⟨uC, element_mem_centralizer_zpowers uC⟩ : E') * ⟨yC, hyE'⟩)⁻¹ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hval] at hG
  rw [hvalC] at hC
  rw [← hG, ← hC, ← hsymm, ← hT]
  rfl

theorem characterSubsetProjection_eq_sum_blocksInnerProduct {E : Type} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (support : Finset basis.index) (f : E → ℂ) :
    characterSubsetProjection basis support f =
      ∑ label ∈ support, BlocksInnerProduct f (basis.representation label).character •
        (basis.representation label).character := by
  change (∑ label ∈ support, characterPairing f (basis.representation label).character •
    (basis.representation label).character) = _
  apply Finset.sum_congr rfl
  intro label _
  have hmem : (basis.representation label).character ∈ BlocksIrr E := by
    rw [blocksIrr_eq_irreducible_characters]
    exact ⟨basis.representation label, basis.irreducible label, rfl⟩
  rw [blocksInnerProduct_eq_characterPairing f (AddSubgroup.subset_closure hmem)]

theorem central_involution_section_principal_block_transport {G : Type} [Group G] [Fintype G]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (t : G)
    (basisG : FiniteIrreducibleCharacterBasis G) (principalG : basisG.index)
    (hprincipalG : (basisG.representation principalG).character = 1)
    (basisC : FiniteIrreducibleCharacterBasis (Subgroup.centralizer ({t} : Set G)))
    (principalC : basisC.index)
    (hprincipalC : (basisC.representation principalC).character = 1) :
    (∀ f : G → ℂ, BlocksIsClassFunction f →
      characterFunctionMask
          {x : Subgroup.centralizer ({t} : Set G) | (x : G) ∈ centralInvolutionSection t}
          (fun x => characterSubsetProjection basisG
            (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG) f x) =
        characterFunctionMask
          {x : Subgroup.centralizer ({t} : Set G) | (x : G) ∈ centralInvolutionSection t}
          (characterSubsetProjection basisC
            (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)
            (fun x => f x))) ∧
    ∀ α ∈ coefficientCharacterSpace basisC
        (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC),
      (∀ x : Subgroup.centralizer ({t} : Set G),
        (x : G) ∉ centralInvolutionSection t → α x = 0) →
      inducedFunction (Subgroup.centralizer ({t} : Set G)) α ∈
        coefficientCharacterSpace basisG
          (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG) := by
  refine ⟨fun f hf => ?_, fun α hα hsupport => ?_⟩
  · funext x
    simp only [characterFunctionMask]
    split_ifs with hx
    · exact principalProjection_eq_on_centralInvolutionSection ideal t basisG principalG
        hprincipalG basisC principalC hprincipalC f
        (fun element conjugator => hf element conjugator) x hx
    · rfl
  · apply supported_inducedFunction_mem_coefficientCharacterSpace _ basisG _ basisC _
      {x : Subgroup.centralizer ({t} : Set G) | (x : G) ∈ centralInvolutionSection t} α hα
      hsupport
    intro label hlabel element helement
    have hinv : ((element⁻¹ : Subgroup.centralizer ({t} : Set G)) : G) ∈
        centralInvolutionSection t := by
      rw [Subgroup.coe_inv]
      exact inv_mem_centralInvolutionSection helement
    rw [← principalProjection_eq_on_centralInvolutionSection ideal t basisG principalG
      hprincipalG basisC principalC hprincipalC _
      (fun element conjugator => Representation.char_conj _ element conjugator) element⁻¹ hinv,
      characterSubsetProjection_character_not_mem basisG _ label hlabel]
    rfl

end CFSG.Semidihedral.Principal
