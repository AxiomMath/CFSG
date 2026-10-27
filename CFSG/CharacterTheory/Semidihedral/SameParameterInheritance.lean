module

public import CFSG.CharacterTheory.Semidihedral.Principal.SpectrumRestrictionRigidity
public import CFSG.CharacterTheory.Semidihedral.SameParameterFourierCharacters
public import CFSG.CharacterTheory.Semidihedral.SameParameterInvolutionColumns
public import CFSG.CharacterTheory.Semidihedral.SameParameterCharacterKernels

public noncomputable section

namespace CFSG.Semidihedral.SameParameterInheritance

open CFSG.Semidihedral.Principal CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.LocalPrincipalCompatibility CFSG.Semidihedral.SameParameterSections
open CFSG.TwoRankLowerBound.Helpers CFSG.Open
open CFSG.Semidihedral.PerfectLayerNormalization CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Semidihedral.SameParameterCharacterKernels
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed

open scoped Classical in
theorem actual_local_degree_q_witness_restriction {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (basisU : FiniteIrreducibleCharacterBasis (C t))
    (principal : basis.index) (principalU : basisU.index)
    (hprincipal : (basis.representation principal).character = 1)
    (hprincipalU : (basisU.representation principalU).character = 1)
    (l : basis.index) (lU : basisU.index)
    (hl : l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hlU : lU ∈ coefficientBlock basisU (localizedComplexIntegerRing ideal) principalU)
    (hdegree : Module.finrank ℂ (basis.representation l).vector = p ^ f)
    (hdegreeU : Module.finrank ℂ (basisU.representation lU).vector = p ^ f)
    (hkernel : MonoidHom.ker (basis.representation l).representation = NZ (t : G))
    (hkernelU : MonoidHom.ker (basisU.representation lU).representation = NZ t) :
    ∀ y : C t, Odd (orderOf y) →
      (basis.representation l).character (centralizerInclusion U t y) =
        (basisU.representation lU).character y := by
  have compat := same_parameter_local_principal_character_restriction U t ht n m hn hm
    S eS SU eSU hG hU hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf hq
      hmodel hmodelU ideal
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  intro y hy
  have hyG : Odd (orderOf (centralizerInclusion U t y)) := by
    rw [orderOf_injective (centralizerInclusion U t) (centralizerInclusion_injective U t)]
    exact hy
  have hleft := local_degree_q_principal_odd_restriction_rigidity n hn S eS hG
    (t : G) htG hnonab hcentral hnc p f hp hpodd hf hmodel ideal basis principal
      hprincipal l hl hdegree hkernel (centralizerInclusion U t y) hyG
  have hright := local_degree_q_principal_odd_restriction_rigidity m hm SU eSU hU
    t ht hnonabU hcentralU hncU p f hp hpodd hf hmodelU ideal basisU principalU
      hprincipalU lU hlU hdegreeU hkernelU y hy
  change (basis.representation l).character (centralizerInclusion U t y) =
    intrinsicPhi p (t : G) (centralizerInclusion U t y) at hleft
  change (basisU.representation lU).character y = intrinsicPhi p t y at hright
  exact hleft.trans ((compat.restrictions y).2.1.trans hright.symm)

open scoped Classical in
theorem actual_family_local_witness_restriction {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G)
    (basisU : FiniteIrreducibleCharacterBasis U)
    (principal : basis.index) (principalU : basisU.index)
    (localBasis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (localBasisU : FiniteIrreducibleCharacterBasis (C t))
    (localPrincipal : localBasis.index) (localPrincipalU : localBasisU.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (hlocalPrincipalU : (localBasisU.representation localPrincipalU).character = 1)
    (q : ℕ) (hqp : q = p ^ f) (e : ℤ)
    (φ : C (t : G) → ℂ) (φU : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (α₁ α₂ α₃ α₄ : basisU.index)
    (ψ ν : ℕ → basis.index) (ψU νU : ℕ → basisU.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hfamilyU : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e (2 ^ (m - 3)) φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU) :
    ∀ y : C t, Odd (orderOf y) → φ (centralizerInclusion U t y) = φU y := by
  obtain ⟨l, hl, -, hlchar, hldeg, hlker⟩ := hfamily.1
  obtain ⟨lU, hlU, -, hlUchar, hlUdeg, hlUker⟩ := hfamilyU.1
  intro y hy
  rw [← hlchar, ← hlUchar]
  exact actual_local_degree_q_witness_restriction U t ht n m hn hm S eS SU eSU hG hU
    hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf hq hmodel hmodelU ideal
      localBasis localBasisU localPrincipal localPrincipalU hlocalPrincipal hlocalPrincipalU
      l lU hl hlU (hldeg.trans hqp) (hlUdeg.trans hqp) hlker hlUker y hy

open scoped Classical in
theorem actual_family_signed_section_restrictions {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    (hcent : (eSU (CFSG.Semidihedral.r m) : U) ^ (modulus m / 2) = t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G)
    (basisU : FiniteIrreducibleCharacterBasis U)
    (principal : basis.index) (principalU : basisU.index)
    (localBasis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (localBasisU : FiniteIrreducibleCharacterBasis (C t))
    (localPrincipal : localBasis.index) (localPrincipalU : localBasisU.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (hlocalPrincipalU : (localBasisU.representation localPrincipalU).character = 1)
    (q : ℕ) (hqp : q = p ^ f) (e : ℤ)
    (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C (t : G) → ℂ) (φU : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (α₁ α₂ α₃ α₄ : basisU.index)
    (ψ ν : ℕ → basis.index) (ψU νU : ℕ → basisU.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hfamilyU : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e (2 ^ (m - 3)) φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU)
    (hdegree : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hdegreeU : ActualPrincipalDegreeRelations basisU q δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄)
    (hregularU : ActualPrincipalCharacteristicValues basisU t
      (eSU (CFSG.Semidihedral.s m) : U) p q (2 ^ (m - 3)) e
        δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU)
    (hprincipal : (basis.representation principal).character = 1)
    (hprincipalU : (basisU.representation principalU).character = 1) :
    n = m ∧ ∃ (S' : Sylow 2 G) (eS' : SemidihedralGroup m ≃* S'),
      (S' : Subgroup G) = SU.toSubgroup.map U.subtype ∧
      (∀ a, (eS' a : G) = ((eSU a : U) : G)) ∧
      (∀ x ∈ twoSection t,
        (basis.representation χ₁).character (x : G) =
          (δ₁ * e : ℤ) * (basisU.representation α₁).character x ∧
        (basis.representation χ₂).character (x : G) =
          (-δ₂ : ℤ) * (basisU.representation α₂).character x ∧
        (basis.representation χ₃).character (x : G) =
          (-δ₃ * e : ℤ) * (basisU.representation α₃).character x) ∧
      (∀ x ∈ rotationSections eSU,
        (basis.representation χ₁).character (x : G) =
          (δ₁ * e : ℤ) * (basisU.representation α₁).character x ∧
        (basis.representation χ₂).character (x : G) =
          (-δ₂ : ℤ) * (basisU.representation α₂).character x ∧
        (basis.representation χ₃).character (x : G) =
          (-δ₃ * e : ℤ) * (basisU.representation α₃).character x) ∧
      (δ₂ = -1 → ∀ x : U, 2 ∣ orderOf x →
        (basis.representation χ₂).character (x : G) =
          (basisU.representation α₂).character x) := by
  have compat := same_parameter_local_principal_character_restriction U t ht n m hn hm
    S eS SU eSU hG hU hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf hq
      hmodel hmodelU ideal
  have hphi := actual_family_local_witness_restriction U t ht n m hn hm S eS SU eSU
    hG hU hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf hq hmodel hmodelU
      ideal basis basisU principal principalU localBasis localBasisU localPrincipal
      localPrincipalU hlocalPrincipal hlocalPrincipalU q hqp e φ φU
      δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄ ψ ν ψU νU hfamily hfamilyU
  have hnm := compat.parameters
  have hodd := compat.ambient_index
  obtain ⟨S', eS', hS', hcoe⟩ := subgroup_sylow_presentation U hodd m SU eSU
  have he' : e = 1 ∨ e = -1 := by rw [he]; split_ifs <;> simp
  have hsign1 := hregularU.1
  have hsign2 := hregularU.2.1
  have hsign3 := hregularU.2.2.1
  have hsign4 := hregularU.2.2.2.1
  rw [hsign1, hsign2, hsign3, hsign4] at hfamilyU hdegreeU
  have hinvolution := actual_family_involution_section_restrictions U t basis basisU ideal
    principal principalU localBasis localBasisU localPrincipal localPrincipalU q
      (2 ^ (m - 3)) e he' φ φU δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄ ψ ν ψU νU
      (by simpa only [hnm] using hfamily) hfamilyU hphi
  have hrotation := actual_family_rotation_section_restrictions U t ht m hm S' eS' SU eSU
    hcoe hcent hG hU hnonab hnonabU basis basisU ideal principal principalU hprincipal
      hprincipalU localBasis localBasisU localPrincipal localPrincipalU q (by omega)
      (hqp ▸ hpodd.pow) e (fun h => by simp only [he, h, ite_true])
      (fun h => by simp only [he, h, Nat.reduceEqDiff, ite_false])
      φ φU δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄ ψ ν ψU νU
      (by simpa only [hnm] using hfamily) hfamilyU hdegree hdegreeU
  refine ⟨hnm, S', eS', hS', hcoe, hinvolution, hrotation, ?_⟩
  intro hdelta
  have hzt : (eSU (CFSG.Semidihedral.z m) : U) = t := by
    rw [CFSG.Semidihedral.z, map_pow, Subgroup.coe_pow,
      ← CFSG.Semidihedral.modulus_div_two m (by omega)]
    exact hcent
  apply even_order_agreement m hm SU eSU hU t hzt
  · intro x hx
    simpa only [hdelta, neg_neg, Int.cast_one, one_mul] using (hinvolution x hx).2.1
  · intro x hx
    simpa only [hdelta, neg_neg, Int.cast_one, one_mul] using (hrotation x hx).2.1

open scoped Classical in
theorem actual_family_finite_spectrum {H : Type} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (t : H)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q k : ℕ) (e : ℤ) (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
      q e k φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    let Ψ : Fin (k - 1) → basis.index := fun j => ψ (j.val + 1)
    let N : Fin k → basis.index := fun i => ν i.val
    (∀ c, c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃ ∨ c = χ₄ ∨
        (∃ j, c = Ψ j) ∨ ∃ i, c = N i) ∧
    Function.Injective (Sum.elim ![principal, χ₁, χ₂, χ₃, χ₄] (Sum.elim Ψ N)) := by
  intro Ψ N
  obtain ⟨-, -, -, -, -, hnd, hψ, hν, hψavoid, hνavoid, hdisjoint, hblock, -⟩ := hfamily
  have hΨmem (j : Fin (k - 1)) : j.val + 1 ∈ Finset.Icc 1 (k - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have hNmem (i : Fin k) : i.val ∈ Finset.range k := Finset.mem_range.mpr i.isLt
  have hsmall : Function.Injective ![principal, χ₁, χ₂, χ₃, χ₄] := by
    have h := List.Nodup.injective_get hnd
    intro a b hab
    have hab' : ([principal, χ₁, χ₂, χ₃, χ₄] : List basis.index).get
        ⟨a.val, by simp⟩ =
      ([principal, χ₁, χ₂, χ₃, χ₄] : List basis.index).get
        ⟨b.val, by simp⟩ := by
      fin_cases a <;> fin_cases b <;> exact hab
    have hv := congrArg Fin.val (h hab')
    exact Fin.ext hv
  constructor
  · intro c
    rw [hblock]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro ((h | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩)
      · rcases h with h | h | h | h | h <;> simp only [h, true_or, or_true]
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        refine ⟨⟨j - 1, ?_⟩, ?_⟩
        · have := Finset.mem_Icc.mp hj
          omega
        · have := Finset.mem_Icc.mp hj
          dsimp [Ψ]
          congr 1
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
        exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
    · rintro (rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨i, rfl⟩)
      all_goals try simp only [true_or, or_true]
      · exact Or.inl (Or.inr ⟨j.val + 1, hΨmem j, rfl⟩)
      · exact Or.inr ⟨i.val, hNmem i, rfl⟩
  · apply Sum.elim_injective.mpr
    refine ⟨hsmall, ?_, ?_⟩
    · apply Sum.elim_injective.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro j j' h
        have hv := hψ (hΨmem j) (hΨmem j') h
        apply Fin.ext
        omega
      · intro i i' h
        exact Fin.ext (hν (hNmem i) (hNmem i') h)
      · intro j i h
        exact hdisjoint i.val (hNmem i) (j.val + 1) (hΨmem j) h.symm
    · intro a b
      rcases b with j | i
      · obtain ⟨h0, h1, h2, h3, h4⟩ := hψavoid (j.val + 1) (hΨmem j)
        fin_cases a
        · exact h0.symm
        · exact h1.symm
        · exact h2.symm
        · exact h3.symm
        · exact h4.symm
      · obtain ⟨h0, h1, h2, h3, h4⟩ := hνavoid i.val (hNmem i)
        fin_cases a
        · exact h0.symm
        · exact h1.symm
        · exact h2.symm
        · exact h3.symm
        · exact h4.symm

open scoped BigOperators Classical in
theorem sum_even_family_eq_fin {A : Type*} [AddCommMonoid A]
    (k : ℕ) (hk : 1 ≤ k) (f : ℕ → A) :
    (∑ j ∈ Finset.Icc 1 (k - 1), f j) = ∑ j : Fin (k - 1), f (j.val + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hk,
    Finset.sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  congr 1
  funext j
  rw [Nat.add_comm]

open scoped BigOperators Classical in
theorem sum_odd_family_eq_fin {A : Type*} [AddCommMonoid A] (k : ℕ) (f : ℕ → A) :
    (∑ i ∈ Finset.range k, f i) = ∑ i : Fin k, f i.val :=
  (Fin.sum_univ_eq_sum_range f k).symm

open scoped Classical in
theorem actual_family_finite_characteristic_values {H : Type} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (t s : H)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (p q k : ℕ) (e : ℤ) (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
      q e k φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hvalues : ActualPrincipalCharacteristicValues basis t s p q k e δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν) :
    (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) = (q : ℤ) ^ 3 ∧
    (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) = (q : ℤ) ^ 2 - e * q + 1 ∧
    (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) = q * ((q : ℤ) ^ 2 - e * q + 1) ∧
    (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = (q : ℤ) ^ 2 - e * q ∧
    (∀ j : Fin (k - 1),
      (Module.finrank ℂ (basis.representation (ψ (j.val + 1))).vector : ℤ) =
        (q : ℤ) ^ 3 + e) ∧
    (∀ i : Fin k, (Module.finrank ℂ (basis.representation (ν i.val)).vector : ℤ) =
      (q : ℤ) ^ 3 + e) ∧
    (basis.representation χ₂).character t = (e : ℂ) * q ∧
    (basis.representation χ₄).character t = 1 - (e : ℂ) * q := by
  obtain ⟨hφ, -, -, -, -, -, -, -, -, -, -, -, -, -, hty, -⟩ := hfamily
  obtain ⟨-, hδ₂, -, hδ₄, h1, h2, h3, h4, hψ, hν, -, -⟩ := hvalues
  obtain ⟨l, -, -, hl, hd, -⟩ := hφ
  have hφ1 : φ 1 = q := by
    rw [← hl, (basis_character_one localBasis l).1, hd]
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · intro j
    have hj : j.val + 1 ∈ Finset.Icc 1 (k - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have h := hψ (j.val + 1) hj
    rw [(basis_character_one basis _).1] at h
    exact_mod_cast h
  · intro i
    have h := hν i.val (Finset.mem_range.mpr i.isLt)
    rw [(basis_character_one basis _).1] at h
    exact_mod_cast h
  · simpa [hδ₂, hφ1] using (hty (1 : C t) (by simp)).2.1
  · simpa [hδ₄, hφ1] using (hty (1 : C t) (by simp)).2.2.2.1


open scoped BigOperators Classical in
theorem actual_family_second_character_restriction {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    (hcent : (eSU (CFSG.Semidihedral.r m) : U) ^ (modulus m / 2) = t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G)
    (basisU : FiniteIrreducibleCharacterBasis U)
    (principal : basis.index) (principalU : basisU.index)
    (localBasis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (localBasisU : FiniteIrreducibleCharacterBasis (C t))
    (localPrincipal : localBasis.index) (localPrincipalU : localBasisU.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (hlocalPrincipalU : (localBasisU.representation localPrincipalU).character = 1)
    (q : ℕ) (hqp : q = p ^ f) (e : ℤ)
    (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C (t : G) → ℂ) (φU : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (α₁ α₂ α₃ α₄ : basisU.index)
    (ψ ν : ℕ → basis.index) (ψU νU : ℕ → basisU.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hfamilyU : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e (2 ^ (m - 3)) φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU)
    (hdegree : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hdegreeU : ActualPrincipalDegreeRelations basisU q δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄)
    (hregularU : ActualPrincipalCharacteristicValues basisU t
      (eSU (CFSG.Semidihedral.s m) : U) p q (2 ^ (m - 3)) e
        δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU)
    (hprincipal : (basis.representation principal).character = 1)
    (hprincipalU : (basisU.representation principalU).character = 1) :
    (restrictRepresentation U (basis.representation χ₂)).character =
      (basisU.representation α₂).character ∧
    δ₁ = e ∧ δ₂ = -1 ∧ δ₃ = -e ∧
    (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) = (q : ℤ) ^ 3 ∧
    (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) = (q : ℤ) ^ 2 - e * q + 1 ∧
    (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) =
      q * ((q : ℤ) ^ 2 - e * q + 1) := by
  let θ₁ := restrictRepresentation U (basis.representation χ₁)
  let θ₂ := restrictRepresentation U (basis.representation χ₂)
  let θ₃ := restrictRepresentation U (basis.representation χ₃)
  have hq : 5 ≤ q := hqp ▸ hq
  have hqodd : Odd q := hqp ▸ hpodd.pow
  have he' : e = 1 ∨ e = -1 := by rw [he]; split_ifs <;> simp
  have hk : 2 ≤ 2 ^ (m - 3) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ m - 3 by omega)
    simpa only [pow_one] using h
  obtain ⟨-, -, -, -, -, -, hrotation, hEven⟩ :=
    actual_family_signed_section_restrictions U t ht n m hn hm S eS SU eSU hG hU hcent
      hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf (by simpa [hqp] using hq)
      hmodel hmodelU ideal basis basisU principal principalU localBasis localBasisU
      localPrincipal localPrincipalU hlocalPrincipal hlocalPrincipalU q hqp e he φ φU
      δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄ ψ ν ψU νU
      hfamily hfamilyU hdegree hdegreeU hregularU hprincipal hprincipalU
  have hrotation' : ∀ x ∈ rotationSections eSU,
      θ₁.character x = (δ₁ * e : ℤ) * (basisU.representation α₁).character x ∧
      θ₂.character x = (-δ₂ : ℤ) * (basisU.representation α₂).character x ∧
      θ₃.character x = (-δ₃ * e : ℤ) * (basisU.representation α₃).character x := hrotation
  obtain ⟨hT₁, hT₂, hT₃, hE, hF⟩ :=
    original_regular_rotation_pairings_of_character_restrictions hU hm ht hnonabU
        basisU ideal principalU hprincipalU localBasisU localPrincipalU q (by omega) hqodd e he'
        φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU hfamilyU eSU hcent p hregularU
        θ₁ θ₂ θ₃ δ₁ δ₂ δ₃ hrotation'
  have hphi := actual_family_local_witness_restriction U t ht n m hn hm S eS SU eSU
    hG hU hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf
      (by simpa [hqp] using hq) hmodel hmodelU ideal basis basisU principal principalU
      localBasis localBasisU localPrincipal localPrincipalU hlocalPrincipal hlocalPrincipalU
      q hqp e φ φU δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄
      ψ ν ψU νU hfamily hfamilyU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hty, hodd⟩ := hfamily
  have hrow : ∀ y : C t, Odd (orderOf y) →
      θ₁.character (t * y) = (δ₁ : ℂ) * e * φU y := by
    intro y hy
    have hy' : Odd (orderOf (centralizerInclusion U t y)) := by
      rw [orderOf_injective (centralizerInclusion U t) (centralizerInclusion_injective U t)]
      exact hy
    change (basis.representation χ₁).character
      ((t : G) * ((y : U) : G)) = (δ₁ : ℂ) * e * φU y
    rw [← centralizerInclusion_coe U t y, (hty _ hy').1, hphi y hy]
  obtain ⟨hI₁, hI₂⟩ := actual_regular_involution_pairings_of_signed_local_row m hm SU eSU hU t
      (eSU (CFSG.Semidihedral.s m) : U) ht hnonabU hcentralU hncU p f hp hpodd hf hmodelU
      ideal basisU principalU hprincipalU localBasisU localPrincipalU hlocalPrincipalU q hqp
      e he φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU hfamilyU hregularU θ₁ δ₁ hrow
  obtain ⟨hB, hdistinct⟩ := actual_family_finite_spectrum basisU ideal principalU t localBasisU
    localPrincipalU q (2 ^ (m - 3)) e φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU hfamilyU
  obtain ⟨hα₁, hα₂, hα₃, hα₄, hψ, hν, hα₂t, hα₄t⟩ :=
    actual_family_finite_characteristic_values basisU ideal principalU t
      (eSU (CFSG.Semidihedral.s m) : U) localBasisU localPrincipalU p q (2 ^ (m - 3)) e φU
      δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU hfamilyU hregularU
  obtain ⟨hf₁, hf₂, hf₃, -, hsign, -, -, hprod, -⟩ := hdegree
  have hsum : 1 + δ₁ * (Module.finrank ℂ θ₁.vector : ℤ) +
      δ₂ * (Module.finrank ℂ θ₂.vector : ℤ) +
      δ₃ * (Module.finrank ℂ θ₃.vector : ℤ) = 0 := by
    have h := (hodd 1 (by simp)).2.2.1
    rw [(basis_character_one basis χ₁).1, (basis_character_one basis χ₂).1,
      (basis_character_one basis χ₃).1] at h
    exact_mod_cast h
  apply regular_principal_spectrum_restriction_rigidity basisU ideal principalU hprincipalU
    t ht q (2 ^ (m - 3)) hq hk e he' α₁ α₂ α₃ α₄
      (fun j => ψU (j.val + 1)) (fun i => νU i.val) hB hdistinct
      hα₁ hα₂ hα₃ hα₄ hψ hν hα₂t hα₄t θ₁ θ₂ θ₃ hf₁ hf₂ hf₃
      δ₁ δ₂ δ₃ hsign hsum hprod
  · simpa only [hprincipalU] using hT₁
  · simpa only [hprincipalU] using hT₂
  · simpa only [hprincipalU] using hT₃
  · intro j
    have hj : j.val + 1 ∈ Finset.Icc 1 (2 ^ (m - 3) - 1) := by
      simp only [Finset.mem_Icc]
      omega
    simpa only [hprincipalU] using hE (j.val + 1) hj
  · intro i _
    exact hF i.val (Finset.mem_range.mpr i.isLt) 0
      (Finset.mem_range.mpr (by omega))
  · convert hI₁ using 1
    congr 1
    funext x
    simp only [regularInvolutionU,
      hprincipalU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
  · convert hI₂ using 1
    congr 1
    funext x
    simp only [regularInvolutionV,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [sum_even_family_eq_fin (2 ^ (m - 3)) (by omega),
      sum_odd_family_eq_fin (2 ^ (m - 3))]
  · exact hEven


open scoped BigOperators Classical in
theorem actual_family_ambient_characteristic_values
    {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    (hcent : (eSU (CFSG.Semidihedral.r m) : U) ^ (modulus m / 2) = t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G)
    (basisU : FiniteIrreducibleCharacterBasis U)
    (principal : basis.index) (principalU : basisU.index)
    (localBasis : FiniteIrreducibleCharacterBasis (C (t : G)))
    (localBasisU : FiniteIrreducibleCharacterBasis (C t))
    (localPrincipal : localBasis.index) (localPrincipalU : localBasisU.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (hlocalPrincipalU : (localBasisU.representation localPrincipalU).character = 1)
    (q : ℕ) (hqp : q = p ^ f) (e : ℤ)
    (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C (t : G) → ℂ) (φU : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (α₁ α₂ α₃ α₄ : basisU.index)
    (ψ ν : ℕ → basis.index) (ψU νU : ℕ → basisU.index)
    (hfamily : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hfamilyU : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e (2 ^ (m - 3)) φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU)
    (hdegree : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hdegreeU : ActualPrincipalDegreeRelations basisU q δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄)
    (hregularU : ActualPrincipalCharacteristicValues basisU t
      (eSU (CFSG.Semidihedral.s m) : U) p q (2 ^ (m - 3)) e
        δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU)
    (hprincipal : (basis.representation principal).character = 1)
    (hprincipalU : (basisU.representation principalU).character = 1) :
    n = m ∧ ∃ (S' : Sylow 2 G) (eS' : SemidihedralGroup m ≃* S'),
      (S' : Subgroup G) = SU.toSubgroup.map U.subtype ∧
      (∀ a, (eS' a : G) = ((eSU a : U) : G)) ∧
      ActualPrincipalCharacteristicValues basis (t : G) (eS' (CFSG.Semidihedral.s m) : G)
        p q (2 ^ (m - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
      (restrictRepresentation U (basis.representation χ₂)).character =
        (basisU.representation α₂).character ∧
      MonoidHom.ker (basis.representation χ₂).representation = CFSG.pPrimeCore 2 G ∧
      MonoidHom.ker (basisU.representation α₂).representation = CFSG.pPrimeCore 2 U ∧
      CFSG.pPrimeCore 2 U = (CFSG.pPrimeCore 2 G).comap U.subtype ∧
      (CFSG.pPrimeCore 2 U).map U.subtype = U ⊓ CFSG.pPrimeCore 2 G := by
  have hq : 5 ≤ q := hqp ▸ hq
  have he' : e = 1 ∨ e = -1 := by rw [he]; split_ifs <;> simp
  obtain ⟨hrestriction, hδ₁, hδ₂, hδ₃, hf₁, hf₂, hf₃⟩ :=
    actual_family_second_character_restriction U t ht n m hn hm S eS SU eSU hG hU hcent
      hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf (by simpa [hqp] using hq)
      hmodel hmodelU ideal basis basisU principal principalU localBasis localBasisU
      localPrincipal localPrincipalU hlocalPrincipal hlocalPrincipalU q hqp e he φ φU
      δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄ ψ ν ψU νU
      hfamily hfamilyU hdegree hdegreeU hregularU hprincipal hprincipalU
  obtain ⟨hnm, S', eS', hS', hcoe, -, -, -⟩ :=
    actual_family_signed_section_restrictions U t ht n m hn hm S eS SU eSU hG hU hcent
      hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf (by simpa [hqp] using hq)
      hmodel hmodelU ideal basis basisU principal principalU localBasis localBasisU
      localPrincipal localPrincipalU hlocalPrincipal hlocalPrincipalU q hqp e he φ φU
      δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄ ψ ν ψU νU
      hfamily hfamilyU hdegree hdegreeU hregularU hprincipal hprincipalU
  have hfamily' : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (m - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν := by
    simpa only [hnm] using hfamily
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hcentG : (eS' (CFSG.Semidihedral.r m) : G) ^ (modulus m / 2) = (t : G) := by
    rw [hcoe, ← Subgroup.coe_pow, hcent]
  obtain ⟨hφ1, hφnc⟩ := family_character_nonconstant hnonab localBasis ideal localPrincipal
    q φ hfamily'.1
  have hOF := actual_principal_order_formulas_of_family m hm S' eS' hG (t : G) htG
    hnonab hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal q hqp e he φ hφ1 hφnc δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ ν hfamily' hdegree eS' hcentG
  obtain ⟨-, -, horder, -⟩ := hOF
  have hf₁Q : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = (q : ℚ) ^ 3 := by
    exact_mod_cast hf₁
  have heQ : (e : ℚ) = 1 ∨ (e : ℚ) = -1 := by
    rcases he' with h | h <;> [left; right] <;> rw [h] <;> push_cast <;> rfl
  have hGorder : (Nat.card G : ℚ) =
      (Nat.card (Subgroup.centralizer ({(t : G)} : Set G)) : ℚ) ^ 3 /
      (Nat.card (Subgroup.centralizer ({(t : G)} : Set G) ⊓
        Subgroup.centralizer ({(eS' (CFSG.Semidihedral.s m) : G)} : Set G) :
          Subgroup G) : ℚ) ^ 2 * (((q : ℚ) ^ 2 - e * q + 1) / ((q : ℚ) - e) ^ 2) := by
    rw [horder, hf₁Q, hδ₁, mul_assoc,
      characteristic_order_factor heQ (by exact_mod_cast (show 1 < q by omega))]
  obtain ⟨-, -, -, -, -, hδ₄, hf₄, -, -⟩ := hdegree
  have hδ₄' : δ₄ = 1 := by rw [hδ₄, hδ₂]; norm_num
  have hf₄' : (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) =
      (q : ℤ) ^ 2 - e * q := by rw [hf₄, hf₂, hδ₂]; ring
  have hf₁C : (Module.finrank ℂ (basis.representation χ₁).vector : ℂ) = (q : ℂ) ^ 3 := by
    exact_mod_cast hf₁
  have hodd := hfamily'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hodd1 := hodd 1 (by simp)
  have hvalues : ActualPrincipalCharacteristicValues basis (t : G)
      (eS' (CFSG.Semidihedral.s m) : G) p q (2 ^ (m - 3)) e
        δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν := by
    refine ⟨hδ₁, hδ₂, hδ₃, hδ₄', hf₁, hf₂, hf₃, hf₄', ?_, ?_, hGorder, ?_⟩
    · intro j hj
      rw [hodd1.1 j hj, (basis_character_one basis χ₁).1, hf₁C, hδ₁]
    · intro i hi
      rw [hodd1.2.1 i hi, (basis_character_one basis χ₁).1, hf₁C, hδ₁]
    · let : Fact p.Prime := ⟨hp⟩
      have hpq : (p : ℤ) ∣ (q : ℤ) := by
        rw [hqp]
        push_cast
        exact dvd_pow_self _ (by omega)
      have hA0 : (q : ℤ) ^ 2 - e * q + 1 ≠ 0 := by
        rcases he' with rfl | rfl <;> nlinarith [hq]
      have hC0 : (q : ℤ) - e ≠ 0 := by rcases he' with rfl | rfl <;> omega
      have hvA : padicValInt p ((q : ℤ) ^ 2 - e * q + 1) = 0 := by
        apply padicValInt.eq_zero_of_not_dvd
        intro h
        have h1 : (p : ℤ) ∣ (q : ℤ) ^ 2 - e * q := by
          rw [show (q : ℤ) ^ 2 - e * q = (q : ℤ) * (q - e) by ring]
          exact dvd_mul_of_dvd_left hpq _
        have h2 : (p : ℤ) ∣ 1 := by
          have h3 := dvd_sub h h1
          rwa [show (q : ℤ) ^ 2 - e * q + 1 - ((q : ℤ) ^ 2 - e * q) = 1 by ring] at h3
        exact not_prime_dvd_sign hp (Or.inl rfl) h2
      have hvC : padicValInt p ((q : ℤ) - e) = 0 := by
        apply padicValInt.eq_zero_of_not_dvd
        intro h
        have he'' : -e = 1 ∨ -e = -1 := by rcases he' with rfl | rfl <;> simp
        apply not_prime_dvd_sign hp he''
        have h1 := dvd_sub h hpq
        rwa [show (q : ℤ) - e - q = -e by ring] at h1
      have h := padicValNat_order_formula (p := p)
        (c := Nat.card (Subgroup.centralizer ({(t : G)} : Set G)))
        (d := Nat.card (Subgroup.centralizer ({(t : G)} : Set G) ⊓
          Subgroup.centralizer ({(eS' (CFSG.Semidihedral.s m) : G)} : Set G) : Subgroup G))
        (g := Nat.card G) (A := (q : ℤ) ^ 2 - e * q + 1) (B := 1)
        (C := (q : ℤ) - e) (E := 1) (Q := 1)
        Nat.card_pos.ne' Nat.card_pos.ne' hA0 one_ne_zero hC0 one_ne_zero one_ne_zero
        (by rw [hGorder]; push_cast; ring)
      rw [hvA, hvC, padicValInt.one] at h
      linarith
  have hkernel := actual_regular_second_character_kernel m hm S' eS' hG (t : G) htG
    basis ideal principal
      hprincipal localBasis localPrincipal p q hq e φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν
      hfamily' hvalues
  have hkernelU := actual_regular_second_character_kernel m hm SU eSU hU t ht
    basisU ideal principalU
      hprincipalU localBasisU localPrincipalU p q hq e φU δ₁U δ₂U δ₃U δ₄U
      α₁ α₂ α₃ α₄ ψU νU hfamilyU hregularU
  have hcore := actual_regular_odd_core_intersection U t ht m m hm hm S' eS' SU eSU
    hG hU basis basisU
      ideal principal principalU hprincipal hprincipalU localBasis localBasisU localPrincipal
      localPrincipalU p q hq e φ φU δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U χ₁ χ₂ χ₃ χ₄
      α₁ α₂ α₃ α₄ ψ ν ψU νU hfamily' hvalues hfamilyU hregularU hrestriction
  exact ⟨hnm, S', eS', hS', hcoe, hvalues, hrestriction, hkernel, hkernelU, hcore⟩


open scoped BigOperators Classical in
theorem actual_same_parameter_regularity_and_odd_core_intersection
    {G : Type} [Group G] [Fintype G]
    (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2) (hU : ∀ V : Subgroup U, V.index ≠ 2)
    (hcent : (eSU (CFSG.Semidihedral.r m) : U) ^ (modulus m / 2) = t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (hval : 3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set U))) : ℤ) -
        2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set U) ⊓
          Subgroup.centralizer ({(eSU (CFSG.Semidihedral.s m) : U)} : Set U) : Subgroup U)) : ℤ) ≤
      padicValNat p (Nat.card U)) :
    n = m ∧ ∃ (S' : Sylow 2 G) (eS' : SemidihedralGroup m ≃* S'),
      (S' : Subgroup G) = SU.toSubgroup.map U.subtype ∧
      (∀ a, (eS' a : G) = ((eSU a : U) : G)) ∧
      (Nat.card G : ℚ) =
        (Nat.card (Subgroup.centralizer ({(t : G)} : Set G)) : ℚ) ^ 3 /
        (Nat.card (Subgroup.centralizer ({(t : G)} : Set G) ⊓
          Subgroup.centralizer ({((eSU (CFSG.Semidihedral.s m) : U) : G)} : Set G) :
            Subgroup G) : ℚ) ^ 2 *
          ((((p ^ f : ℕ) : ℚ) ^ 2 - (if p ^ f % 4 = 1 then 1 else -1) * p ^ f + 1) /
            (((p ^ f : ℕ) : ℚ) - (if p ^ f % 4 = 1 then 1 else -1)) ^ 2) ∧
      (padicValNat p (Nat.card G) : ℤ) =
        3 * (padicValNat p (Nat.card (Subgroup.centralizer ({(t : G)} : Set G))) : ℤ) -
        2 * (padicValNat p (Nat.card (Subgroup.centralizer ({(t : G)} : Set G) ⊓
          Subgroup.centralizer ({((eSU (CFSG.Semidihedral.s m) : U) : G)} : Set G) :
            Subgroup G)) : ℤ) ∧
      CFSG.pPrimeCore 2 U = (CFSG.pPrimeCore 2 G).comap U.subtype ∧
      (CFSG.pPrimeCore 2 U).map U.subtype = U ⊓ CFSG.pPrimeCore 2 G ∧
      ∃ (basis : FiniteIrreducibleCharacterBasis G)
        (basisU : FiniteIrreducibleCharacterBasis U)
        (principal : basis.index) (principalU : basisU.index)
        (χ : basis.index) (α : basisU.index),
        (basis.representation principal).character = 1 ∧
        (basisU.representation principalU).character = 1 ∧
        χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
        α ∈ coefficientBlock basisU (localizedComplexIntegerRing ideal) principalU ∧
        (Module.finrank ℂ (basis.representation χ).vector : ℤ) =
          ((p ^ f : ℕ) : ℤ) ^ 2 - (if p ^ f % 4 = 1 then 1 else -1) * p ^ f + 1 ∧
        (Module.finrank ℂ (basisU.representation α).vector : ℤ) =
          ((p ^ f : ℕ) : ℤ) ^ 2 - (if p ^ f % 4 = 1 then 1 else -1) * p ^ f + 1 ∧
        (restrictRepresentation U (basis.representation χ)).character =
          (basisU.representation α).character ∧
        MonoidHom.ker (basis.representation χ).representation = CFSG.pPrimeCore 2 G ∧
        MonoidHom.ker (basisU.representation α).representation = CFSG.pPrimeCore 2 U := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨basisU⟩ := finiteIrreducibleCharacterBasis_exists (G := U)
  obtain ⟨principalU, hprincipalU⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisU
    (principalFiniteComplexRepresentation U) (principalFiniteComplexRepresentation_isIrreducible U)
  rw [principalFiniteComplexRepresentation_character] at hprincipalU
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C (t : G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C (t : G)))
      (principalFiniteComplexRepresentation_isIrreducible (C (t : G)))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨localBasisU⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipalU, hlocalPrincipalU⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasisU (principalFiniteComplexRepresentation (C t))
      (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipalU
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, hφ1, hφnc, δ₁, δ₂, δ₃, δ₄,
      χ₁, χ₂, χ₃, χ₄, ψ, ν, hfamily, hdegree, -⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S eS hG (t : G) htG hnonab hcentral
      hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  let φ : C (t : G) → ℂ := fun c =>
    (Nat.card {x : Omega F // ((ρ (kappa (t : G) c) : coordinateE F) :
      Equiv.Perm (Omega F)) x = x} : ℂ) - 1
  obtain ⟨FU, hFU, hFUfin, ρU, hcardU, -, -, -, -, -, δ₁U, δ₂U, δ₃U, δ₄U,
      α₁, α₂, α₃, α₄, ψU, νU, hfamilyU, hdegreeU, hregularU⟩ :=
    actual_nonsimple_layer_characteristic_valuation_degree_formulas m hm SU eSU hU t ht
      hnonabU hcentralU hncU p f hp hpodd hf hmodelU ideal basisU principalU hprincipalU
      localBasisU localPrincipalU hlocalPrincipalU eSU hcent hval
  let φU : C t → ℂ := fun c =>
    (Nat.card {x : Omega FU // ((ρU (kappa t c) : coordinateE FU) :
      Equiv.Perm (Omega FU)) x = x} : ℂ) - 1
  let q := p ^ f
  let e : ℤ := if q % 4 = 1 then 1 else -1
  have hfamily' : ActualPrincipalBlockFamily basis ideal principal (t : G) localBasis
      localPrincipal q e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν := by
    simpa only [hcard] using hfamily
  have hfamilyU' : ActualPrincipalBlockFamily basisU ideal principalU t localBasisU
      localPrincipalU q e (2 ^ (m - 3)) φU δ₁U δ₂U δ₃U δ₄U α₁ α₂ α₃ α₄ ψU νU := by
    simpa only [hcardU] using hfamilyU
  have hdegree' : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ := by
    simpa only [hcard] using hdegree
  have hdegreeU' : ActualPrincipalDegreeRelations basisU q δ₁U δ₂U δ₃U δ₄U
      α₁ α₂ α₃ α₄ := by simpa only [hcardU] using hdegreeU
  have hregularU' : ActualPrincipalCharacteristicValues basisU t
      (eSU (CFSG.Semidihedral.s m) : U) p q (2 ^ (m - 3)) e δ₁U δ₂U δ₃U δ₄U
      α₁ α₂ α₃ α₄ ψU νU := by simpa only [hcardU] using hregularU
  obtain ⟨hnm, S', eS', hS', hcoe, hvalues, hrestriction, hkernel, hkernelU, hcomap, hmap⟩ :=
    actual_family_ambient_characteristic_values U t ht n m hn hm S eS SU eSU hG hU hcent
      hnonab hnonabU hcentral hcentralU hnc hncU p f hp hpodd hf hq hmodel hmodelU
      ideal basis basisU principal principalU localBasis localBasisU localPrincipal
      localPrincipalU hlocalPrincipal hlocalPrincipalU q rfl e rfl φ φU
      δ₁ δ₂ δ₃ δ₄ δ₁U δ₂U δ₃U δ₄U χ₁ χ₂ χ₃ χ₄ α₁ α₂ α₃ α₄ ψ ν ψU νU
      hfamily' hfamilyU' hdegree' hdegreeU' hregularU' hprincipal hprincipalU
  obtain ⟨-, -, -, -, -, hdegG, -, -, -, -, horder, hvaluation⟩ := hvalues
  have hdegU := hregularU'.2.2.2.2.2.1
  rw [hcoe] at horder hvaluation
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hblockG, -⟩ := hfamily'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hblockU, -⟩ := hfamilyU'
  have hχ : χ₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    rw [hblockG]
    simp
  have hα : α₂ ∈ coefficientBlock basisU (localizedComplexIntegerRing ideal) principalU := by
    rw [hblockU]
    simp
  refine ⟨hnm, S', eS', hS', hcoe, ?_, hvaluation, hcomap, hmap,
    basis, basisU, principal, principalU, χ₂, α₂, hprincipal, hprincipalU, hχ, hα,
    ?_, ?_, hrestriction, hkernel, hkernelU⟩
  · simpa only [q, e, Int.cast_ite, Int.cast_one, Int.cast_neg, Nat.cast_pow] using horder
  · simpa only [q, e, Nat.cast_pow] using hdegG
  · simpa only [q, e, Nat.cast_pow] using hdegU

end CFSG.Semidihedral.SameParameterInheritance
