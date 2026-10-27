module

public import CFSG.CharacterTheory.Wreathed.ConditionalEveryFlatPrincipal
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBases
public import CFSG.CharacterTheory.Wreathed.ConditionalExactOrderPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatEvery

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.FlatTwistedBases
  CFSG.Wreathed.LinearLocalTwistMoment

theorem flat_cubic_moment
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (B : basis.index) (hflat : FlatWreathedBlock basis ideal S e B)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θB : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θB θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (basis.representation χ).character
          (wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2)) ^ 3 /
        (basis.representation χ).character 1 =
      ((2 ^ n : ℕ) : ℂ) ^ 2 *
        (((p ^ f : ℕ) : ℂ) + ((if p ^ f % 4 = 1 then 1 else -1 : ℤ) : ℂ)) ^ 2 /
        (((p ^ f : ℕ) : ℂ) ^ 2 + ((if p ^ f % 4 = 1 then 1 else -1 : ℤ) : ℂ) * ((p ^ f : ℕ) : ℂ) +
          1) := by
  obtain ⟨-, ⟨lam, hlam⟩, hall⟩ := conditional_flat_local_twisted_regular_bases hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  obtain ⟨eb₀, θ₀, nb₀, θhat₀, hθ₀1, hθ₀, hB₀, hflat₀⟩ := principal_flat basis ideal hn S e
  obtain ⟨-, -, hall₀⟩ := conditional_flat_local_twisted_regular_bases hnonab n hn S e hfour p f
    hp hpodd hf hmodel ideal basis (principalCharacterLabel basis) hflat₀ eb₀ θ₀ nb₀ θhat₀ hθ₀ hB₀
    η hη hord
  have hext₀ := hall₀ 1 ⟨fun v z _ => by rw [hθ₀1]; rfl, fun v _ => rfl, fun c c' _ _ => rfl⟩
  have hxorder := CompatibleFamilies.orderOf_x S e hn
  have hxp := involution_zpowers_isPGroup _ hxorder
  have hxu : wreathModelHom S e (Original.x (2 ^ n)) ∈
      Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) := Subgroup.mem_zpowers _
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer
    (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) : Set G))
  obtain ⟨hcent, -, hlocal⟩ := (hall lam hlam).1 _ hxp hxu
  obtain ⟨⟨ℓ, hℓ⟩, hℓall⟩ := hlocal basisN
  obtain ⟨hbr, hun, hblk⟩ := hℓall ℓ (principalCharacterLabel basisN) hℓ
    (principalCharacterLabel_character basisN)
  obtain ⟨-, -, hlocal₀⟩ := hext₀.1 _ hxp hxu
  obtain ⟨-, hℓall₀⟩ := hlocal₀ basisN
  obtain ⟨hbr₀, hun₀, -⟩ := hℓall₀ (principalCharacterLabel basisN) (principalCharacterLabel basisN)
    (fun c => by rw [principalCharacterLabel_character]; rfl)
    (principalCharacterLabel_character basisN)
  let lam' : Subgroup.centralizer (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) :
      Set G) →* ℂˣ :=
    lam.comp (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu))
  have htw : coefficientBlock basisN (localizedComplexIntegerRing ideal) ℓ =
      linearTwistedBlock basisN lam' (principalCoefficientBlock basisN ideal) :=
    Finset.ext fun θ' => by rw [hblk θ', mem_linearTwistedBlock]; rfl
  have hSN : (S : Subgroup G) ≤ Subgroup.centralizer
      (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) : Set G) := by
    rw [hcent]
    exact sylow_le_involutionCentralizer n hn S e
  have hmom := linear_local_twist_preserves_involution_cubic_moment_of_sylow_trivial basis ideal
    _ hxorder basisN B ℓ lam' S hSN (fun s hs => hlam.2.1 _ hs) htw hbr₀
    (fun θ hθ' => (coefficientBlock_mem_iff _ _ _ _).mpr
      (sameCoefficientBlock_symm _ _ (hun₀ θ hθ'))) hbr
    (fun θ hθ' => (coefficientBlock_mem_iff _ _ _ _).mpr
      (sameCoefficientBlock_symm _ _ (hun θ hθ')))
  let _ : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  obtain ⟨F, _, _, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel
  have h0 := ConditionalExactOrder.conditional_principal_cubic_sum hnonab n hn S e hfour p f hp
    hpodd hf hmodel ideal basis (principalCharacterLabel basis)
    (principalCharacterLabel_character basis) F Sigma b hSigma ρ Ψ hdata
  rw [hdata.card] at h0
  rw [wreathModelHom_x_eq] at hmom
  rw [hmom]
  exact h0

end CFSG.Wreathed.FlatEvery
