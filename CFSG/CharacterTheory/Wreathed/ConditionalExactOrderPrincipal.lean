module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegrees
public import CFSG.CharacterTheory.Wreathed.ConditionalExactOrderSum

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalExactOrder

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalSquareRoot
  CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalFirstFourierRows
  CFSG.Wreathed.ConditionalOddFourier CFSG.Wreathed.ConditionalFiveFixed
  CFSG.Wreathed.ConditionalCompleteBase CFSG.Wreathed.ConditionalGlobalDegrees

theorem conditional_principal_cubic_sum_of_localHyp
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character
          (wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2)) ^ 3 /
        (basis.representation χ).character 1 =
      ((2 ^ n : ℕ) : ℂ) ^ 2 *
        ((Nat.card F : ℂ) + ((if Nat.card F % 4 = 1 then 1 else -1 : ℤ) : ℂ)) ^ 2 /
        ((Nat.card F : ℂ) ^ 2 + ((if Nat.card F % 4 = 1 then 1 else -1 : ℤ) : ℂ) * Nat.card F +
          1) := by
  have H := (conditional_global_principal_degrees_and_involution_values_of_localHyp n hn S e p f hp
    hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨⟨σ0, υ0, g0, hg0⟩, H⟩ := H
  have hm0 : 0 < 2 * 2 ^ n := by positivity
  have hθ := Complex.isPrimitiveRoot_exp (2 * 2 ^ n) hm0.ne'
  have hζ := hθ.pow hm0 (show 2 * 2 ^ n = 2 * 2 ^ n from rfl)
  obtain ⟨⟨v, hv⟩, H⟩ := H _ hζ _ hθ rfl
  obtain ⟨⟨lam, hlam⟩, H⟩ := H v hv ⟨σ0, hg0.left_mem⟩ ⟨υ0, hg0.right_mem⟩ g0 hg0
  obtain ⟨⟨α, β, η, σ, χ, δ, e₀, hcons⟩, H⟩ := H lam hlam
  obtain ⟨⟨ω, iB, iD, τ₀, κ, γ, εs, hcore, heven⟩, H⟩ := H α β η σ χ δ e₀ hcons
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨V, hV6, hVrep⟩ := ConditionalFiveFixed.exists_orbit_representatives
    (K := dualGroup (2 ^ n)) (X := ZMod (2 ^ n) × ZMod (2 ^ n)) (fun O => O.ncard = 6)
  obtain ⟨⟨P, Q, er, ψ, ρ₀, Δ, hW⟩, H⟩ := H ω iB iD τ₀ κ γ εs hcore heven V hV6 hVrep
  obtain ⟨-, ⟨hdA, hdB, hdD, hdω, hdχ, hdPQ, hdψ, -⟩, -,
    ⟨hx1, hxA, hxB, hxD, hxω, hxχ, hxPQ, hxψ⟩, -, hE, hO, -⟩ := H P Q er ψ ρ₀ Δ hW
  obtain ⟨hlab, -, -, -, -, -, -, -, hψinj, hψ, -, -, -, -, hBunion, -, -⟩ := hW
  obtain ⟨hinj, hα, -, -, -, hχinj, hχ, -⟩ := hcons
  obtain ⟨-, hωp, hωα, hωχ, hBe, hDe, hBD, -⟩ := hcore
  obtain ⟨hγε, hγinj, hγdisj, hγav, -⟩ := heven
  have BF : BlockFamilies principal (α e₀) (α iB) (α iD) ω (2 ^ n / 2)
      ((Finset.Ico 1 (2 ^ n)).filter Odd) χ γ P Q ψ V :=
    { hAp := (hα e₀).2
      hBp := (hα iB).2
      hDp := (hα iD).2
      hωp := hωp
      hBA := fun h => hBe (hinj h)
      hDA := fun h => hDe (hinj h)
      hωA := hωα e₀
      hDB := fun h => hBD (hinj h).symm
      hωB := hωα iB
      hωD := hωα iD
      hχcore := fun j hj => ⟨(hχ j hj).2.1, (hχ j hj).2.2 e₀, (hχ j hj).2.2 iB,
        (hχ j hj).2.2 iD, fun h => hωχ j hj h.symm⟩
      hχinj := hχinj
      γinj := hγinj
      γcore := fun r hr l => ⟨(hγav r hr l).1, (hγav r hr l).2.1, (hγav r hr l).2.2.1,
        (hγav r hr l).2.2.2.1, (hγav r hr l).2.2.2.2.1⟩
      γodd := fun r hr l j hj => (hγav r hr l).2.2.2.2.2 j hj
      disj := hγdisj
      lab := fun r hr => (hlab r hr).1
      gen := fun I hI => ⟨(hψ I hI).2.1, (hψ I hI).2.2.1, (hψ I hI).2.2.2.1,
        (hψ I hI).2.2.2.2.1, (hψ I hI).2.2.2.2.2.1, (hψ I hI).2.2.2.2.2.2.1,
        (hψ I hI).2.2.2.2.2.2.2.1⟩
      geninj := hψinj }
  have hεs : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
      (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    split_ifs <;> simp
  have hq3 : 3 ≤ Nat.card F := by
    rw [hdata.card]
    exact three_le_prime_pow hp hpodd hf
  have h1 : ∀ φ, (basis.representation φ).character 1 =
      ((Module.finrank ℂ (basis.representation φ).vector : ℤ) : ℂ) := fun φ => by
    rw [FiniteComplexRepresentation.character, Representation.char_one, Int.cast_natCast]
  exact cubic_sum_of_data BF hBunion hn (fun φ => (basis.representation φ).character 1)
    (fun φ => (basis.representation φ).character
      (wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2)))
    (fun φ => (Module.finrank ℂ (basis.representation φ).vector : ℤ)) hεs hq3 h1
    (congrFun hprincipal 1) hdA hdB hdD hdω hdχ hdPQ hdψ hx1 hxA hxB hxD hxω hxχ hxPQ hxψ hE hO

theorem conditional_principal_cubic_sum
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character
          (wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2)) ^ 3 /
        (basis.representation χ).character 1 =
      ((2 ^ n : ℕ) : ℂ) ^ 2 *
        ((Nat.card F : ℂ) + ((if Nat.card F % 4 = 1 then 1 else -1 : ℤ) : ℂ)) ^ 2 /
        ((Nat.card F : ℂ) ^ 2 + ((if Nat.card F % 4 = 1 then 1 else -1 : ℤ) : ℂ) * Nat.card F +
          1) :=
  conditional_principal_cubic_sum_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal F Sigma b hSigma ρ Ψ hdata

end CFSG.Wreathed.ConditionalExactOrder
