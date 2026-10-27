module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompatibleModelData
public import CFSG.CharacterTheory.Wreathed.ConditionalOddFourierCharacters
public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusion

public section

open scoped Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalFourier

structure ConditionalLocalHyp {G : Type} [Group G] [Fintype G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) : Prop where
  modelData : ∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ
  layerNoncyclic : ∃ U : Sylow 2 (centralizerSimpleLayer n hn S e),
    ¬ IsCyclic (U : Subgroup (centralizerSimpleLayer n hn S e))
  qTwoPart : 2 ^ ((p ^ f) ^ 2 - 1).factorization 2 = 2 * 2 ^ n
  adaptedBase : ∃ σ υ g : G, IsAdaptedBase (modelBase S e)
    (wreathModelHom S e (Original.a (2 ^ n))) (wreathModelHom S e (Original.z (2 ^ n))) σ υ g
  involutions_conj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y
  principal_degree : ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index), (basis.representation principal).character = 1 →
    ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ψ ≠ principal → 2 ≤ basisDegree basis ψ

theorem ConditionalLocalHyp.of_isSimpleGroup
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f) :
    ConditionalLocalHyp n hn S e p f where
  modelData := exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel
  layerNoncyclic := by
    obtain ⟨-, -, -, -, -, hSylow, -⟩ :=
      centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
    let U : Sylow 2 (centralizerSimpleLayer n hn S e) := Classical.choice Sylow.nonempty
    obtain ⟨eU⟩ := hSylow U
    exact ⟨U, dihedral_sylow_not_isCyclic n hn eU⟩
  qTwoPart := by
    obtain ⟨F', _, _, hcard', -, -, theta', rho', eta', hin', hrho', -, hdata'⟩ :=
      FullCentralizerFromProjectiveModel.actual_projective_model_determines_full_centralizer
        hnonab n hn S e hfour p f hp hpodd hf hmodel
    rw [← hcard']
    exact hdata'.structural.q_two_part
  adaptedBase := (adapted_base_fusion_model hnonab n hn S e).1
  involutions_conj := (simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e).2.2.1
  principal_degree := fun _ _ _ _ _ hprincipal _ _ hψ =>
    ConditionalOddFourier.two_le_basisDegree hnonab hprincipal hψ

end CFSG.Wreathed
