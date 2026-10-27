module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionFixedComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalIndexTwoB

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalInvolutionFixedComponents

theorem fixed_twoComponents_of_simple_model {M : Type*} [Group M] [IsSimpleGroup M]
    (hnonab : ∃ a b : M, a * b ≠ b * a)
    (hfixed : ∀ alpha : MulAut M, alpha * alpha = 1 → alpha ≠ 1 → ∀ r : ℕ, r.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
        CFSG.IsPComponent r L → CFSG.IsQuasisimple L)
    (alpha : MulAut M) (hinv : Function.Involutive alpha)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha))
    (hL : TwoComponents.IsTwoComponent L) : CFSG.Open.IsQuasisimple L := by
  have hL2 := (CatalogueBAlternating.pComponent_two_iff L).mpr hL
  have hsq : alpha * alpha = 1 := MulEquiv.ext fun x => hinv x
  by_cases h1 : alpha = 1
  · subst h1
    have htop : FixedCommutingProduct.fixedSubgroup (1 : MulAut M) = ⊤ := by
      ext x
      exact ⟨fun _ => Subgroup.mem_top x, fun _ => rfl⟩
    let e : FixedCommutingProduct.fixedSubgroup (1 : MulAut M) ≃* M :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have hM : CFSG.IsQuasisimple M := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
    have hfix : CFSG.IsQuasisimple (FixedCommutingProduct.fixedSubgroup (1 : MulAut M)) :=
      CatalogueBAlternating.quasisimple_iff_native.mpr
        (Components.quasisimple_of_equiv e (CatalogueBAlternating.quasisimple_iff_native.mp hM))
    have hLtop := CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hfix 2 L hL2
    rw [hLtop]
    exact Components.quasisimple_of_equiv Subgroup.topEquiv
      (CatalogueBAlternating.quasisimple_iff_native.mp hfix)
  · exact CatalogueBAlternating.quasisimple_iff_native.mp
      (hfixed alpha hsq h1 2 Nat.prime_two L hL2)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem local_bad_eq_bot_of_coordinate_model {M : Type} [Group M] [Finite M]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (psi : GeneralizedFitting.subgroup G ≃* M)
    (hfixed : ∀ alpha : MulAut M, alpha * alpha = 1 → alpha ≠ 1 → ∀ r : ℕ, r.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
        CFSG.IsPComponent r L → CFSG.IsQuasisimple L)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  have : IsSimpleGroup M := psi.symm.isSimpleGroup
  have hnonabM : ∃ a b : M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨psi a, psi b, fun h => hab (psi.injective (by rw [map_mul, map_mul, h]))⟩
  exact CatalogueRelativeB.local_bad_eq_bot_of_simple_generalizedFitting_model hnonab hindex psi
    (fixed_twoComponents_of_simple_model hnonabM hfixed) hproper S hne htwo

omit [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)] in
theorem exists_coordinate_model (t : Assembly.ComponentType.ClassicalTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ) [Fact p.Prime]
    (hp : p ≠ 2)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G) t n p f) :
    ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (Q : QuadraticForm K (Fin d → K)),
      Nonempty (GeneralizedFitting.subgroup G ≃* matrixProjectiveDerived Q) ∧
      ∀ alpha : MulAut (matrixProjectiveDerived Q), alpha * alpha = 1 → alpha ≠ 1 →
        ∀ r : ℕ, r.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
          CFSG.IsPComponent r L → CFSG.IsQuasisimple L := by
  have hstated := ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel t n p f hmodel
  have hf : f ≠ 0 := by
    rcases ht with rfl | rfl | rfl
    · have := hmodel.1.2.1
      omega
    · have := hmodel.1.2.1
      omega
    · have := hmodel.1.2.1
      omega
  let K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, ⟨θ⟩⟩ := hmodel
    let e := θ.trans (ClassicalModelStatedBridge.omegaModelOddEquiv n K)
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadOdd n K,
      ⟨coordinateOddWitnessEquiv K e⟩,
      odd_orthogonal_involution_fixed_p_components .POmegaOdd (.inl rfl) hp hstated K hK e⟩
  · obtain ⟨-, ⟨θ⟩⟩ := hmodel
    let e := θ.trans (ClassicalModelStatedBridge.omegaModelPlusEquiv n K)
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadPlus n K,
      ⟨coordinatePlusWitnessEquiv K e⟩,
      odd_orthogonal_involution_fixed_p_components .POmegaPlus (.inr (.inl rfl)) hp hstated K
        hK e⟩
  · obtain ⟨hadm, b, c, hbc, ⟨θ⟩⟩ := hmodel
    have hn : 1 ≤ n := by have := hadm.2.2; omega
    let e := θ.trans (ClassicalModelStatedBridge.omegaModelMinusEquiv n b c)
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadMinus n K hn b c,
      ⟨coordinateMinusWitnessEquiv K hn b c e⟩,
      odd_orthogonal_involution_fixed_p_components .POmegaMinus (.inr (.inr rfl)) hp hstated hn
        K hK b c hbc e⟩

theorem odd_orthogonal_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (t : Assembly.ComponentType.ClassicalTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ) [Fact p.Prime]
    (hp : p ≠ 2)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G) t n p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨d, K, _, _, Q, ⟨psi⟩, hfixed⟩ := exists_coordinate_model t ht n p f hp hmodel
  have : Finite (matrixProjectiveDerived Q) := Finite.of_equiv _ psi.toEquiv
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => local_bad_eq_bot_of_coordinate_model hnonab hindex psi hfixed hproper S hne
      htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

omit [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)] in
theorem exists_coordinate_model_of_stated (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ) (hp : p ≠ 2)
    (hmodel : StatedClassicalModel (GeneralizedFitting.subgroup G) t n p f) :
    ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (Q : QuadraticForm K (Fin d → K)),
      Nonempty (GeneralizedFitting.subgroup G ≃* matrixProjectiveDerived Q) ∧
      ∀ alpha : MulAut (matrixProjectiveDerived Q), alpha * alpha = 1 → alpha ≠ 1 →
        ∀ r : ℕ, r.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
          CFSG.IsPComponent r L → CFSG.IsQuasisimple L := by
  have hfix := odd_orthogonal_involution_fixed_p_components t ht hp hmodel
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadOdd n K,
      ⟨coordinateOddWitnessEquiv K e⟩, hfix K hK e⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadPlus n K,
      ⟨coordinatePlusWitnessEquiv K e⟩, hfix K hK e⟩
  · obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hmodel
    have hn : 1 ≤ n := by have := hadm.2.2; omega
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadMinus n K hn b c,
      ⟨coordinateMinusWitnessEquiv K hn b c e⟩, hfix hn K hK b c hbc e⟩

theorem odd_orthogonal_index_two_B_of_stated
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (n p f : ℕ) (hp : p ≠ 2)
    (hmodel : StatedClassicalModel (GeneralizedFitting.subgroup G) t n p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨d, K, _, _, Q, ⟨psi⟩, hfixed⟩ := exists_coordinate_model_of_stated t ht n p f hp hmodel
  have : Finite (matrixProjectiveDerived Q) := Finite.of_equiv _ psi.toEquiv
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => local_bad_eq_bot_of_coordinate_model hnonab hindex psi hfixed hproper S hne
      htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.CatalogueBOrthogonalIndexTwoB
