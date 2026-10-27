module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalIndexTwoB

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_symplectic_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (n p f : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hn : 2 ≤ n)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G) .PSp n p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨⟨-, hf, -, -⟩, ⟨θ⟩⟩ := hmodel
  let psi : GeneralizedFitting.subgroup G ≃* StatedProj (StatedSp n (GaloisField p f)) :=
    θ.trans (ClassicalModelStatedBridge.pspModelEquiv n p f)
  have : Finite (StatedProj (StatedSp n (GaloisField p f))) := Finite.of_equiv _ psi.toEquiv
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex psi (fun alpha h2 h1 => odd_symplectic_involution_fixed_p_components p f Fact.out hp
        hf (GaloisField p f) hcard n hn alpha h2 h1) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.CatalogueBSymplecticB
