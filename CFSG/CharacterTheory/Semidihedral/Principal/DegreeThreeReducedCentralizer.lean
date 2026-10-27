module

public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeThreeReducedCentralizerSupport

public noncomputable section

namespace CFSG.Semidihedral.Principal.DegreeThreeReducedCentralizer

open CFSG.Assembly.LowTwoRank
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Wreathed.DegreeThreeModelFullCenter

theorem degree_three_model_reduced_centralizer_local_parameter (G : Type) [Group G]
    (tau : StatedLieTag) (htau : tau = .PSL ∨ tau = .PSU) (p f : ℕ) (hp : p.Prime)
    (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f) (hmodel : StatedClassicalModel G tau 3 p f)
    (hcong : (tau = .PSL → p ^ f % 4 = 3) ∧ (tau = .PSU → p ^ f % 4 = 1))
    (t : G) (ht : orderOf t = 2) :
    let L := CFSG.generalizedFitting (Gamma t)
    IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      Subgroup.centralizer (L : Set (Gamma t)) = ⊥ ∧ L.index = 2 ∧
      StatedClassicalModel L .PSL 2 p f ∧ Nat.card L = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∀ (r a : ℕ), r.Prime → Odd r → 1 ≤ a → StatedClassicalModel L .PSL 2 r a →
        r ^ a = p ^ f ∧ r = p ∧ a = f := by
  let : Finite G := originalDegreeThreeModel_finite G p f tau htau hmodel
  have hZ := stated_reduced_center_card_dvd_two G tau htau p f hp hpodd hq hmodel hcong t ht
  have hW := (degree_three_model_full_center_local_quotient_parameter G p f hp hpodd hf tau
    htau hmodel t ht).2 hq
  exact full_large_conclusions_of_equiv (reducedFullCenterEquivGamma t ht hZ) p f hp hpodd hf hq
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩

end CFSG.Semidihedral.Principal.DegreeThreeReducedCentralizer
