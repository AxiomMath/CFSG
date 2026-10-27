module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Solomon74SpinSevenAsUsed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) → z ∈ L →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L) →
    5 ≤ p ^ f → (L.subgroupOf (centralizer {z})).Characteristic →
    centralizer {z} ⊓ coreActionKernel L =
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ zpowers z →
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L →
    (∀ x ∈ centralizer ({z} : Set G), (∃ g : G, g * z * g⁻¹ = x) ↔ (x ∈ L ∧ orderOf x = 2)) →
    ∀ S : Sylow 2 G, ¬ (S : Subgroup G) ≤ L

end CFSG.ComponentClassification.HarrisLit.T1
