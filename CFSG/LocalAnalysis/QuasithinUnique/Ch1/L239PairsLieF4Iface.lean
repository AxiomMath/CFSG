module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Cov
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Core

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin
open scoped commutatorElement

@[expose] def LargeReeCenterGen :
    Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime],
    1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
      (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) ≤
        ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
          F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩⁆ ∧
      F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ≤
        ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩,
          perfectCore (F4.reeLocalParabolic K a ⟨0, by decide⟩)⁆) ∧
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊓
        Subgroup.centralizer
          (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) ≤
        ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩,
          F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩⁆ ∧
      F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤
        ⁅F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩,
          perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩)⁆)

theorem largeReeParabolicFacts_of
    (H : LargeReeCenterGen) : LargeReeParabolicFacts := by
  intro a K _ _ _ ha hK
  obtain ⟨⟨hC₀, hG₀⟩, ⟨hC₁, hG₁⟩⟩ := H a K ha hK
  exact ⟨parabolicFacts_zero_of ha hK hC₀ hG₀, parabolicFacts_one_of ha hK hC₁ hG₁⟩

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

