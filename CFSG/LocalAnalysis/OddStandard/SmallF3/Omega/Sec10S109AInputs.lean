module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Step109AOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → ∀ g : G, g ∈ normalizer (S : Set G) → g ∉ secM t S L →
      IsPGroup 2 ↥(zpowers g) → g⁻¹ * t * g = t * z → g⁻¹ * z * g = z →
        ∃ s ∈ S, IsOuterOn (g * s) (K1 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z)) ∧
          (∀ k ∈ K2, (g * s) * k * (g * s)⁻¹ * k⁻¹ ∈ oddCoreIn (secK0 t z)) ∧
          ∀ k ∈ secK0 t z, (g * s) * (g * s) * k = k * ((g * s) * (g * s))

end CFSG.OddStandard.SmallF3.Omega
