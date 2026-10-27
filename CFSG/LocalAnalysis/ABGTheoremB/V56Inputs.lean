module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
public import CFSG.LocalAnalysis.ABGTheoremB.V3Defs

public section

namespace CFSG.ABGTheoremB.V56

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

structure CStructure (σ : Setting G) : Prop where
  C_eq : oddCoreIn σ.C ⊔ (σ.D ⊓ Subgroup.centralizer (σ.T : Set G)) = σ.C
  omega : ∀ g ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G), g ^ 2 = 1 → g ∈ σ.T

structure LemmaV31 (σ : Setting G) (J : Subgroup G) : Prop where
  nonempty : (σ.familyW J).Nonempty
  coprime : ∀ W ∈ σ.familyW J, ¬ σ.p ∣ Nat.card W
  covers : ∀ W ∈ σ.familyW J, ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
    ((W ⊔ σ.D : Subgroup G) : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G)

structure LemmaV33 (σ : Setting G) (J : Subgroup G) : Prop where
  inf_ON : ∀ W ∈ σ.familyW J, W ⊓ σ.ON = ⊥
  permutable : ∀ W ∈ σ.familyW J, ∀ P : Subgroup G, IsSylowOf σ.p P σ.C →
    (P : Set G) * (W : Set G) = (W : Set G) * (P : Set G)
  normalizes_Q : σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J, ∀ d : σ.IV7Data σ.p,
    W ≤ Subgroup.normalizer (d.Q : Set G)

@[expose] def PropR1Input (σ : Setting G) (J : Subgroup G) : Prop :=
  σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J, ∀ P : Subgroup G, IsSylowOf σ.p P σ.C →
    σ.D ≤ Subgroup.normalizer (P : Set G) → ∀ K ∈ σ.familyL σ.p, W ≤ K →
    ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ →
        CFSG.thompsonCenter U ≤ oddCoreIn K ∧
          pPrimeCoreIn σ.p K ⊔ (K ⊓ Subgroup.normalizer (CFSG.thompsonCenter U : Set G)) = K

@[expose] def PropR2Input (σ : Setting G) (J : Subgroup G) : Prop :=
  σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J, ∀ P : Subgroup G, IsSylowOf σ.p P σ.C →
    σ.D ≤ Subgroup.normalizer (P : Set G) → ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
    ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ →
        pPrimeCoreIn σ.p K ⊔ (K ⊓ Subgroup.normalizer (CFSG.thompsonCenter U : Set G)) = K

end CFSG.ABGTheoremB.V56
