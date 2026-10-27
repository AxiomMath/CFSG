module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

@[expose] def L6_2Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      ∀ J ∈ Ω, J ∉ twinSet Ω K → ∀ t : G, IsUniqueInvolution J t →
        ∀ V : Subgroup G, IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) → t ∈ V →
          (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
          (V = Subgroup.zpowers t ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
            ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
              IsSemidihedral (R ⊔ V)) ∨
          (V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
            ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
              IsWreathed (R ⊔ V)) ∨
          (V ∈ RSet Ω ∧ ⁅V, K⁆ ≤ oddCoreOf K)

@[expose] def L6_4ThreeGenAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    ∀ K ∈ Ω, ∀ J ∈ Ω, InA Ω K J → ∀ z j : G, IsUniqueInvolution K z → IsUniqueInvolution J j →
      ∀ X Y : Subgroup G,
        X = (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) →
        Y = pairNormalizers K J z j →
      ∀ u v : G, Subgroup.zpowers u ∈ USet Ω → Subgroup.zpowers u ≤ K →
        Subgroup.zpowers v ∈ USet Ω → Subgroup.zpowers v ≤ J →
        Commutes (Subgroup.zpowers u) (Subgroup.zpowers v) →
      ∀ R T : Subgroup G, IsSylow2In R K → IsSylow2In T J →
        Subgroup.zpowers u ≤ R → Subgroup.zpowers v ≤ T →
        R ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) →
        T ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) →
          (X = oddCoreOf X ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧ R ⊔ T ≤ Y) ∧
          (X ≤ Y ∧ Y ≤ Subgroup.normalizer (X : Set G) ∧
            Y ≤ Subgroup.normalizer ((Subgroup.closure {z, j} : Subgroup G) : Set G) ∧
            ∃ φ : ↥Y →* DihedralGroup 6, Function.Surjective φ ∧ φ.ker = X.subgroupOf Y) ∧
          (∃ Kstar : Subgroup G, Kstar ≠ K ∧ twinSet Ω K = {K, Kstar} ∧
            (∃ y ∈ Y, conjSub y J = Kstar) ∧ v * v ∈ K ⊔ Kstar ∧
            (∃ Rstar : Subgroup G, IsSylow2In Rstar Kstar ∧
              Rstar ≤ Subgroup.normalizer
                ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) ∧
            ∀ Rstar : Subgroup G, IsSylow2In Rstar Kstar →
              Rstar ≤ Subgroup.normalizer
                ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) →
                Rstar ≤ Y ∧
                (∃ ustar : G,
                  Subgroup.zpowers ustar = Rstar ⊓ Subgroup.centralizer ({j} : Set G) ∧
                  Subgroup.zpowers ustar ∈ USet Ω ∧
                  Subgroup.zpowers u ⊔ Subgroup.zpowers v =
                    Subgroup.zpowers ustar ⊔ Subgroup.zpowers v) ∧
                ∀ r ∈ R, r ∉ Subgroup.zpowers u → ∀ rstar ∈ Rstar,
                  rstar ∉ Subgroup.centralizer ({j} : Set G) →
                    (∀ x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v,
                      (r * rstar) * x * (r * rstar)⁻¹ = x⁻¹) ∧
                    Y ⊓ Subgroup.centralizer ((Subgroup.closure {z, j} : Subgroup G) : Set G) =
                      X ⊔ Subgroup.zpowers (r * rstar)) ∧
          ((∀ r ∈ R, r ∉ Subgroup.zpowers u → r * j * r⁻¹ = z * j) ∧
            (∀ t ∈ T, t ∉ Subgroup.zpowers v → t * z * t⁻¹ = z * j) ∧
            IsSylow2In (Subgroup.zpowers v) (J ⊓ Subgroup.centralizer ({z} : Set G))) ∧
          (Y ⊓ Subgroup.centralizer
              ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) ≤ X ∧
            ∀ W : Subgroup G, IsPGroup 2 W → Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ W →
              W ≤ Subgroup.centralizer
                ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) →
                Y ⊓ W = Subgroup.zpowers u ⊔ Subgroup.zpowers v)

@[expose] def L6_10Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
      (∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → ∀ r ∈ R, ∀ V ∈ η, conjSub r V ∈ η) ∧
      (∀ U ∈ USet Ω, U ≤ (S : Subgroup G) → ∀ u ∈ U, ∀ V ∈ η, conjSub u V ∈ η)

@[expose] def L6_11Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
      ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
