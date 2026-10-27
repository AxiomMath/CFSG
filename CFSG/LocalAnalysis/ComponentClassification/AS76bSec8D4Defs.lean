module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Open.QuasithinDefs
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

variable (K : Type) [Field K] (σ : K ≃+* K)

abbrev d4C
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedRootGroup TwistTag.D4 K σ.toRingHom

abbrev d4k : Subfield K :=
  trialityFixedField K σ.toRingHom

@[expose] noncomputable def d4x₁
    (c : K) : ModGL TwistTag.D4.tag K :=
  (trialityOrbitProd K σ.toRingHom (trialityRoot 0) c : ModGL TwistTag.D4.tag K)

@[expose] noncomputable def d4x₂
    (c : K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K (trialityRoot 1) c

@[expose] noncomputable def d4x₃
    (c : K) : ModGL TwistTag.D4.tag K :=
  (trialityOrbitProd K σ.toRingHom (trialityRoot 2) c : ModGL TwistTag.D4.tag K)

@[expose] noncomputable def d4x₄
    (c : K) : ModGL TwistTag.D4.tag K :=
  (trialityOrbitProd K σ.toRingHom (trialityRoot 3) c : ModGL TwistTag.D4.tag K)

@[expose] noncomputable def d4x₅
    (c : K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K (trialityRoot 4) c

@[expose] noncomputable def d4x₆
    (c : K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K (trialityRoot 5) c

@[expose] noncomputable def d4y₁
    (c : K) : ModGL TwistTag.D4.tag K :=
  (trialityOrbitProd K σ.toRingHom (-trialityRoot 0) c : ModGL TwistTag.D4.tag K)

@[expose] noncomputable def d4y₂
    (c : K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K (-trialityRoot 1) c

@[expose] noncomputable def d4y₃
    (c : K) : ModGL TwistTag.D4.tag K :=
  (trialityOrbitProd K σ.toRingHom (-trialityRoot 2) c : ModGL TwistTag.D4.tag K)

@[expose] noncomputable def d4y₄
    (c : K) : ModGL TwistTag.D4.tag K :=
  (trialityOrbitProd K σ.toRingHom (-trialityRoot 3) c : ModGL TwistTag.D4.tag K)

@[expose] noncomputable def d4y₅
    (c : K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K (-trialityRoot 4) c

@[expose] noncomputable def d4y₆
    (c : K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K (-trialityRoot 5) c

@[expose] noncomputable def d4z
    : ModGL TwistTag.D4.tag K :=
  d4x₆ K 1

@[expose] noncomputable def d4t
    : ModGL TwistTag.D4.tag K :=
  d4x₄ K σ 1

@[expose] noncomputable def d4Zz
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  closure (Set.range fun c : d4k K σ => d4x₆ K c)

@[expose] noncomputable def d4Zt
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  closure (Set.range fun c : d4k K σ => d4x₄ K σ c)

abbrev d4Vr
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩

abbrev d4Mr
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  orbitRankOneGroup TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩

abbrev d4Ma
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  orbitRankOneGroup TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩

@[expose] noncomputable def d4U0t
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ ⊓ centralizer {d4t K σ}

abbrev d4H
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedRootTorus TwistTag.D4 K σ.toRingHom

@[expose] noncomputable def d4W0
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  closure (trialityOuterTorus K σ '' {a : Kˣ | (a : K) * σ a * σ (σ a) = 1})

@[expose] noncomputable def d4Qt
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  ((trialityTorusHom σ).comp (MonoidHom.inr Kˣ (trialityFixedField K σ.toRingHom)ˣ)).range

@[expose] noncomputable def d4Lz
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  closure (Set.range (fun c : d4k K σ => d4x₂ K c) ∪ Set.range (fun c : d4k K σ => d4y₂ K c) ∪
    Set.range (fun c : d4k K σ => d4x₅ K c) ∪ Set.range (fun c : d4k K σ => d4y₅ K c) ∪
    Set.range (fun c : d4k K σ => d4x₆ K c) ∪ Set.range (fun c : d4k K σ => d4y₆ K c))

@[expose] noncomputable def d4Lt
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  closure (Set.range (d4x₄ K σ) ∪ Set.range (d4y₄ K σ))

@[expose] noncomputable def d4D0z
    : Subgroup (ModGL TwistTag.D4.tag K) :=
  closure (Set.range (fun c : d4k K σ => d4x₆ K c) ∪ Set.range (fun c : d4k K σ => d4y₆ K c))

@[expose] def D4ClassFacts : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ m) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ m) → ∀ z t : ↥(d4C K σ),
      (z : ModGL TwistTag.D4.tag K) = d4z K → (t : ModGL TwistTag.D4.tag K) = d4t K σ →
        Exc.ClassesCover [z, t] ∧ (∃ Z, Exc.ClassData (2 ^ m) z Z ∧ Exc.ResidualMem z) ∧
          (∃ Z, Exc.ClassData (2 ^ m) t Z ∧ Exc.ResidualMem t)

@[expose] def D4LeviFacts : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ m) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ m) → ∀ z t : ↥(d4C K σ),
      (z : ModGL TwistTag.D4.tag K) = d4z K → (t : ModGL TwistTag.D4.tag K) = d4t K σ →
        (∃ Z Dl Q H L : Subgroup ↥(d4C K σ), Exc.CentreData z Z ∧ Exc.LeviData Z Dl Q H L ∧
          Exc.AutFix Q L ∧ Exc.D0Data z Z ∧ StatedClassicalModel (rankTwoQuot L) .PSL 3 2 m ∧
          (m = 2 → ∃ y ∈ centralizer (Q : Set ↥(d4C K σ)), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
            ¬ InducesInner y L)) ∧
        (∃ Z Dl Q H L : Subgroup ↥(d4C K σ), Exc.CentreData t Z ∧ Exc.LeviData Z Dl Q H L ∧
          Exc.AutFix Q L ∧ Exc.D0Data t Z ∧
          StatedClassicalModel (rankTwoQuot L) .PSL 2 2 (3 * m) ∧
          (m = 2 → ¬ StatedClassicalModel (rankTwoQuot L) .PSL 3 2 2))

end CFSG.ComponentClassification.RankTwoExceptional.D4
