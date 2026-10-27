module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveHarada
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Ind
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecRed
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd.NoA8

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction

@[expose] def HSInnerRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HSLemma21Setting G L →
    HSInductionHiS G →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
      centralizer ({t} : Set G) = L ⊔ zpowers t →
        (∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
          (∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
            φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)) ∧
          ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G),
            m * t * m⁻¹ = t * e) → False

@[expose] def HSOuterFiveYStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S : Subgroup G) (z n v s : G),
    HSOuterSetup G L t S z n v s → HSInductionHiS G →
    ∀ r : G, r ∈ L → r * v = v * r → orderOf r = 5 →
      ∀ (htr : t ∈ centralizer ({r} : Set G)) (hvr : v ∈ centralizer ({r} : Set G))
        (htv : t * v ∈ centralizer ({r} : Set G)),
        IsSporadic (HSFiveBar G r) .M12 →
        (∃ h : HSFiveBar G r, h * fiveBar htr * h⁻¹ = fiveBar hvr ∧
          h * fiveBar hvr * h⁻¹ = fiveBar htv) → False

@[expose] def HSOuterFiveCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S : Subgroup G) (z n v s : G),
    HSOuterSetup G L t S z n v s → HSOuterSetup G L t S z n (t * v) s →
      HSInductionHiS G → HSOuterOutcomeFive (OuterSection v) →
      HSOuterOutcomeFive (OuterSection (t * v)) → False

structure HSMinCex (H : Type) [Group H] [Finite H] (A : Subgroup H) : Prop where
  kProper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H
  below : BelowSec HSMainHiSKP H
  oddCore : CFSG.oddCore H = ⊥
  standard : standardComponentIsStandard A
  sporadic : IsSporadic ↥A .HS
  rank : Open.pRank 2 (centralizer (A : Set H)) = 1
  balanced : ∀ t : H, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set H)) = ⊥
  notOutcome : ¬ ∃ K₁ K₂ : Subgroup H, K₁.IsSubnormal ∧ K₂.IsSubnormal ∧
    IsSporadic (K₁ ⧸ center K₁) .HS ∧ IsSporadic (K₂ ⧸ center K₂) .HS ∧
    A ≤ K₁ ⊔ K₂ ∧ (K₁ ⊔ K₂).Normal

@[expose] def HSMinCexProp13 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (A : Subgroup H), HSMinCex H A →
    center H = ⊥ ∧ IsSimpleGroup ↥(commutator H) ∧ (commutator H).index ≤ 2

@[expose] def HSMinCexLemma21 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (A : Subgroup H), HSMinCex H A →
    ∀ S : Sylow 2 (centralizer (A : Set H)), Nat.card S = 2

end CFSG.EvenSporadicStandard.HSStd.NoA8

