module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Config

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

structure JankoConfiguration (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) :
    Prop where
  abelian : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a
  exponent_two : ∀ a ∈ (S : Subgroup G), a * a = 1
  card : Nat.card (S : Subgroup G) = 8
  transitive : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a ≠ 1 → b ≠ 1 →
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * a * n = b
  quotient : ∃ J : Subgroup (EscapingQuotient z), J.Normal ∧
    Nonempty (J ≃* alternatingGroup (Fin 5)) ∧ escapingBar z ∉ J ∧
      J ⊔ Subgroup.zpowers (escapingBar z) = ⊤
  generated : properTwoGenCoreGamma (S : Subgroup G) 2 ⊔
    Subgroup.centralizer ({z} : Set G) = ⊤

@[expose] def CaseIUnitaryOuterExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ H →
      ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → escapingBar z ∉ J →
        (∃ n : ℕ, Nonempty (↥J ≃* ↥(CFSG.Theory.Comparator.PSU3Model n))) →
        ¬ escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
          False

@[expose] def CaseILinear : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ H →
      ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → escapingBar z ∉ J →
        ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥J ≃* CFSG.Theory.Comparator.PSL2Model n)

@[expose] def CaseIJankoConfiguration : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ H →
      (∃ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J ∧ escapingBar z ∉ J) →
        JankoConfiguration G S z

@[expose] def CentralOddCoreTrivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ H → JankoConfiguration G S z →
        pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) = ⊥

@[expose] def JankoConfigurationJanko : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G),
    IsSimpleGroup G → IsCentralInvolution (S : Subgroup G) z → JankoConfiguration G S z →
      pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) = ⊥ →
        Nonempty (CFSG.Walter.J1Props.JankoHyp₀ G)

end CFSG.ProperTwoGeneratedCore.Lemma37
