module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenThirteenSp62 : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsTwoPrimeComponent I₀ I₀ → H ⊓ L ≤ normalizer (I₀ : Set G) →
    ∀ (q : TauCeti.PrimePower) (dK dJ : TauCeti.ValidLieTypeIndex), q.p = 2 →
    q.exponent = 1 → dK.1 = .B 3 q → dJ.1 = .twistedA 3 q → Nonempty (K ≃* CatGroup dK) →
    ∀ f : I₀ →* CatGroup dJ, Function.Surjective f →
      (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker → False

@[expose] def AGL81TenThirteenSp48 : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    3 ∈ rankThreeSigmaA G → AGL81CfgData 3 P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsTwoPrimeComponent I₀ I₀ →
    ∀ (q : TauCeti.PrimePower) (dK dJ : TauCeti.ValidLieTypeIndex), q.p = 2 →
    q.exponent = 3 → dK.1 = .B 2 q → dJ.1 = .A 1 q → Nonempty (K ≃* CatGroup dK) →
    ∀ f : I₀ →* CatGroup dJ, Function.Surjective f →
      (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker → False

@[expose] def AGL81TenThirteenA10 : Prop :=
  Setting G → ∀ (P : Sylow 5 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 5)),
    AGL81CfgData 5 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsTwoPrimeComponent I₀ I₀ →
    Nonempty (K ≃* (TauCeti.CFSGIndex.alternating 10 (by norm_num)).Group) →
    ∀ f : I₀ →* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group, Function.Surjective f →
      (d1PlusCore 5 H K).subgroupOf I₀ ≤ f.ker → False

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
