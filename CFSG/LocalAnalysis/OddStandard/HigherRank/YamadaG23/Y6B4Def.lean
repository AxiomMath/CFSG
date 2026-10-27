module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec6S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def y6bE16 (c : Ctx5 G L) : Subgroup G := c.s.fr.F ⊔ zpowers c.g

@[expose] def y6bE (c : Ctx5 G L) : Subgroup G := y6bE16 c ⊔ zpowers c.s.t

@[expose] def y6bX (c : Ctx5 G L) : Subgroup G := normalizer ((y6bE c : Subgroup G) : Set G)

@[expose] def y6bT3 (c : Ctx5 G L) : Subgroup G := c.s.T ⊔ M3 c.s

@[expose] def y6bW (c : Ctx5 G L) : Subgroup G := y6bE c ⊔ M3 c.s

@[expose] def Y6Four4a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx6 G L, c.toCtx5.Facts5 → c.Facts6 →
      ¬ (centralizer ({c.g} : Set G) ⊓
          normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤ c.s.H)

end CFSG.OddStandard.HigherRank.YamadaG23
