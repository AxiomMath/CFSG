module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFusion33

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure B5Std (c : Ctx7 G L) : Prop where
  hH : F33Hyp c.s c.e
  h5 : c.toCtx5.Facts5
  h71 : c.Fact71
  h72 : c.Fact72
  h73 : c.Fact73
  h74 : c.Fact74

structure B6Std (c : Ctx7 G L) : Prop extends B5Std c where
  h75 : c.Fact75

theorem B5Std.fact54 {c : Ctx7 G L} (hb : B5Std c) : c.toCtx5.Fact54 := hb.h5.2.2.1

theorem B5Std.fact55 {c : Ctx7 G L} (hb : B5Std c) : c.toCtx5.Fact55 := hb.h5.2.2.2.1

theorem B5Std.fact57 {c : Ctx7 G L} (hb : B5Std c) : c.toCtx5.Fact57 := hb.h5.2.2.2.2.2

theorem B5Std.fact33 {c : Ctx7 G L} (hb : B5Std c) : c.e.Fact33 := fact33_of hb.hH

@[expose] def R5 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := s.R ⊔ M5 e

@[expose] def X76 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G :=
  normalizer (R5 e : Set G) ⊓ normalizer (M5 e : Set G) ⊓ normalizer (V1 e : Set G) ⊓
    normalizer (V2 e : Set G)

@[expose] def AM5 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := s.fr.A ⊔ M5 e

@[expose] def BM5 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := s.fr.B ⊔ M5 e

@[expose] def SM5 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := s.fr.S ⊔ M5 e

@[expose] def EFV2 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G :=
  s.fr.E ⊔ s.fr.F ⊔ V2 e

@[expose] def U76 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G :=
  X76 e ⊓ centralizerSection (M5 e) (V1 e)

end CFSG.OddStandard.HigherRank.YamadaG23
