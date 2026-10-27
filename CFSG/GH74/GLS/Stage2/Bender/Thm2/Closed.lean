module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def IG_5_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ (N P : Subgroup G), IsPGroup p ↥P → P ≤ N →
    (Fs N = Op p N → Fs (N ⊓ normalizer (P : Set G)) = Op p (N ⊓ normalizer (P : Set G))) ∧
    (Fs (N ⊓ normalizer (P : Set G)) = Op p (N ⊓ normalizer (P : Set G)) ↔
      Fs (N ⊓ centralizer (P : Set G)) = Op p (N ⊓ centralizer (P : Set G)))

@[expose] def KInfty_facts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ P : Subgroup G, IsPGroup p ↥P →
    kInfty P ≤ P ∧ zOf P ≤ kInfty P

end CFSG.GH74.GLS.Stage2.Bender.Thm2
