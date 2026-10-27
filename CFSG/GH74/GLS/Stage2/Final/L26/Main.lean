module

public import CFSG.GH74.GLS.Stage2.Final.L26.Sporadic
public import CFSG.GH74.GLS.Stage2.Final.L26.Pair
public import CFSG.GH74.GLS.Stage2.Local.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def Lemma26K (k : Kind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z k S → Lemma26 z S

theorem lemma26K_psp4 : Lemma26K Kind.psp4 := by
  intro G _ _ z S hctx
  have hd := hctx.data
  cases hd with
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact lemma26_of_pair hctx h.pair

theorem lemma26K_l4 (ε : Bool) : Lemma26K (Kind.l4 ε) := by
  intro G _ _ z S hctx
  have hd := hctx.data
  cases hd with
  | l4 _ h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact lemma26_of_pair hctx h.pair

theorem lemma26K_mcl : Lemma26K Kind.mcl := by
  intro G _ _ z S hctx
  have hd := hctx.data
  cases hd with
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact lemma26_of_sporadic hctx h

theorem lemma26K_ly : Lemma26K Kind.ly := by
  intro G _ _ z S hctx
  have hd := hctx.data
  cases hd with
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact lemma26_of_sporadic hctx h

theorem leaf_lemma26_of_g2_m12 (hg2 : Lemma26K Kind.g2) (hm12 : Lemma26K Kind.m12) : Leaf_Lemma26 := by
  intro G _ _ z k S hctx
  cases k with
  | g2 => exact hg2 G z S hctx
  | m12 => exact hm12 G z S hctx
  | psp4 => exact lemma26K_psp4 G z S hctx
  | l4 ε => exact lemma26K_l4 ε G z S hctx
  | mcl => exact lemma26K_mcl G z S hctx
  | ly => exact lemma26K_ly G z S hctx

end CFSG.GH74.GLS.Stage2.Final.L26
