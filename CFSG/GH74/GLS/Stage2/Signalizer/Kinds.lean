module

public import CFSG.GH74.GLS.Stage2.Local.Concl
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem Stage2Ctx.typeOneCase_of_kind {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (h : Stage2Ctx G z k S)
    (hk : k = Kind.g2 ∨ k = Kind.m12 ∨ k = Kind.mcl ∨ k = Kind.ly) : TypeOneCase G k := by
  have hd := h.data
  rcases hk with rfl | rfl | rfl | rfl
  · cases hd with
    | g2 hg => exact Or.inl hg.one_class
  · exact Or.inr rfl
  · cases hd with
    | mcl hm => obtain ⟨n, -, hs⟩ := hm; exact Or.inl hs.one_class
  · cases hd with
    | ly hm => obtain ⟨n, -, hs⟩ := hm; exact Or.inl hs.one_class

theorem Stage2Ctx.isClassicalKind_of_not_typeOneCase {G : Type} [Group G] [Finite G] {z : G}
    {k : Kind} {S : Subgroup G} (h : Stage2Ctx G z k S) (hn : ¬ TypeOneCase G k) :
    IsClassicalKind k := by
  have hd := h.data
  cases hd with
  | g2 hg => exact absurd (Or.inl hg.one_class) hn
  | m12 _ => exact absurd (Or.inr rfl) hn
  | psp4 _ => exact Or.inl rfl
  | l4 ε _ => exact Or.inr ⟨ε, rfl⟩
  | mcl hm => obtain ⟨n, -, hs⟩ := hm; exact absurd (Or.inl hs.one_class) hn
  | ly hm => obtain ⟨n, -, hs⟩ := hm; exact absurd (Or.inl hs.one_class) hn

end CFSG.GH74.GLS.Stage2.Signalizer
