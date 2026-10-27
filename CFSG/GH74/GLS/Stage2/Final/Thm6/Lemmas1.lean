module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs2

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def Lemma20_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z

@[expose] def Lemma20_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    (k = Kind.g2 ∨ k = Kind.mcl ∨ k = Kind.ly) → False

section Proved

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}

theorem Fail20.typeCl (h8 : Lemma20_8) (h : Fail20 G z k S M) (hMC : M = Cen z) : TypeCl z k S := by
  have hd := h.ctx.ctx17.ctx.data
  cases hd with
  | g2 _ => exact (h8 G z _ S M h hMC (Or.inl rfl)).elim
  | m12 _ => exact (h.notM12 rfl).elim
  | psp4 h' => obtain ⟨q, L₁, L₂, hq⟩ := h'; exact Or.inr ⟨q, rfl, L₁, L₂, hq⟩
  | l4 ε h' => obtain ⟨q, L₁, L₂, hq⟩ := h'; exact Or.inl ⟨ε, q, rfl, L₁, L₂, hq⟩
  | mcl _ => exact (h8 G z _ S M h hMC (Or.inr (Or.inl rfl))).elim
  | ly _ => exact (h8 G z _ S M h hMC (Or.inr (Or.inr rfl))).elim

end Proved

end CFSG.GH74.GLS.Stage2.Final.Thm6
