module

public import CFSG.GH74.SectionalRank

public section

universe u

namespace CFSG.GH74.QTGen4

class Finite4 (G : Type u) [Group G] : Prop where
  finite : Finite G
  gen4 : Gen4 G

attribute [instance 100] Finite4.finite

instance instFinite4Subgroup (G : Type u) [Group G] [Finite4 G] (H : Subgroup G) : Finite4 H where
  finite := inferInstance
  gen4 := Gen4.subgroup H Finite4.gen4

instance instFinite4Quotient (G : Type u) [Group G] [Finite4 G] (N : Subgroup G) [N.Normal] :
    Finite4 (G ⧸ N) where
  finite := inferInstance
  gen4 := Gen4.quotient N Finite4.gen4

theorem finite4_of_gen4 {G : Type u} [Group G] [Finite G] (h : Gen4 G) : Finite4 G :=
  ⟨inferInstance, h⟩

theorem Finite4.of_mulEquiv {G H : Type u} [Group G] [Group H] [Finite4 G] (e : G ≃* H) :
    Finite4 H :=
  ⟨Finite.of_equiv G e.toEquiv, Gen4.of_mulEquiv e Finite4.gen4⟩

end CFSG.GH74.QTGen4
