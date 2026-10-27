module

public import CFSG.GH74.GLS.Basic
public import CFSG.GH74.NoComponent

public section

namespace CFSG.GH74.GLS

theorem isKProperSimple_of_kgh {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (h : KGH G) : IsKProperSimple G :=
  ⟨hs, hn, kProper_of_kgh h⟩

theorem isKGroupNative_of_kgh {G : Type} [Group G] [Finite G] (h : KGH G) {H : Subgroup G}
    (hH : H ≠ ⊤) : IsKGroupNative H :=
  isKGroupNative_of_kProper (kProper_of_kgh h) hH

end CFSG.GH74.GLS
