module

public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.R2

open Subgroup

theorem card_centralizer_conj {G : Type} [Group G] (c t : G) :
    Nat.card (centralizer ({c * t * c⁻¹} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
  have h := card_centralizer_mulEquiv (MulAut.conj c) t
  rwa [MulAut.conj_apply] at h

end CFSG.LocalAnalysis.EvenBN.Tits.R2
