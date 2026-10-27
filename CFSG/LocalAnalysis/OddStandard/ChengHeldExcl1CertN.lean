module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Cert
public import Certificates.Certificate6140

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.excl_field_cert
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hk : c.kinds = {Kind.field}) : False :=
  c.excl_field Certificates.certificate6140 hα h hc hk

end CFSG.OddStandard.ChengHeld
