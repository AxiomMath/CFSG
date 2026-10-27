module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Graph
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Field
public import Certificates.Certificate6137
public import Certificates.Certificate6138
public import Certificates.Certificate6139

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.excl_QS
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = ∅) : False :=
  c.excl_QS_core hα h Certificates.certificate6137 Certificates.certificate6138
    Certificates.certificate6139 hc hg hact hk

theorem Chart4.excl_graph
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = {Kind.graph}) : False :=
  c.excl_graph_core hα h Certificates.certificate6137 Certificates.certificate6138
    Certificates.certificate6139 hc hg hact hk

theorem Chart4.excl_field
    (hE : chExcl1OK = true) (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hk : c.kinds = {Kind.field}) : False :=
  c.excl_field_core hα h Certificates.certificate6137 Certificates.certificate6138
    Certificates.certificate6139 hE hc hk

end CFSG.OddStandard.ChengHeld
