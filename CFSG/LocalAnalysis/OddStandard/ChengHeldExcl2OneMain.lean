module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2One
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Pi

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

theorem Chart4.excl_both_one_hyp
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}
    (h : Hyp G A) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (c : Chart4 d 1) {g : G} (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S)
    (hact : GAct 1 c.t c.pi c.tau c.mu c.lam c.ze c.xi g) (hk : c.kinds = Set.univ) : False := by
  let K : Excl2.Cfg d 1 :=
    { h := h, hα := le_rfl, hc := hc, c := c, hP := Certificates.certificate6137,
      hQ := Certificates.certificate6138, hS2 := Certificates.certificate6139,
      hN := d.normalizer_eq_cert h, g := g, g_norm := hg, g_act := hact, kin := hk }
  have hnc : ¬ IsConj d.q K.c.pi := K.not_isConj_q_pi_one rfl
  obtain ⟨k, y, x, hrep, hxQ, hzq, hz2⟩ := K.exists_pure_involution hnc
  obtain ⟨hyX, hyQS, hact⟩ := K.c.rep_mem k y hrep
  have hzX : y * x ∈ d.X := d.X.mul_mem hyX (d.Q_le_X hxQ)
  have hzQS : y * x ∉ d.QS := fun h => hyQS (by
    have := mul_mem h (d.QS.inv_mem (mem_sup_left hxQ))
    simpa using this)
  have hact' := K.act_mul_Q hyX hxQ hact
  cases k
  · exact hnc (K.isConj_q_pi_of_field_one rfl hzX hzQS hz2 hzq hact')
  · exact hnc (K.isConj_q_pi_of_graph_one rfl hzQS hzq hact')
  · exact hnc (K.isConj_q_pi_of_unitary hzX hzQS hz2 hzq hact')

theorem Chart4.excl_both_one
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}
    (hb : HypBal G A) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (c : Chart4 d 1) {g : G} (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S)
    (hact : GAct 1 c.t c.pi c.tau c.mu c.lam c.ze c.xi g) (hk : c.kinds = Set.univ) : False :=
  Chart4.excl_both_one_hyp hb.toHyp hc c hg hact hk

end CFSG.OddStandard.ChengHeld
