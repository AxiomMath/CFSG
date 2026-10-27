module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Rank
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Fus
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Pi

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

theorem Chart4.excl_both_zero_hyp
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}
    (h : Hyp G A) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (c : Chart4 d 0) {g : G} (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S)
    (hact : GAct 0 c.t c.pi c.tau c.mu c.lam c.ze c.xi g) (hk : c.kinds = Set.univ) : False := by
  let K : Excl2.Cfg d 0 :=
    { h := h, hα := by norm_num, hc := hc, c := c, hP := Certificates.certificate6137,
      hQ := Certificates.certificate6138, hS2 := Certificates.certificate6139,
      hN := d.normalizer_eq_cert h, g := g, g_norm := hg, g_act := hact, kin := hk }
  have hqπ := K.isConj_q_pi_zero
  have hQt := K.Q_le_zpowers_t hqπ
  obtain ⟨n, hnN, -, hord, z, hzP, hzW, hz2, hnz⟩ := K.exists_fixed_involution hqπ hQt
  obtain ⟨f, hfz⟩ := K.exists_hom hQt hzP hzW hz2
  have hzq := K.isConj_q_z hqπ hQt f hzP hzW hz2 hfz
  exact K.false_of_isConj_q_z hQt hnN hord hzP.2 hzW hnz hzq

theorem Chart4.excl_both_zero
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}
    (hb : HypBal G A) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (c : Chart4 d 0) {g : G} (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S)
    (hact : GAct 0 c.t c.pi c.tau c.mu c.lam c.ze c.xi g) (hk : c.kinds = Set.univ) : False :=
  Chart4.excl_both_zero_hyp hb.toHyp hc c hg hact hk

end CFSG.OddStandard.ChengHeld
