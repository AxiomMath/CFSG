module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Main
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelNormalizer
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Inv
public import Certificates.Certificate6136
public import Certificates.Certificate6137
public import Certificates.Certificate6138

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Sec1
open CFSG.ComponentClassification

section Construction

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem Sec1.invol_facts (h : Hyp G A) :
    (∀ x y : ↥A ⧸ center ↥A, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
      (∀ x : ↥A ⧸ center ↥A, orderOf x = 2 →
        Nat.card {y : ↥A ⧸ center ↥A // IsConj x y} = 315) := by
  obtain ⟨e⟩ := ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel h.model
  have key : ∀ x : ↥A ⧸ center ↥A, orderOf x = 2 → IsConj Seitz77.L34.r₁S (e x) := fun x hx =>
    Seitz77.L34.isConj_r₁S_of_orderOf_eq_two (by rw [MulEquiv.orderOf_eq]; exact hx)
  have hmap : ∀ {x y : ↥A ⧸ center ↥A}, IsConj (e x) (e y) → IsConj x y := fun {x y} h1 => by
    have := e.symm.toMonoidHom.map_isConj h1
    simpa using this
  refine ⟨fun x y hx hy => hmap ((key x hx).symm.trans (key y hy)), fun x hx => ?_⟩
  have h1 : Nat.card {y : ↥A ⧸ center ↥A // IsConj x y} =
      Nat.card {s : PSL3Four.S // IsConj (e x) s} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun y =>
      ⟨fun hy => e.toMonoidHom.map_isConj hy, fun hy => hmap hy⟩))
  have h2 : Nat.card {s : PSL3Four.S // IsConj (e x) s} =
      Nat.card {s : PSL3Four.S // IsConj Seitz77.L34.r₁S s} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s =>
      ⟨fun hs => (key x hx).trans hs, fun hs => (key x hx).symm.trans hs⟩)
  rw [h1, h2]
  exact Seitz77.L34.card_isConj_r₁_S


theorem Sec1.Cfg.nonempty (d : Datum A) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) : Nonempty (Sec1.Cfg d) := by
  obtain ⟨c, g, hgA, hgS, hgact⟩ := d.exists_chart2_g_cert h hc
  have hP : chPresOK = true := Certificates.certificate6137
  have hQ : chPropsOK = true := Certificates.certificate6138
  obtain ⟨hinv, hcard⟩ := Sec1.invol_facts h
  have hCS := c.centralizer_X_S_le h hP hQ
  have hN := d.normalizer_eq_cert h
  exact ⟨⟨h, hc, c, g, hgA, hgS, hgact, hP, hQ, hCS, hN, hinv, hcard⟩⟩

theorem sec1_false_hyp {d : Datum A} (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) : False := by
  obtain ⟨K⟩ := Sec1.Cfg.nonempty d h hc
  refine K.sec1_core fun k₀ => ?_
  exact Sec1.Cfg.nonempty (d.conj k₀) (h.conj k₀)
    (by rw [d.card_conj_center_two_part k₀]; exact hc)

theorem sec1_false {d : Datum A} (hb : HypBal G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) : False :=
  sec1_false_hyp hb.toHyp hc

end Construction

end CFSG.OddStandard.ChengHeld
