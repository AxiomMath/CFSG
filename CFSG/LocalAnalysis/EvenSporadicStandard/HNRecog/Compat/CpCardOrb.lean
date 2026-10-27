module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.CentOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3 CFSG.Monster.GMS

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem cp_card_orb2A (h : F5Std a z) : Nat.card ↥(orb2A a a) = 2200 := by
  haveI : Finite G := h.finite
  have hpart : IsConjOrbit (Gx a) (orb2A a a) := by
    simpa [tab5Set] using h.loc.tableV.self.partition.orbit 0
  obtain ⟨c, hc⟩ := hpart.nonempty
  have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 80640 := by
    simpa [tab5Set] using h.loc.tableV.self.card_stab 0 c (by simpa [tab5Set] using hc)
  have hos := IsConjOrbit.card_mul_card_stab hpart hc
  rw [hstab, card_Gx_a h] at hos
  omega

theorem cp_card_conjVert_eq (h : F5Std a z) (h' : F5Std a' z') :
    Nat.card (ConjVert a) = Nat.card (ConjVert a') := by
  haveI : Finite G := h.finite
  haveI : Finite G' := h'.finite
  have h1 := card_isConj_mul_card_centralizer (G := G) a
  have h2 := card_isConj_mul_card_centralizer (G := G') a'
  rw [card_Gx_a h] at h1
  rw [card_Gx_a h'] at h2
  have hcard : Nat.card G = Nat.card G' := by
    rw [h.loc.order.card_eq, h'.loc.order.card_eq]
  rw [hcard] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h1.trans h2.symm)

private def orb2A_conjEquiv (a g : G) :
    ↥(orb2A a a) ≃ ↥(orb2A a (g * a * g⁻¹)) where
  toFun b := ⟨g * b.1 * g⁻¹, isConj_conj b.2.1 g, by
    have h : (g * a * g⁻¹) * (g * b.1 * g⁻¹) = g * (a * b.1) * g⁻¹ := by group
    rw [h]
    exact isConj_conj b.2.2 g⟩
  invFun c := ⟨g⁻¹ * c.1 * g, by simpa using isConj_conj c.2.1 g⁻¹, by
    have h : a * (g⁻¹ * c.1 * g) = g⁻¹ * ((g * a * g⁻¹) * c.1) * g := by group
    rw [h]
    simpa using isConj_conj c.2.2 g⁻¹⟩
  left_inv b := by
    apply Subtype.ext
    group
  right_inv c := by
    apply Subtype.ext
    group

private def orb2A_adjEquiv (h : F5Std a z) (v : ConjVert a) :
    {u : ConjVert a // (Gamma a).Adj v u} ≃ ↥(orb2A a (v : G)) where
  toFun u := ⟨(u.1 : G), u.1.2, (gamma_adj_iff.mp u.2).2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, by
    rw [gamma_adj_iff]
    refine ⟨?_, b.2.2⟩
    intro hveq
    have hb : b.1 = (v : G) := by
      have := congrArg (fun x : ConjVert a => (x : G)) hveq
      simpa using this.symm
    have hvv : (v : G) * (v : G) = 1 := by
      have hv2 : orderOf (v : G) = 2 := h.orderOf_eq_two (Or.inl v.2)
      rw [← pow_two, ← hv2]
      exact pow_orderOf_eq_one (v : G)
    have ha1 : a ≠ 1 := by
      intro h1
      have h1' : orderOf a = 1 := orderOf_eq_one_iff.mpr h1
      have h2 : orderOf a = 2 := h.typ.orderOf_a
      rw [h1'] at h2
      exact (by norm_num : (1 : ℕ) ≠ 2) h2
    have hconj : IsConj a (1 : G) := by
      have hb2 := b.2.2
      rw [hb, hvv] at hb2
      exact hb2
    exact ha1 (isConj_one_left.mp hconj)⟩
  left_inv u := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl

theorem cp_card_adj (h : F5Std a z) (v : ConjVert a) :
    Nat.card {u : ConjVert a // (Gamma a).Adj v u} = 2200 := by
  have hcard : Nat.card {u : ConjVert a // (Gamma a).Adj v u} =
      Nat.card ↥(orb2A a (v : G)) := Nat.card_congr (orb2A_adjEquiv h v)
  obtain ⟨g, hg⟩ := isConj_iff.mp v.2
  rw [hcard, ← hg, ← cp_card_orb2A h]
  exact (Nat.card_congr (orb2A_conjEquiv a g)).symm

end CFSG.EvenSporadicStandard.HNRecog.Section4
