module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentC
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE186

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

variable (p f) in
@[expose] def EBelowCent (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
      EStand p f Ω K S R W → (∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) →
        E186Cent2 Ω K H → H = ⊤

theorem natCard_quotient_lt {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 : 2 ≤ Nat.card N := by
    have := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
    omega
  have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  nlinarith

omit [Finite G] in
theorem eq_top_of_map_eq_top {N : Subgroup G} [N.Normal] (hNH : N ≤ H)
    (h : H.map (QuotientGroup.mk' N) = ⊤) : H = ⊤ := by
  have h1 : H.map (QuotientGroup.mk' N) = ⊤ := h
  have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' N) H
  rw [h1, QuotientGroup.ker_mk', sup_eq_left.mpr hNH, Subgroup.comap_top] at h2
  exact h2.symm

theorem MinCex.eq_bot_of_odd (c : MinCex p f Ω K S R W H) (hcent : E186Cent2 Ω K H)
    (hmin : EBelowCent p f (Nat.card G)) {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N))
    (hNH : N ≤ H) : N = ⊥ := by
  by_contra hne
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hΩ' : HypOmegaMod p f (quotFamily Ω N) := oddQuotHyp p f hp hq G Ω hΩ N hN
  obtain ⟨Sb, Rb, Wb, hst⟩ := c.odd_quot_stand hΩ' hN
  have h1 := hmin (G ⧸ N) (natCard_quotient_lt hne) (quotFamily Ω N) (K.map (QuotientGroup.mk' N))
    Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst (c.odd_quot_trans hΩ' hN)
    (E186Cent2.quot_odd hp hq hΩ hΩ' hN c.stand.mem hcent)
  exact c.proper (eq_top_of_map_eq_top hNH h1)

theorem MinCex.eq_bot_of_central (c : MinCex p f Ω K S R W H) (hcent : E186Cent2 Ω K H)
    (hmin : EBelowCent p f (Nat.card G)) (h182 : E18_2 p f) {N : Subgroup G} [N.Normal]
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hNH : N ≤ H)
    (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) : N = ⊥ := by
  by_contra hne
  have hc : CentQuot p f Ω N :=
    CentQuot.of_isPGroup c.stand.odd c.stand.five c.stand.hyp hNc hN2 hmeet
  obtain ⟨Sb, Rb, Wb, hst⟩ := MinCex.cent_quot_stand c hc
  have h1 := hmin (G ⧸ N) (natCard_quotient_lt hne) (quotFamily Ω N) (K.map (QuotientGroup.mk' N))
    Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst (MinCex.cent_quot_trans c hc)
    (E186Cent2.quot_cent c.proper hN2 hc c.stand.mem hcent
      (fun M hM u hu hu4 g hg => MinCex.mem_of_conj_mem c h182 hM hu hu4 hg))
  exact c.proper (eq_top_of_map_eq_top hNH h1)

end CFSG.ClassicalInvolution.Asc77.AscE186
