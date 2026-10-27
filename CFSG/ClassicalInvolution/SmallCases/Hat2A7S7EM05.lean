module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM04
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EThm2
public import CFSG.ClassicalInvolution.Asc77.AscE186Close
public import CFSG.ClassicalInvolution.Q3.Q3T7FUE5

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E

section
namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

@[expose] def EBelowCent (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
      EStand Ω K S R W → (∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) →
        E186Cent2 Ω K H → H = ⊤

theorem MinCex.eq_bot_of_odd (c : MinCex Ω K S R W H) (hcent : E186Cent2 Ω K H)
    (hmin : EBelowCent (Nat.card G)) {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N))
    (hNH : N ≤ H) : N = ⊥ := by
  by_contra hne
  have hΩ : HM Ω := c.stand.hyp
  have hΩ' : HM (quotFamily Ω N) := oddQuotHyp G Ω hΩ N hN
  obtain ⟨Sb, Rb, Wb, hst⟩ := c.odd_quot_stand hΩ' hN
  have h1 := hmin (G ⧸ N) (natCard_quotient_lt hne) (quotFamily Ω N) (K.map (QuotientGroup.mk' N))
    Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst (c.odd_quot_trans hΩ' hN)
    (E186Cent2.quot_odd hΩ hΩ' hN c.stand.mem hcent)
  exact c.proper (eq_top_of_map_eq_top hNH h1)

theorem MinCex.eq_bot_of_central (c : MinCex Ω K S R W H) (hcent : E186Cent2 Ω K H)
    (hmin : EBelowCent (Nat.card G)) (h182 : E18_2) {N : Subgroup G} [N.Normal]
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hNH : N ≤ H)
    (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) : N = ⊥ := by
  by_contra hne
  have hc : CentQuot Ω N :=
    CentQuot.of_isPGroup c.stand.hyp hNc hN2 hmeet
  obtain ⟨Sb, Rb, Wb, hst⟩ := MinCex.cent_quot_stand c hc
  have h1 := hmin (G ⧸ N) (natCard_quotient_lt hne) (quotFamily Ω N) (K.map (QuotientGroup.mk' N))
    Sb Rb Wb (H.map (QuotientGroup.mk' N)) hst (MinCex.cent_quot_trans c hc)
    (E186Cent2.quot_cent c.proper hN2 hc c.stand.mem hcent
      (fun M hM u hu hu4 g hg => MinCex.mem_of_conj_mem c h182 hM hu hu4 hg))
  exact c.proper (eq_top_of_map_eq_top hNH h1)

end Asc77.AscE186
end
section
namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

theorem e18_6_of_wfree (hcent : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K :
    Subgroup G)
      (S : Sylow 2 G) (R W H : Subgroup G), MinCex Ω K S R W H → E186Cent2 Ω K H)
    (hmin : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
      (S : Sylow 2 G) (R W H : Subgroup G), MinCex Ω K S R W H →
        EBelowCent (Nat.card G)) : E18_6 :=
  e18_6
    (fun G _ _ Ω K S R W H c _ _ hN hNH =>
      MinCex.eq_bot_of_odd c (hcent G Ω K S R W H c) (hmin G Ω K S R W H c) hN hNH)
    (fun G _ _ Ω K S R W H c _ _ hNc hN2 hNH hmeet =>
      MinCex.eq_bot_of_central c (hcent G Ω K S R W H c) (hmin G Ω K S R W H c)
        (e18_2_of_l6_9_l6_11 (l6_9_proved) (l6_11_proved)) hNc hN2 hNH hmeet)
    (thm2)

end Asc77.AscE186
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_z (c : MinCex Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W ∧ Subgroup.centralizer ({z} : Set G) ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.exists_z c.toU

theorem MinCex.hbad_of_conj (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {z g : G} (hz : IsUniqueInvolution K z) (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M (g * z * g⁻¹) → ∀ u ∈ M, orderOf u = 4 → u ∉ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.hbad_of_conj c.toU hA hM hz hg

theorem MinCex.goodFour_of_commute (h : E187Hyps) (c : MinCex Ω K S R W H) {z g t : G}
    (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H)
    (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hcomm : t * z = z * t) :
    GoodFour H t :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.goodFour_of_commute h.toU c.toU hz hzH hg ht htS hcomm

end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7E
