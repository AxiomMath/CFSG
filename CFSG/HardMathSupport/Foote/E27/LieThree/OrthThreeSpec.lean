module

public import CFSG.HardMathSupport.Foote.E27.LieThree.OrthThreeOrder
public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill
public import CFSG.RankThree.PartOne.N143.O7
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import Certificates.Certificate131009

public section

namespace CFSG.HardMathSupport.Foote.E27

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143.O7

section Certificates


theorem o73_S0 : ∃ S : Subgroup ↥Om, Nat.card S = 3 ^ (Nat.card ↥Om).factorization 3 ∧
    ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ centralizer ({s} : Set ↥Om)) := by
  obtain ⟨S, hcard, hprop⟩ := Certificates.certificate131009
  have hdvd : 3 ^ 9 ∣ Nat.card ↥Om := hcard ▸ Subgroup.card_subgroup_dvd_card S
  have hge : 9 ≤ (Nat.card ↥Om).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 hdvd
  have hfac : (Nat.card ↥Om).factorization 3 = 9 := le_antisymm factorization_three_om_le hge
  exact ⟨S, by rw [hcard, hfac], hprop⟩

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_pomega_seven_three (h : E27Config X K R T z) (hz : z ∈ K)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    (eK : ↥K ≃* StatedProj (StatedOmega (StatedQuadOdd 3 F))) : False := by
  obtain ⟨S, hS, hprop⟩ := o73_S0
  exact h.false_of_sylow_table hz (eK.trans (modelEquiv hF)) S hS hprop

open TauCeti in
theorem E27Config.false_of_typeB_three_three (h : E27Config X K R T z) (hz : z ∈ K)
    (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid) (hq : q.p = 3 ∧ q.exponent = 1)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) : False := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv (by omega) le_rfl e
  rw [hq.1, hq.2] at hm
  obtain ⟨-, F, hF, hFin, hFcard, ⟨eK⟩⟩ := hm
  exact h.false_of_pomega_seven_three hz (by simpa using hFcard) eK

end Certificates

end CFSG.HardMathSupport.Foote.E27
