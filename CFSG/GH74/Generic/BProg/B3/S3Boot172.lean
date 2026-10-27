module

public import CFSG.GH74.Generic.BProg.B3.S3Boot175
public import CFSG.GH74.Generic.BProg.B3.S3Boot154
public import CFSG.GH74.Generic.BProg.B1.NontrivNonsolv

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

section SD14

variable {G : Type} [Group G] [Finite G]

theorem prop172_p2 (hKG : BootKG G) (hB2 : B_B2_g4) {x a : G} {K A D J B : Subgroup G}
    (hc : Ctx21 G x K A a D J) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hext : IsExtSource2 x K A B) (hB4 : pRank 2 ↥B = 4) {y : G}
    {Lb : Subgroup (CentralizerBar x)} (hadm : IsBAdmPair x K B y Lb)
    (hns : ¬ NbhdSemisimple x y Lb) (h8 : A7InGamma K A B) :
    ¬ (IsKBal 3 B ∧ IsWeakKBal 2 B) := by
  rintro ⟨hbal, hweak⟩
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hext.2.2.2.1
  have hBE : IsE 4 ⊤ B := ⟨le_top, hBel, hext.2.2.2.2.1⟩
  have hIL : IsILo 2 x K := hc.circ.1.1.1
  have hterm : IsTwoTerminal x K := hc.circ.1.2.2
  have hth : thetaPrime52 B ≠ ⊥ :=
    prop114_p2 hB2 (B1.kgroup_centralizers hc.hyp) hIL.1 hIL.2.2 hext hB4 hadm hns
  obtain ⟨hodd, hΓN, hθ⟩ := prop41_52 hBE hbal hweak
  have hθ52 : thetaHalf 2 B ≠ ⊥ := fun h => hth (le_bot_iff.mp (hθ.trans h.le))
  have hMne : normalizer (thetaHalf 2 B : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : (thetaHalf 2 B).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hc.hyp.simple.eq_bot_or_eq_top_of_normal (thetaHalf 2 B) with h | h
    · exact hθ52 h
    · have h16 : Nat.card ↥B = 2 ^ pRank 2 ↥B := C3.Layer1.Back.card_eq_two_pow_pRank hBel
      rw [hB4] at h16
      have hdvd : Nat.card ↥B ∣ Nat.card G := Subgroup.card_subgroup_dvd_card B
      rw [h16] at hdvd
      have h2 : 2 ∣ Nat.card G := (dvd_pow_self 2 (by norm_num)).trans hdvd
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hKM : K ≤ normalizer (thetaHalf 2 B : Set G) :=
    (hKG.hKB x K A B hc.hyp hterm h3 hc.src hext hB4).trans hΓN
  obtain ⟨hl1, hl2⟩ := lemma175_p2 hKG hB2 hc.hyp hterm h3 hc.src hext hB4 hMne hKM hΓN
  have hboot : Boot15B G x K A B (normalizer (thetaHalf 2 B : Set G)) :=
    { hyp := hc.hyp, noAlt := hc.noAlt, term := hterm, shape := h3, src := hc.src,
      notAllow := hc.notAllow, theta := hc.theta, AB := hext.1, B_cent := hext.2.2.1,
      B_E4 := hBE, B_rank := hB4, theta52 := hθ52, bal52 := ⟨hbal, hweak⟩, M_ne := hMne,
      M_norm := le_rfl, K_le := hKM, locM := hl1, a7 := h8, locM' := hl2,
      a15A7 := hKG.l15A7 x K A a D J hc h3 }
  exact hc.notBal (prop151_p2 hKG hboot)

end SD14

end CFSG.GH74.Generic.BProg.B3
