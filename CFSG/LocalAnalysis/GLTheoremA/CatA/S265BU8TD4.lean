module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T2
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPBasic
import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge lieOrderBridge_holds)

private theorem card_unTwo (hLO : LieOrderBridge) {R : Type} [Group R] [Finite R]
    (h : catalogIs R S9.isU5two ∨ catalogIs R S9.isU6two) :
    Nat.card R = 13685760 ∨ Nat.card R = 9196830720 := by
  rcases h with h | h
  · obtain ⟨d, hv, hP, he⟩ := CatB.exists_lieIndex h
    cases d <;> try exact hP.elim
    rename_i r q
    rcases r with _ | _ | _ | _ | _ | r <;> try exact hP.elim
    have hq : q.card = 2 := hP
    refine Or.inl ((hLO ⟨_, hv⟩ R he).trans ?_)
    show orderTwistedA 4 q.card = _
    rw [hq]
    decide +kernel
  · obtain ⟨d, hv, hP, he⟩ := CatB.exists_lieIndex h
    cases d <;> try exact hP.elim
    rename_i r q
    rcases r with _ | _ | _ | _ | _ | _ | r <;> try exact hP.elim
    have hq : q.card = 2 := hP
    refine Or.inr ((hLO ⟨_, hv⟩ R he).trans ?_)
    show orderTwistedA 5 q.card = _
    rw [hq]
    decide +kernel


theorem QUCfg.fieldOn_of_unTwo {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b)
    (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU5two ∨
      catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU6two) : FieldOn 3 b S := by
  rcases cfg.prop with hF | ⟨-, hT, -⟩
  · exact hF
  exfalso
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hbp : b ^ 3 = 1 := cfg.elem.2 b cfg.hb
  obtain ⟨hb, E, hEC, hE, hna, hperf, h2, -⟩ := FR.coreSub_of_r2 hp hp2 FR.Res.smallDatum_holds
    (FR.Res.twF4Core_holds hp hp2) FR.Res.td4Core_holds cfg.comp cfg.chev hbp cfg.prop cfg.ipart
  have hEC' := hEC
  have hperf' := hperf
  rw [FR.fixSub_indAut hb] at hEC' hperf'
  obtain ⟨J₀, hJ₀, hIeq, -⟩ := FR.ipart_single hp hb hbp hE hEC' hperf' cfg.ipart
  obtain ⟨e⟩ := I91T.pSimple_component_equiv hp hb hbp hE hEC hna hperf hJ₀
  rw [← hIeq] at e
  have hcent := FP.centCard2_eq_twoPart_fixNum hb (FP.odd_card_center_pQuot hp hp2 S)
  rw [FP.fixNum_eq_card_fixSub] at hcent
  have hle : twoPart (Nat.card E) ≤ centCard2 3 S b := by
    rw [hcent]
    exact lemma102_twoPart_le_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le hEC)
  have hge : centCard2 3 S b ≤ 2 * twoPart (Nat.card E) := by
    rw [hcent]
    exact h2
  obtain ⟨q, hv, ⟨eS⟩⟩ := FR.Res.td4_index' hT
  have hqp : q.p = 2 := by
    by_contra hne
    exact FR.Res.td4_odd_false' hv hne eS cfg.chev
  have hcardS : Nat.card (PSimple 3 S) = orderTrialityD4 q.card :=
    lieOrderBridge_holds ⟨.trialityD4 q, hv⟩ (PSimple 3 S) ⟨eS⟩
  rw [TauCeti.PrimePower.card_def, hqp] at hcardS
  obtain ⟨O, hO, -, hOrd⟩ := CatDistinct.orderTrialityD4_two_pow q.exponent_pos
  have hsqrt : centCard2 3 S b = 2 ^ (q.exponent * 6) := by
    rw [cfg.g2 rfl hT, FP.card2_eq_twoPart_card_pSimple hp hp2, hcardS, hOrd,
      FQ.twoPart_two_pow_mul_odd hO,
      show (2 : ℕ) ^ (q.exponent * 12) = (2 ^ (q.exponent * 6)) ^ 2 by rw [← pow_mul]; ring_nf,
      Nat.sqrt_eq']
  have hexp : ∀ a O' : ℕ, Odd O' → Nat.card E = 2 ^ a * O' →
      a ≤ q.exponent * 6 ∧ q.exponent * 6 ≤ a + 1 := by
    intro a O' hO' hEa
    rw [hEa, FQ.twoPart_two_pow_mul_odd hO', hsqrt] at hle hge
    exact ⟨(Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle,
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [pow_succ']; exact hge)⟩
  have hNE : Nat.card (PSimple 3 (Ipart 3 S b)) = Nat.card E := Nat.card_congr e.toEquiv
  rcases card_unTwo lieOrderBridge_holds hJ with h | h <;> rw [hNE] at h
  · obtain ⟨h1, h1'⟩ := hexp 10 13365 (by decide) (h.trans (by norm_num))
    omega
  · obtain ⟨h1, h1'⟩ := hexp 15 280665 (by decide) (h.trans (by norm_num))
    omega

end CFSG.LocalAnalysis.GLTheoremA.S265

end
