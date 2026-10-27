module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieRanges
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
import CFSG.CGT.PushingUpLit.SolKNA.QuatLieDatum
import CFSG.ClassicalInvolution.Q3.TA3SOLA0
import CFSG.ClassicalInvolution.Q3.TA3SOLL3U3
import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4
import CFSG.ClassicalInvolution.Q3.TA3SOLL5U5
import CFSG.ClassicalInvolution.Q3.TA3SOLSp4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG CFSG.ClassicalInvolution CFSG.Blueprint CFSG.GH74.Filter
open CFSG.ClassicalInvolution.Q3.TA3

theorem qlSmall_of_small3 (h3 : Small3Table) : QLSmall := by
  intro G _ _ K hst R hqu hodd hFG
  have : IsSimpleGroup G := hst.simple
  obtain ⟨t, P, SP, hTD, -, -, -⟩ := pieceTightDatum G K hst R hqu
  have hD : HasDatum G := ⟨P, SP, t, hTD⟩
  obtain ⟨tag, n, p, f, hp, hp2, hadm, hmG⟩ := hodd
  have hf : 1 ≤ f := hadm.2.1
  have hq := eq_three_or_five_le_pow hp hp2 hf
  have hodd2 := pow_mod_two_of_ne_two (f := f) hp hp2
  have hm' := hmG
  rcases hm' with ⟨htag, hc⟩ | ⟨rfl, htag, he⟩ | ⟨rfl, htag, hr⟩ | ⟨-, -, hsz⟩
  · cases tag
    case PSL =>
      obtain ⟨-, -, hn, -⟩ := hadm
      rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n) with
        rfl | rfl | rfl | rfl | rfl | hn7
      · exact (noDatumL2 G p f hp2 hc hD).elim
      · rcases hq with ⟨rfl, rfl⟩ | h5
        · exact h3 G .PSL 3 (Or.inl ⟨rfl, Or.inl rfl⟩) hmG K hst R hqu
        · exact (noDatumL3U3_holds G .PSL p f (Or.inl rfl) hp hp2 h5 hc hFG hD).elim
      · by_cases h8 : p ^ f % 8 = 1
        · exact (t_PSL_four_odd G p f hp2 h8 hc hFG).elim
        · rcases hq with ⟨rfl, rfl⟩ | h5
          · exact h3 G .PSL 4 (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩) hmG K hst R hqu
          · exact (noDatumL4U4_holds G p f hp hp2 h5 (Or.inl ⟨h8, hc⟩) hFG hD).elim
      · by_cases h4 : p ^ f % 4 = 1
        · exact (t_PSL_five_odd G p f hp2 h4 hc hFG).elim
        · have h43 : p ^ f % 4 = 3 := by omega
          rcases hq with ⟨rfl, rfl⟩ | h5
          · exact h3 G .PSL 5 (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩) hmG K hst R hqu
          · exact (noDatumL5U5_holds G p f hp hp2 h5 (Or.inl ⟨h43, hc⟩) hFG hD).elim
      · exact (t_PSL_six_odd G p f hp2 hc hFG).elim
      · exact (t_PSL_ge_seven_odd G n p f hp2 hn7 hc hFG).elim
    case PSU =>
      obtain ⟨-, -, hn, -⟩ := hadm
      rcases (by omega : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n) with
        rfl | rfl | rfl | rfl | hn7
      · rcases hq with ⟨rfl, rfl⟩ | h5
        · exact h3 G .PSU 3 (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)) hmG K hst R hqu
        · exact (noDatumL3U3_holds G .PSU p f (Or.inr rfl) hp hp2 h5 hc hFG hD).elim
      · by_cases h8 : p ^ f % 8 = 7
        · exact (t_PSU_four_odd G p f hp2 h8 hc hFG).elim
        · rcases hq with ⟨rfl, rfl⟩ | h5
          · exact h3 G .PSU 4 (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)) hmG K hst R hqu
          · exact (noDatumL4U4_holds G p f hp hp2 h5 (Or.inr ⟨h8, hc⟩) hFG hD).elim
      · by_cases h4 : p ^ f % 4 = 3
        · exact (t_PSU_five_odd G p f hp2 h4 hc hFG).elim
        · have h41 : p ^ f % 4 = 1 := by omega
          rcases hq with ⟨rfl, rfl⟩ | h5
          · exact absurd (by norm_num) h4
          · exact (noDatumL5U5_holds G p f hp hp2 h5 (Or.inr ⟨h41, hc⟩) hFG hD).elim
      · exact (t_PSU_six_odd G p f hp2 hc hFG).elim
      · exact (t_PSU_ge_seven_odd G n p f hp2 hn7 hc hFG).elim
    case PSp =>
      obtain ⟨-, -, hn, -⟩ := hadm
      rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
      · rcases hq with ⟨rfl, rfl⟩ | h5
        · exact h3 G .PSp 2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hmG K hst R hqu
        · exact (noDatumSp4_holds G p f hp hp2 h5 hc hFG hD).elim
      · exact (t_PSp_odd_ge_three G n p f hp2 hn3 hc hFG).elim
    case POmegaOdd =>
      obtain ⟨-, -, hn, -⟩ := hadm
      exact (t_POmegaOdd G n p f hp2 hn hc hFG).elim
    case POmegaPlus => exact (t_POmegaPlus_odd G n p f hp2 hc hFG).elim
    case POmegaMinus => exact (t_POmegaMinus_odd G n p f hp2 hc hFG).elim
    all_goals exact absurd htag (by decide)
  · cases tag
    case G2 =>
      rcases hq with ⟨rfl, rfl⟩ | h5
      · exact h3 G .G2 0 (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, rfl⟩))) hmG K hst R hqu
      · exact (noDatumG2D4 G .G2 p f (Or.inl rfl) hp hp2 h5 he hFG hD).elim
    case trialityD4 =>
      rcases hq with ⟨rfl, rfl⟩ | h5
      · exact h3 G .trialityD4 0 (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, rfl⟩))) hmG K hst R hqu
      · exact (noDatumG2D4 G .trialityD4 p f (Or.inr rfl) hp hp2 h5 he hFG hD).elim
    case F4 => exact (t_F4_odd G p f hp2 he hFG).elim
    case E6 => exact (t_E6_odd G p f hp2 he hFG).elim
    case E7 => exact (t_E7_odd G p f hp2 he hFG).elim
    case E8 => exact (t_E8_odd G p f hp2 he hFG).elim
    case twistedE6 => exact (t_2E6_odd G p f hp2 he hFG).elim
    all_goals exact absurd htag (by decide)
  · cases tag
    case twistedG2 =>
      obtain ⟨-, -, -, hp3, -⟩ := hadm
      subst hp3
      exact (noDatumRee G f hr hD).elim
    case twistedF4 =>
      obtain ⟨-, -, -, hp2', -⟩ := hadm
      exact absurd hp2' hp2
    case Tits =>
      obtain ⟨-, -, -, hp2', -⟩ := hadm
      exact absurd hp2' hp2
    all_goals exact absurd htag (by decide)
  · exact absurd hsz.1 hp2

end CFSG.CGT.PushingUpLit.SolKNA
