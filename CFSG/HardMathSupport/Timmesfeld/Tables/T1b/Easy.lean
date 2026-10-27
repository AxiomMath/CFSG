module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.PSL2Odd
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Easy
public import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
public import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.RankThree.PartOne.AUTSL.OddOutRee
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.OutStructure

@[expose] def OutEasy (p : ℕ) : StatedLieTag → ℕ → ℕ → ℕ → Prop
  | .PSL, n, r, f => 3 ≤ n → ¬ p ∣ Nat.gcd n (r ^ f - 1)
  | .PSU, n, r, f => ¬ p ∣ Nat.gcd n (r ^ f + 1)
  | .PSp, _, _, _ => True
  | .POmegaOdd, _, _, _ => True
  | .POmegaPlus, n, _, _ => n = 4 → 3 < p
  | .POmegaMinus, _, _, _ => True
  | .E6, _, r, f => p ≠ 3 ∨ ¬ 3 ∣ r ^ f - 1 ∨ ¬ 3 ∣ f
  | .twistedE6, _, r, f => p ≠ 3 ∨ ¬ 3 ∣ r ^ f + 1 ∨ ¬ 3 ∣ f
  | .G2, _, _, _ => True
  | .F4, _, _, _ => True
  | .E7, _, _, _ => True
  | .E8, _, _, _ => True
  | .trialityD4, _, _, _ => True
  | .twistedB2, _, _, _ => True
  | .twistedG2, _, _, _ => True
  | .twistedF4, _, _, _ => True
  | .Tits, _, _, _ => True

theorem five_le_of_three_lt {p : ℕ} (hp : p.Prime) (h : 3 < p) : 5 ≤ p := by
  by_contra h5
  have : p = 4 := by omega
  subst this
  norm_num at hp

theorem three_lt_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 3 < p := by
  have := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  omega

theorem outPChain_of_lieModel
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n r f : ℕ} (hm : CFSG.Blueprint.LieModel X t n r f)
    (h : OutEasy p t n r f) : OutPChain p X := by
  rcases hm with ⟨ht, hc⟩ | ⟨h0, ht, hc⟩ | ⟨h0, ht, hc⟩ | ⟨h0, rfl, hc⟩
  · cases t
    case PSL =>
      have hn2 : 2 ≤ n := hc.1.2.2.1
      by_cases hn : n = 2
      · subst hn
        by_cases hr : r = 2
        · subst hr
          exact (outPNice_PSL_two hp hc).toChain
        · exact (outPNice_PSL_two_odd_all hp hp2 hr hc).toChain
      · exact (outPNice_PSL_ge_three_odd hp hp2 (by omega) hc (h (by omega))).toChain
    case PSU => exact (outPNice_PSU_odd hp hc h).toChain
    case PSp =>
      have hn2 : 2 ≤ n := hc.1.2.2.1
      by_cases hn : n = 2
      · subst hn
        by_cases hr : r = 2
        · subst hr
          exact (outPNice_PSp_two hp hc).toChain
        · exact (CFSG.RankThree.PartOne.AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hr hc).toChain
      · by_cases hr : r = 2
        · subst hr
          exact (outPNice_PSp_ge_three hp (by omega) hc).toChain
        · exact (outPNice_PSp_ge_three_odd hp hp2 (by omega) hc).toChain
    case POmegaOdd =>
      exact (outPNice_POmegaOdd_all hp hp2 hc).toChain
    case POmegaPlus =>
      have hn4 : 4 ≤ n := hc.1.2.2
      by_cases hn : n = 4
      · subst hn
        have h5 := five_le_of_three_lt hp (h rfl)
        by_cases hr : r = 2
        · subst hr
          exact outPChain_POmegaPlus_four hp (h rfl) hc
        · exact outPChain_POmegaPlus_four_gen hp h5 hc
      · by_cases hr : r = 2
        · subst hr
          exact (outPNice_POmegaPlus_ge_five hp hp2 (by omega) hc).toChain
        · exact (outPNice_POmegaPlus_all_ge_five hp hp2 (by omega) hc).toChain
    case POmegaMinus =>
      have hn4 : 4 ≤ n := hc.1.2.2
      by_cases hr : r = 2
      · subst hr
        exact (outPNice_POmegaMinus hp hp2 hn4 hc).toChain
      · exact (outPNice_POmegaMinus_all hp hp2 hc).toChain
    all_goals exact absurd ht (by decide)
  · cases t
    case G2 =>
      by_cases hr2 : r = 2
      · subst hr2
        exact (outPNice_G2 hp hc).toChain
      · by_cases hr3 : r = 3
        · subst hr3
          exact (outPNice_G2_three hp hc).toChain
        · exact (outPNice_G2_odd hp hr2 hr3 hc).toChain
    case F4 =>
      by_cases hr2 : r = 2
      · subst hr2
        exact (outPNice_F4 hp hc).toChain
      · exact (outPNice_F4_odd hp hr2 hc).toChain
    case E6 =>
      by_cases hp3 : p = 3
      · subst hp3
        obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := hc
        exact outPChain_E6_three hrp hf1 hm (h.resolve_left (fun h => h rfl))
      · exact (outPNice_E6_gen hp hp3 hp2 hc).toChain
    case E7 => exact (outPNice_E7_gen hp hp2 hc).toChain
    case E8 => exact (outPNice_E8_gen hp hc).toChain
    case twistedE6 =>
      by_cases hp3 : p = 3
      · subst hp3
        obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := hc
        exact outPChain_twistedE6_three hrp hf1 hm (h.resolve_left (fun h => h rfl))
      · exact (outPNice_twistedE6_gen hp hp3 hc).toChain
    case trialityD4 =>
      by_cases hr2 : r = 2
      · subst hr2
        exact (outPNice_trialityD4 hp hc).toChain
      · exact (outPNice_trialityD4_odd hp hr2 hc).toChain
    all_goals exact absurd ht (by decide)
  · cases t
    case twistedG2 =>
      obtain rfl : r = 3 := hc.1.2.2.2.1
      exact (CFSG.RankThree.PartOne.AUTSL.outPNice_twistedG2 hp hc).toChain
    case twistedF4 =>
      obtain rfl : r = 2 := hc.1.2.2.2.1
      exact (outPNice_twistedF4 hp hc).toChain
    case Tits =>
      have hQ := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier X r f hc).1
      refine (CFSG.RankThree.PartOne.PlaneCases.outPNice_of_not_dvd_outer hp ?_).toChain
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      rw [hk]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    all_goals exact absurd ht (by decide)
  · obtain rfl : r = 2 := hc.1
    exact (outPNice_Suzuki hp hc).toChain

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
