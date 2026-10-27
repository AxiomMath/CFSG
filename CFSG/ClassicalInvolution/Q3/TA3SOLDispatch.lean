module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.TA3SmallOddLieS
public import CFSG.GH74.Filter.ClassicalOdd.Unitary
public import CFSG.GH74.Filter.ClassicalOdd.Symplectic
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.GH74.Filter.Lie.TwistedE6Odd

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ClassicalInvolution.Q3.Q3T.MFS CFSG.GH74.Filter

theorem eq_three_or_five_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    (p = 3 ∧ f = 1) ∨ 5 ≤ p ^ f := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by norm_num)
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  by_cases h3 : p = 3
  · subst h3
    rcases Nat.lt_or_ge f 2 with h | h
    · exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h))
  · exact Or.inr (by omega)

theorem pow_mod_two_of_ne_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ^ f % 2 = 1 :=
  Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)

theorem smallOddLieTightMemberS_of_parts (hL2 : NoDatumL2) (hRee : NoDatumRee)
    (hG2D4 : NoDatumG2D4) (h3 : Member3Three) (hL3U3 : NoDatumL3U3) (hSp4 : NoDatumSp4)
    (hL4U4 : NoDatumL4U4) (hL5U5 : NoDatumL5U5) : SmallOddLieTightMemberS := by
  intro G _ _ _ _ hnab hF hodd R S hS t ht hto hRC hRn h2
  have hD : HasDatum G := ⟨R, S, t, ⟨hS, ht, hto, hRC, hRn, h2⟩⟩
  have hnabG : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  obtain ⟨e⟩ := nonempty_genFittingFStar_equiv G hnabG
  have hFG : TwoSubgroupsFourGenerated G := GH74.Gen4.of_mulEquiv e hF
  obtain ⟨tag, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  have hmG : LieModel G tag n p f := LieType.CurtisTits.lieModel_of_mulEquiv e hm
  have hf : 1 ≤ f := hadm.2.1
  have hq := eq_three_or_five_le_pow hp hp2 hf
  have hodd2 := pow_mod_two_of_ne_two (f := f) hp hp2
  show HasMember3 G
  have hm' := hmG
  rcases hm' with ⟨htag, hc⟩ | ⟨rfl, htag, he⟩ | ⟨rfl, htag, hr⟩ | ⟨-, -, hsz⟩
  · cases tag
    case PSL =>
      obtain ⟨-, -, hn, -⟩ := hadm
      rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n) with
        rfl | rfl | rfl | rfl | rfl | hn7
      · exact (hL2 G p f hp2 hc hD).elim
      · rcases hq with ⟨rfl, rfl⟩ | h5
        · exact h3 G .PSL 3 (Or.inl ⟨rfl, Or.inl rfl⟩) hmG
        · exact (hL3U3 G .PSL p f (Or.inl rfl) hp hp2 h5 hc hFG hD).elim
      · by_cases h8 : p ^ f % 8 = 1
        · exact (t_PSL_four_odd G p f hp2 h8 hc hFG).elim
        · rcases hq with ⟨rfl, rfl⟩ | h5
          · exact h3 G .PSL 4 (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩) hmG
          · exact (hL4U4 G p f hp hp2 h5 (Or.inl ⟨h8, hc⟩) hFG hD).elim
      · by_cases h4 : p ^ f % 4 = 1
        · exact (t_PSL_five_odd G p f hp2 h4 hc hFG).elim
        · have h43 : p ^ f % 4 = 3 := by omega
          rcases hq with ⟨rfl, rfl⟩ | h5
          · exact h3 G .PSL 5 (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩) hmG
          · exact (hL5U5 G p f hp hp2 h5 (Or.inl ⟨h43, hc⟩) hFG hD).elim
      · exact (t_PSL_six_odd G p f hp2 hc hFG).elim
      · exact (t_PSL_ge_seven_odd G n p f hp2 hn7 hc hFG).elim
    case PSU =>
      obtain ⟨-, -, hn, -⟩ := hadm
      rcases (by omega : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n) with
        rfl | rfl | rfl | rfl | hn7
      · rcases hq with ⟨rfl, rfl⟩ | h5
        · exact h3 G .PSU 3 (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)) hmG
        · exact (hL3U3 G .PSU p f (Or.inr rfl) hp hp2 h5 hc hFG hD).elim
      · by_cases h8 : p ^ f % 8 = 7
        · exact (t_PSU_four_odd G p f hp2 h8 hc hFG).elim
        · rcases hq with ⟨rfl, rfl⟩ | h5
          · exact h3 G .PSU 4 (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)) hmG
          · exact (hL4U4 G p f hp hp2 h5 (Or.inr ⟨h8, hc⟩) hFG hD).elim
      · by_cases h4 : p ^ f % 4 = 3
        · exact (t_PSU_five_odd G p f hp2 h4 hc hFG).elim
        · have h41 : p ^ f % 4 = 1 := by omega
          rcases hq with ⟨rfl, rfl⟩ | h5
          · exact absurd (by norm_num) h4
          · exact (hL5U5 G p f hp hp2 h5 (Or.inr ⟨h41, hc⟩) hFG hD).elim
      · exact (t_PSU_six_odd G p f hp2 hc hFG).elim
      · exact (t_PSU_ge_seven_odd G n p f hp2 hn7 hc hFG).elim
    case PSp =>
      obtain ⟨-, -, hn, -⟩ := hadm
      rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
      · rcases hq with ⟨rfl, rfl⟩ | h5
        · exact h3 G .PSp 2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hmG
        · exact (hSp4 G p f hp hp2 h5 hc hFG hD).elim
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
      · exact h3 G .G2 0 (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, rfl⟩))) hmG
      · exact (hG2D4 G .G2 p f (Or.inl rfl) hp hp2 h5 he hFG hD).elim
    case trialityD4 =>
      rcases hq with ⟨rfl, rfl⟩ | h5
      · exact h3 G .trialityD4 0 (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, rfl⟩))) hmG
      · exact (hG2D4 G .trialityD4 p f (Or.inr rfl) hp hp2 h5 he hFG hD).elim
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
      exact (hRee G f hr hD).elim
    case twistedF4 =>
      obtain ⟨-, -, -, hp2', -⟩ := hadm
      exact absurd hp2' hp2
    case Tits =>
      obtain ⟨-, -, -, hp2', -⟩ := hadm
      exact absurd hp2' hp2
    all_goals exact absurd htag (by decide)
  · exact absurd hsz.1 hp2

end CFSG.ClassicalInvolution.Q3.TA3
