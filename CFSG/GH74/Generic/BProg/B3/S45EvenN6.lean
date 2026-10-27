module

public import CFSG.GH74.Generic.BProg.B3.S45EvenSp4
public import CFSG.GH74.Generic.BProg.B3.S45EvenN3
public import CFSG.GH74.Generic.BProg.B3.S45EvenN4
public import CFSG.GH74.Generic.BProg.B3.S45EvenN5
public import CFSG.GH74.Generic.BProg.B3.S45TableB

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic.BProg.B3.S45TableA CFSG.GH74.Generic.BProg.B3.S45TableB

theorem N6_table
    (hF : GenericKnownFacts) (hE : E2.E2ComponentFacts) : S45EvenTableEA := by
  intro X _ _ hgen hq hZ2 hZ1 hGH y hy hd hab hEA
  classical
  have hKp : Group.IsPerfect X := hq.1
  rcases hGH with ⟨n, h7, h11, ⟨e⟩⟩ | hspor | ⟨p, f, hp, hf, hrow⟩
  ·
    by_cases hn : n = 7
    · subst hn
      exact (false_of_center_ne_bot_a7_w hKp hZ2 hZ1 e hd).elim
    · exact (N3_alt hKp hZ2 hZ1 (hF.alt_cover n h7 h11 X hq hZ2 ⟨e⟩) (by omega) h11 e hy hd hab).elim
  ·
    rcases hspor with h | h | h | h | h | h | h | h | h
    · exact (hZ1 (hE.noTwoCover_sporadic _ h X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact h
    · exact (hE.cover_not_gen4 X hq hZ2 (Or.inl h) hZ1 hgen).elim
    · exact (hE.cover_not_gen4_M23_J3 X hq hZ2 (Or.inl h) hZ1 hgen).elim
    · exact (hZ1 (hF.noTwoCover_J1 _ h X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (hE.cover_not_gen4 X hq hZ2 (Or.inr h) hZ1 hgen).elim
    · exact (hE.cover_not_gen4_M23_J3 X hq hZ2 (Or.inr h) hZ1 hgen).elim
    · exact (hZ1 (hF.noTwoCover_McL _ h X hq hZ2 hgen ⟨MulEquiv.refl _⟩)).elim
    · exact (hZ1 (hF.noTwoCover_Ly _ h X hq hZ2 hgen ⟨MulEquiv.refl _⟩)).elim
  ·
    rcases hrow with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (false_of_center_ne_bot_psl2_w hKp hZ2 hZ1 hp2 (stated_of_lieModel_PSL hm) hd).elim
    · exact (hZ1 (hF.noTwoCover_psl3 p f hp hp2 _ hm X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (hZ1 (hF.noTwoCover_psu3 p f hp hp2 _ hm X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · rcases hF.psp4_cover p f hp hp2 X hq hZ2 hm with hbot | ⟨F, _, _, hFc, ⟨eX⟩⟩
      · exact (hZ1 hbot).elim
      · exact (N2_sp4 (ringChar_ne_two_of_card_eq hp hp2 hFc) eX hd).elim
    · exact (hZ1 (hF.noTwoCover_g2 p f hp hp2 _ hm X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (hZ1 (hF.noTwoCover_3D4 p f hp hp2 _ hm X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psl_data hm
      have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq hp hp2 hFc
      have hodd : Odd (Nat.card F) := by rw [hFc]; exact (hp.odd_of_ne_two hp2).pow
      obtain ⟨π, hπ, hcompat⟩ := hF.psl4_cover X hq hZ2 F hodd eS
      rcases cover_branch_SL4 hF2 eS π hπ hcompat hZ1 with ⟨hmod4, ⟨eX⟩⟩ | ⟨-, hc⟩
      · exact (N4_sl4 hmod4 eX hy hd hab hEA).elim
      · exact (hc.not_gen4 (le_refl 4) hgen).elim
    · obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psu_data hm
      have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      obtain ⟨π, hπ, hcompat⟩ := hF.psu4_cover X hq hZ2 F (p ^ f) hFc hqodd eS
      rcases cover_branch_SU4 hFc (Nat.odd_iff.1 hqodd) eS π hπ hcompat hZ1 with
        ⟨hmod4, ⟨eX⟩⟩ | ⟨-, hc⟩
      · exact (N5_su4 hFc hmod4 eX hy hd hab hEA).elim
      · exact (hc.not_gen4 (le_refl 4) hgen).elim
    · exact (hZ1 (hF.noTwoCover_psl5 p f hp hmod _ hm X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (hZ1 (hF.noTwoCover_psu5 p f hp hmod _ hm X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (hZ1 (hF.noTwoCover_ree f _ hm X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (hZ1 (hE.noTwoCover_even _ (Or.inl hm) X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (hZ1 (hE.noTwoCover_even _ (Or.inr (Or.inl hm)) X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · exact (Stage1.Main.l34_cover_any X hq hZ2 hm hZ1 hgen).elim
    · exact (hZ1 (hE.noTwoCover_even _ (Or.inr (Or.inr hm)) X hq hZ2 ⟨MulEquiv.refl _⟩)).elim
    · obtain ⟨yb, -, -, hdb⟩ := datum_quotient hKp hy hd
      exact (false_of_sz8_datum hm hdb).elim

end CFSG.GH74.Generic.BProg.B3
