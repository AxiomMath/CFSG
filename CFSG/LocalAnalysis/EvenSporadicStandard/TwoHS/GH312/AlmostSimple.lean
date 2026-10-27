module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.InvolutionMemNormal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.SectionalRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleOneClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleClassical
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleAlternating
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleA9
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.PGSp45LieModel

public section

open Subgroup CFSG.LargeExtraspecial CFSG.Blueprint

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

theorem gh312AlmostSimple_of_gh74
    (hGH : AS35W.GH74Models) : GH312AlmostSimple := by
  intro X _ _ hO hZ hP hU T hTn hTs hTna hC
  haveI := hTn
  haveI := hTs
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, ⟨ι⟩⟩ := hP
  obtain ⟨u, hu2, hu1, ⟨e⟩⟩ := hU
  have hPcard : Nat.card (P : Subgroup X) = 2 ^ 7 := by
    rw [show Nat.card (P : Subgroup X) = Nat.card CFSG.EvenSporadicStandard.TwoHS.W8 from
      Nat.card_congr ι.toEquiv, SAFyGH.card_W8]
    norm_num
  have hX : 2 ^ 7 ∣ Nat.card X := by
    have := Subgroup.card_subgroup_dvd_card (P : Subgroup X)
    rwa [hPcard] at this
  have hTeven : Even (Nat.card ↥T) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    haveI := CFSG.Milestones.odd_order_solvable hodd
    obtain ⟨a, b, hab⟩ := hTna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
  obtain ⟨huT, hKT, -⟩ := mem_and_altCentralizer_le_and_card_dvd hu2 hu1 e P hPcard hTn hTeven
  have hloc : AlmostSimpleLocal ↥T ⟨u, huT⟩ :=
    AlmostSimpleLocal.of_altCentralizer_le hu2 hu1 e huT hKT
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hC960 : Nat.card ↥(centralizer ({u} : Set X)) = 960 := card_centralizer_eq_of_mulEquiv e
  have hnot : ¬ 2 ^ 7 ∣ Nat.card ↥(centralizer ({u} : Set X)) := by
    rw [hC960]
    norm_num
  have noOne : AS35W.OneClass ↥T → False := fun hone =>
    false_of_oneClass hTn hone huT hu_ord P hPcard hnot
  have hgen := sectionalTwoRankLE_four_subgroup_of_sylow_mulEquiv P ι T
  have hlist : AS35W.GH74List ↥T := hGH ↥T hTna hloc.three_le_twoRank hgen
  rcases hlist with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
    ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
    ⟨p, f, hp, hf, hq, h⟩ | h | ⟨n, h8, h11, ⟨eA⟩⟩ | h
  · exact (noOne (AS35W.oneClass_G2 hp hp2 h)).elim
  · exact (noOne (AS35W.oneClass_D4 hp hp2 h)).elim
  ·
    by_cases h5 : p ^ f = 5
    · refine Or.inr (nonempty_mulEquiv_pgsp45_of_lieModel T h5 h hC ?_)
      obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
      exact ne_top_of_two_pow_seven_dvd T (hK.trans h5) eK hX
    · exact (hloc.false_of_lieModel_psp_two hp hp2 hf h h5).elim
  · exact (noOne (AS35W.oneClass_Ree h)).elim
  · exact (hloc.false_of_lieModel_psl_four hp hp2 hf h).elim
  · rcases AS35W.odd_pow_mod_eight (f := f) hp hp2 with h1 | h1 | h1 | h1
    · exact (hloc.false_of_lieModel_psu_four hp hp2 hf (by omega) h).elim
    · exact (noOne (AS35W.oneClass_L4U4 hp hp2 (Or.inr ⟨h1, h⟩))).elim
    · exact (hloc.false_of_lieModel_psu_four hp hp2 hf (by omega) h).elim
    · exact absurd h1 hq
  · exact (hloc.false_of_lieModel_psl_five hp hf hq h).elim
  · exact (hloc.false_of_lieModel_psu_five hp hf hq h).elim
  · rcases h with h | h | h | h
    · exact (noOne (AS35W.oneClass_of_fusionIsBenderGroup
        (S8.fusionIsBenderGroup_of_lieModel_psl_two h))).elim
    · exact (noOne (AS35W.oneClass_of_fusionIsBenderGroup
        (S8.fusionIsBenderGroup_of_lieModel_psl_two h))).elim
    · exact (noOne (AS35W.oneClass_L34 h)).elim
    · exact (noOne (AS35W.oneClass_of_fusionIsBenderGroup
        (S8.fusionIsBenderGroup_of_lieModel_twistedB2 h))).elim
  ·
    by_cases hn9 : n = 9
    · subst hn9
      exact Or.inl (nonempty_mulEquiv_perm_fin_nine_of_mulEquiv_alternatingGroup T eA hC
        (ne_top_of_two_pow_seven_dvd_of_mulEquiv_alternatingGroup_nine T eA hX))
    · exact (hloc.false_of_mulEquiv_alternatingGroup eA h8 h11 hn9).elim
  · rcases h with h | h | h | h | h | h | h | h
    · exact (false_of_isSporadic_M12 hTn huT hloc h hC960 P hPcard).elim
    · exact (noOne (AS35W.oneClass_M22 h)).elim
    · exact (noOne (AS35W.oneClass_M23 h)).elim
    · exact (noOne (AS35W.oneClass_J1 h)).elim
    · exact (false_of_isSporadic_J2 hTn huT hloc h hC960 P hPcard).elim
    · exact (noOne (AS35W.oneClass_J3 h)).elim
    · exact (noOne (AS35W.oneClass_McL h)).elim
    · exact (noOne (AS35W.oneClass_Ly h)).elim

theorem gh312Fixed_of_gh74
    (hGH : AS35W.GH74Models) : CFSG.EvenSporadicStandard.TwoHS.GH312Fixed :=
  gh312Fixed_of_almostSimple (gh312AlmostSimple_of_gh74 hGH)

end CFSG.EvenSporadicStandard.TwoHS.GH312
