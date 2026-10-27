module

public import CFSG.GH74.Generic.S1.KL3Ord
public import CFSG.GH74.Generic.S1.KL3Cfg
public import CFSG.GH74.Generic.S1.KL3Red

public section

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl3Classify_of_families
    (hF : KL3Families) : KL3Classify := by
  intro S _ _ hS hGH F _ _ hF3 Pb hPe yb hyb hy2 hsolv
  obtain ⟨e⟩ := hPe
  have hdvd : 5616 ∣ Nat.card S := kl3_dvd_card hF3 e
  have hcfg : KL3Cfg F Pb yb := ⟨hF3, ⟨e⟩, hyb, hy2, hsolv⟩
  rcases hGH with ⟨n, hn7, hn11, ⟨eA⟩⟩ | hspor | ⟨p, f, hp, hf, hrest⟩
  · exact (kl3_false_alt hn7 hn11 eA hdvd).elim
  · exact (kl3_false_sporadic (by tauto) hdvd).elim
  · rcases hrest with ⟨hp2, hL⟩ | ⟨hp2, h8, hL⟩ | ⟨hp2, h8, hL⟩ | ⟨h4, hL⟩ | ⟨h4, hL⟩ | hRee |
      ⟨-, hsmall⟩
    · rcases hL with hL | hL | hL | hL | hL | hL
      · exact (hF.l2 S hS p f hp hp2 hf (statedClassicalModel_of_lieModel (by norm_num) hL) F Pb
          yb hcfg).elim
      · exact Or.inl (hF.l3 S hS p f hp hp2 hf (statedClassicalModel_of_lieModel (by norm_num) hL)
          F Pb yb hcfg)
      · exact (hF.u3 S hS p f hp hp2 hf (statedClassicalModel_of_lieModel (by norm_num) hL) F Pb
          yb hcfg).elim
      · exact (hF.sp4 S hS p f hp hp2 hf (statedClassicalModel_of_lieModel (by norm_num) hL) F Pb
          yb hcfg).elim
      · obtain ⟨rfl, rfl⟩ := hF.g2 S hS p f hp hp2 hf hL F Pb yb hcfg
        exact Or.inr (Or.inr hL)
      · exact (hF.d4 S hS p f hp hp2 hf hL F Pb yb hcfg).elim
    · obtain ⟨rfl, rfl⟩ := hF.l4 S hS p f hp hp2 hf h8
        (statedClassicalModel_of_lieModel (by norm_num) hL) F Pb yb hcfg
      exact Or.inr (Or.inl hL)
    · exact (hF.u4 S hS p f hp hp2 hf h8 (statedClassicalModel_of_lieModel (by norm_num) hL) F Pb
        yb hcfg).elim
    · exact (hF.l5 S hS p f hp hf h4 (statedClassicalModel_of_lieModel (by norm_num) hL) F Pb yb
        hcfg).elim
    · exact (hF.u5 S hS p f hp hf h4 (statedClassicalModel_of_lieModel (by norm_num) hL) F Pb yb
        hcfg).elim
    · exact (kl3_false_ree hRee hdvd).elim
    · exact (kl3_false_small hsmall hdvd).elim

theorem kl3Table_of_families
    (hF : KL3Families) (hS : KL3Surv) : KL3Table :=
  kl3Table_of_parts (kl3Classify_of_families hF) hS

end CFSG.GH74.Generic.S1
