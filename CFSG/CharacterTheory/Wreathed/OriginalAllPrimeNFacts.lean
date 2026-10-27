module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFactsConstraint
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.Wreathed.OriginalAllPrime

variable {G : Type} [Group G] [Finite G]

theorem wreathedSetting_nStructure
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    (wreathedSetting n S e p f).NStructure where
  L_eq := wreathedSetting_L_eq hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  N_oddCore_of_cover :=
    wreathedSetting_N_oddCore_of_cover hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  N_solvRad := wreathedSetting_N_solvRad hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  N_minimalNormal :=
    wreathedSetting_N_minimalNormal hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  N_coverTransfer :=
    wreathedSetting_N_coverTransfer hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  N_constraint_criterion :=
    wreathedSetting_N_constraint_criterion hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  center_S_eq_center_D :=
    wreathedSetting_center_S_eq_center_D hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  center_involution_of_sylow :=
    wreathedSetting_center_involution_of_sylow hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  normal_le_center_of_inf_D :=
    wreathedSetting_normal_le_center_of_inf_D hnonab n hn S e hfour p f hp hpodd hf hq hlocal

end CFSG.Wreathed.OriginalAllPrime
