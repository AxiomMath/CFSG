module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallSAct
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallOutChar
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG Subgroup CFSG.ComponentClassification.GSThmB
open CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank GorensteinWalter
  AutL2Facts

theorem hasOuterChar_of_small {Y : Type} [Group Y] (h : IsSmallAltOrL2 Y) : HasOuterChar Y := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · rcases hn with rfl | rfl | rfl
    · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five Y ⟨e⟩
      exact HasOuterChar.of_mulEquiv
        (e'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
        (hasOuterChar_psl2 ⟨5, 1, Nat.prime_five, by decide, le_rfl, hK⟩)
    · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six Y ⟨e⟩
      exact HasOuterChar.of_mulEquiv
        (e'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
        (hasOuterChar_psl2 ⟨3, 2, Nat.prime_three, by decide, by norm_num, hK⟩)
    · exact HasOuterChar.of_mulEquiv e hasOuterChar_alt7
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
    exact HasOuterChar.of_mulEquiv e
      (hasOuterChar_psl2 ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩)

theorem cfAutSmallQuotient : CFAutSmallQuotient := by
  intro H _ _ h hsmall hZ
  obtain ⟨m, ψ, hinn, hker⟩ := hasOuterChar_of_small hsmall
  refine ⟨m, ψ.comp (sAct h), ?_⟩
  ext s
  rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.comp_apply, ← mem_D_sup_P_iff_inner h hZ s]
  constructor
  · intro hψ
    obtain ⟨k, hk⟩ := isPGroup_S h s
    exact hker _ ⟨k, by rw [← map_pow, hk, map_one]⟩ hψ
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact hinn y

end CFSG.ComponentClassification.CatFactsSmall
