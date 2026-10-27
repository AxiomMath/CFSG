module

public import CFSG.GH74.Generic.S1.KL5
public import CFSG.GH74.Generic.S1.KL5Classical
public import CFSG.GH74.Generic.S1.KL5Shape
public import CFSG.GH74.Generic.S1.KL5LyRee
public import CFSG.GH74.Generic.S1.KL5Arith

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

namespace CFSG.GH74.Generic.S1

theorem kl5_ne_two_of_pow_mod_four {p' f' : ℕ} (hf' : 1 ≤ f')
    (h : p' ^ f' % 4 = 3 ∨ p' ^ f' % 4 = 1) : p' ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
  rw [pow_succ] at h
  omega

theorem kl5Table_of_griess (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL5Table := by
  classical
  intro S _ _ _ _ hGH A B hcomm hAq hBq ε p f hp hp2 h5 hAmodel hBmodel
  have hAmod : StatedClassicalModel (↥A ⧸ center ↥A) .PSL 3 p f ∨
      StatedClassicalModel (↥A ⧸ center ↥A) .PSU 3 p f := by
    rcases hAmodel with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have cfg : KL5Cfg A B p f := ⟨hcomm, hAq, hBq, hp, hp2, h5, hAmod, hBmodel⟩
  obtain ⟨b, hbB, hb2, hb1⟩ := kl5_exists_involution_B cfg
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hAb : ∀ a ∈ A, a * b = b * a := fun a ha => hcomm a ha b hbB
  rcases hGH with ⟨n, hn7, hn11, ⟨e⟩⟩ | hspor | ⟨p', f', hp', hf', hrest⟩
  · exact (kl5_false_alt hn7 hn11 e cfg).elim
  · rcases hspor with h | h | h | h | h | h | h | h | h
    all_goals first
      | exact (kl5_false_sporadic (by tauto) cfg).elim
      | exact (kl5_false_ly h hbo hAb hp hp2 h5 (kl5_cube_dvd_card_A cfg)).elim
  · rcases hrest with ⟨hp2', hL⟩ | ⟨hp2', -, hL⟩ | ⟨hp2', -, hL⟩ | ⟨h4, hL⟩ | ⟨h4, hL⟩ | hRee |
      ⟨-, hsmall⟩
    · exfalso
      rcases hL with hL | hL | hL | hL | hL | hL
      · exact kl5_false_of_classical hGA hp2' (statedClassicalModel_of_lieModel (by norm_num) hL)
          (Or.inl ⟨rfl, by norm_num⟩) hcomm hAq hBq hp2 hAmod
      · exact kl5_false_of_classical hGA hp2' (statedClassicalModel_of_lieModel (by norm_num) hL)
          (Or.inl ⟨rfl, by norm_num⟩) hcomm hAq hBq hp2 hAmod
      · exact kl5_false_of_classical hGA hp2' (statedClassicalModel_of_lieModel (by norm_num) hL)
          (Or.inr (Or.inl ⟨rfl, by norm_num⟩)) hcomm hAq hBq hp2 hAmod
      · exact kl5_false_of_classical hGA hp2' (statedClassicalModel_of_lieModel (by norm_num) hL)
          (Or.inr (Or.inr ⟨rfl, by norm_num⟩)) hcomm hAq hBq hp2 hAmod
      · exact kl5_false_G2 hGA hp' hp2' hL hbo hAb hAq hp2 hAmod
      · exact kl5_false_D4 hGA hp' hp2' hL hbo hAb hAq hp2 hAmod
    · exfalso
      exact kl5_false_of_classical hGA hp2' (statedClassicalModel_of_lieModel (by norm_num) hL)
        (Or.inl ⟨rfl, by norm_num⟩) hcomm hAq hBq hp2 hAmod
    · exfalso
      exact kl5_false_of_classical hGA hp2' (statedClassicalModel_of_lieModel (by norm_num) hL)
        (Or.inr (Or.inl ⟨rfl, by norm_num⟩)) hcomm hAq hBq hp2 hAmod
    · exact ⟨p', f', hp', hf', kl5_ne_two_of_pow_mod_four hf' (Or.inl h4),
        Or.inl ⟨h4, statedClassicalModel_of_lieModel (by norm_num) hL⟩⟩
    · exact ⟨p', f', hp', hf', kl5_ne_two_of_pow_mod_four hf' (Or.inr h4),
        Or.inr ⟨h4, statedClassicalModel_of_lieModel (by norm_num) hL⟩⟩
    · exfalso
      exact kl5_false_ree hRee
        ((kl5_sixteen_dvd_card_A cfg).trans (Subgroup.card_subgroup_dvd_card A))
    · exact (kl5_false_small hsmall cfg).elim

end CFSG.GH74.Generic.S1
