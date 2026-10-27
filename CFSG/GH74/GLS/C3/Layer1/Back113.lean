module

public import CFSG.GH74.GLS.C3.Layer1.Back113A
public import CFSG.GH74.GLS.C3.Layer1.Back113E
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.BackLeaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

theorem card_alt_five_ne_six (e : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 6)) : False := by
  have h := Nat.card_congr e.toEquiv
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
  omega

theorem s_lemma113_of
    (h112 : S_lemma112) (ha : B_lemma113a) (hL27 : B_lemma113_L27)
    (hd : B_lemma113_d6) : S_lemma113 := by
  intro G _ _ hG x K L M T Q hh p91
  have hK7 := hL27 G hG x K L M T Q hh p91
  have hnot := ha G hG x K L M T Q hh p91 hK7
  have hterm := terminal_of hh p91 hnot
  have hKL : K = L := hh.a.terminal_eq hterm
  obtain ⟨n, hn, ⟨e⟩⟩ := kbar_alt p91 hK7
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥M →* Equiv.Perm (Fin n), ψ.ker = (CMK M K).subgroupOf M := by
    by_cases h6 : n = 6
    · subst h6
      exact hd G hG x K L M T Q hh p91 hKL ⟨e⟩
    · have hn5 : 5 ≤ n := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        omega
      refine lemma113d_ne6 (K := K) (M := M) ?_ ?_ hn5 h6 e
      · rw [hKL]; exact hh.a.L_normal.1
      · rw [hKL]; exact hh.a.L_normal.2
  refine ⟨hnot, hKL, hterm, n, hn, ⟨e⟩, ⟨ψ, hψ⟩, fun hn5 => ?_⟩
  subst hn5
  refine lemma113e hh.a hKL p91.1.1 p91.1.2 e ψ hψ (fun hQZ => ?_) hnot
  rcases h112 G hG x K L M T Q hh p91 hKL hQZ with ⟨⟨e6⟩, -⟩ | ⟨-, hRT, hS⟩
  · exact (card_alt_five_ne_six (e.symm.trans e6)).elim
  · exact ⟨hRT, hS⟩

end CFSG.GH74.GLS.C3.Layer1.Back
