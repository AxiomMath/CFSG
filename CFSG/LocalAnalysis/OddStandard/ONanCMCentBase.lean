
module

public import CFSG.LocalAnalysis.OddStandard.ONanCMCard
public import Certificates.Data.ONanCMNormal

@[expose] public section

namespace CFSG.OddStandard.ONanRec

namespace CM

theorem wordPerm_append (w v : List ℕ) : wordPerm (w ++ v) = wordPerm w * wordPerm v := by
  rw [wordPerm, wordPerm, wordPerm, List.map_append, List.prod_append]

theorem letterPerm_flip (h : cmLettersOK = true) {c : ℕ} (hc : c < 12) :
    letterPerm (if c % 2 = 0 then c + 1 else c - 1) = (letterPerm c)⁻¹ := by
  obtain ⟨i, hi, hci⟩ : ∃ i < 6, c = 2 * i ∨ c = 2 * i + 1 := ⟨c / 2, by omega, by omega⟩
  rcases hci with rfl | rfl
  · have e : (if 2 * i % 2 = 0 then 2 * i + 1 else 2 * i - 1) = 2 * i + 1 := by
      split <;> omega
    rw [e, letterPerm_odd h hi]
  · have e : (if (2 * i + 1) % 2 = 0 then 2 * i + 1 + 1 else 2 * i + 1 - 1) = 2 * i := by
      split <;> omega
    rw [e, letterPerm_odd h hi, inv_inv]

theorem wordPerm_invWord (h : cmLettersOK = true) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 12) → wordPerm (invWord w) = (wordPerm w)⁻¹
  | [], _ => by simp [invWord, wordPerm]
  | c :: w, hw => by
    have h1 := wordPerm_invWord h w fun d hd => hw d (List.mem_cons_of_mem _ hd)
    have hc := hw c List.mem_cons_self
    have e : invWord (c :: w) = invWord w ++ [if c % 2 = 0 then c + 1 else c - 1] := by
      simp [invWord]
    rw [e, wordPerm_append, h1]
    simp only [wordPerm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [letterPerm_flip h hc, mul_inv_rev]

theorem invWord_lt {w : List ℕ} (hw : ∀ c ∈ w, c < 12) : ∀ c ∈ invWord w, c < 12 := by
  intro c hc
  simp only [invWord, List.mem_reverse, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have := hw d hd
  split <;> omega

end CM

end CFSG.OddStandard.ONanRec
