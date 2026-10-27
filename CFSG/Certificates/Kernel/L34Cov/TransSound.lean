module

public import Certificates.Data.Kernel.L34Cov.Trans
public import CFSG.Certificates.Kernel.L34W.Tab42Sound

public section

namespace CFSG.KC.L34Cov

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.PSL3Four.Native CFSG.KC.L34W CFSG.KC.Enum
open CFSG.KS

variable {T : ℕ}

theorem lt_of_lookC_ne {k l : ℕ} (h : lookC T k l ≠ 0) : k < 64 ∧ l < 64 := by
  unfold lookC at h
  split_ifs at h with hkl
  · exact hkl
  · exact absurd rfl h

theorem commBit_of_cbK (h1 : cOK1 T = true) (h2 : cOK2 T = true) {κ k l : ℕ} {f : Bool}
    (h : cbK T κ k l f = true) : commBit κ k l f = true := by
  unfold cbK at h
  rw [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at h
  obtain ⟨hne, hf⟩ := h
  obtain ⟨hk, hl⟩ := lt_of_lookC_ne hne
  have h2' := List.all_eq_true.1 (List.all_eq_true.1 h2 k (List.mem_range.2 hk)) l
    (List.mem_range.2 hl)
  rw [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h2'
  rcases h2' with h0 | ⟨d, hd, hkey⟩
  · exact absurd h0 hne
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hkey
  obtain ⟨rfl, rfl⟩ := hkey
  have h1' := List.all_eq_true.1 h1 d hd
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h1'
  obtain ⟨⟨hp, hq⟩, hc⟩ := h1'
  rw [hc, cEnc] at hf
  unfold commBit
  rw [List.any_eq_true]
  refine ⟨d, hd, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, true_and]
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq] at hf ⊢ <;> exact hf

theorem transOK_of_transK (h1 : cOK1 T = true) (h2 : cOK2 T = true) (h : transK T = true) :
    transOK = true := by
  unfold transK at h
  unfold transOK
  simp only [List.all_eq_true, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  intro κ hκ I hI k₁ hk₁ k₂ hk₂
  rcases h κ hκ I hI k₁ hk₁ k₂ hk₂ with h0 | h
  · exact Or.inl h0
  · refine Or.inr fun f₁ hf₁ f₂ hf₂ => ?_
    obtain ⟨w, hw, a, b⟩ := h f₁ hf₁ f₂ hf₂
    exact ⟨w, hw, commBit_of_cbK h1 h2 a, commBit_of_cbK h1 h2 b⟩

theorem cceOK_of_cceK {G : ℕ → ℕ} (hG : GensG G) (h1 : cOK1 T = true) (h2 : cOK2 T = true)
    (h : cceK T G = true) : cceOK = true := by
  unfold cceK at h
  unfold cceOK
  rw [List.all_eq_true] at h ⊢
  intro d hd
  have hd' := h d hd
  simp only [Bool.and_eq_true] at hd' ⊢
  obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := hd'
  refine ⟨⟨⟨commBit_of_cbK h1 h2 a, commBit_of_cbK h1 h2 b⟩, c⟩, ?_⟩
  obtain ⟨hc, e1⟩ := tgK_eq hG d.2.1
  obtain ⟨-, e2⟩ := tgK_eq hG d.2.2
  rw [e1, e2, CFSG.KC.L34KSnd.comp_unpack' hc hc, beq_iff_eq.1 e]
  exact beq_self_eq_true _

end CFSG.KC.L34Cov

end
