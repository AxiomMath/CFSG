module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveCore
public import CFSG.CGT.Timmesfeld75.Sec3TwelveNorm

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

theorem lemma312 : Lemma312Stmt := by
  intro G _ _ _ _ T T₁ hWC hglob hiso hS a haD hN F _ _ _ e σ hσ hind
  obtain ⟨g, t, htT, ht1, hat⟩ := haD
  have haa : a * a = 1 := by
    have htt : t * t = 1 := elemAbelian_mul_self hWC.1 htT
    calc a * a = g⁻¹ * (t * t) * g := by rw [hat]; group
      _ = 1 := by rw [htt]; group
  obtain ⟨x₀, hx₀, hT₁⟩ := hS.conj
  have hT₁ne : conjSubgroup x₀ T ≠ T := by
    rw [← hT₁]
    exact hS.cfg.left_ne_right.symm
  have hLne : normIn T (conjSubgroup x₀ T) ≠ ⊥ := by
    rw [← hT₁]
    exact hS.cfg.ne
  have hI : Sec3Iso T T₁ := by
    rw [hT₁]
    exact hiso x₀ hT₁ne hLne
  obtain ⟨hN', f, hf, hpair⟩ := hS.exists_isL2Pair hI
  obtain ⟨x, hxX, ⟨D⟩⟩ := hS.exists_data312 hpair haa e σ hσ hind
  have haD' : a ∈ classD (conjSubgroup x T) := by
    refine ⟨x * g, x * t * x⁻¹, conj_mem_conjSubgroup x htT, fun h => ht1 ?_, ?_⟩
    · have h' : x⁻¹ * (x * t * x⁻¹) * x = x⁻¹ * 1 * x := by rw [h]
      simpa [mul_assoc] using h'
    · rw [hat]
      group
  obtain ⟨hT16, hF4⟩ := D.core haD' (hglob.conj x) (hiso.conj x)
  rw [card_conjSubgroup] at hT16
  exact ⟨hT16, hF4⟩

end CFSG.CGT.Timmesfeld75
