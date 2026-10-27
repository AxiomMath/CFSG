module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

section

variable {G : Type} [Group G]

theorem Distinct5.map {u a b : G} (h : Distinct5 u a b) (f : G →* G)
    (hf : Function.Injective f) : Distinct5 (f u) (f a) (f b) := by
  obtain ⟨hc, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h
  refine ⟨by rw [← map_mul, ← map_mul, hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_one f]; exact hf.ne h₁
  · rw [← map_pow, ← map_one f]; exact hf.ne h₂
  · rw [← map_pow, ← map_one f]; exact hf.ne h₃
  · rw [← map_pow, ← map_pow, ← map_mul, ← map_one f]; exact hf.ne h₄
  · rw [← map_pow]; exact hf.ne h₅
  · rw [← map_pow]; exact hf.ne h₆
  · rw [← map_pow, ← map_pow, ← map_mul]; exact hf.ne h₇
  · rw [← map_pow, ← map_pow]; exact hf.ne h₈
  · rw [← map_pow, ← map_pow, ← map_mul]; exact hf.ne h₉
  · rw [← map_pow, ← map_pow, ← map_mul]; exact hf.ne h₁₀

theorem Distinct5.conj {u a b : G} (h : Distinct5 u a b) (g : G) :
    Distinct5 (g * u * g⁻¹) (g * a * g⁻¹) (g * b * g⁻¹) := by
  simpa [MulAut.conj_apply] using h.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective


end

theorem fzNoPointedEmbedZ3_of (h6 : FzPairAtR) (h7 : FzNoPairAtZ3) : FzNoPointedEmbedZ3 := by
  intro G _ _ t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ hs ht h1 h2 h12 i hi hi2 hiZ g hg hT
  obtain ⟨a, ha, b, hb, hai, hbi, hd⟩ :=
    h6 G t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ hs ht h1 h2 h12 i hi hi2 hiZ
  have := hd.conj g
  rw [hg] at this
  exact h7 G t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ hs ht h1 h2 h12 _ (hT a ha hai) _ (hT b hb hbi) this
end CFSG.OddStandard.SmallF3.FritzII
