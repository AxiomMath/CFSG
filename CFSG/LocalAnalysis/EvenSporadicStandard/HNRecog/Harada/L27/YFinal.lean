module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YSwapB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NRRecog

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.HNRecog

theorem final_A5WrTwo {Y : Type} [Group Y] [Finite Y] {P F : Subgroup Y} {v : Y}
    (h : FinalData Y P F v) (hsec : SmallSections Y) : Nonempty (Y ≃* A5WrTwo) := by
  obtain ⟨T₁, T₂, hT, hF⟩ := exists_two_a5 h hsec
  have hswap : T₁.map (MulAut.conj v).toMonoidHom = T₂ := v_conj_eq h hT hF
  have hidx : (T₁ ⊔ T₁.map (MulAut.conj v).toMonoidHom).index = 2 := by
    rw [hswap]
    exact index_sup_eq_two h hT hF hswap
  obtain ⟨e⟩ := component_equiv_a5 h.free hT.comp₁ hT.card₁
  have hcommT := component_commute_of_ne hT.comp₁ hT.comp₂ hT.ne
  have hmem₂ : ∀ y ∈ T₁, v * y * v⁻¹ ∈ T₂ := by
    intro y hy
    rw [← hswap, Subgroup.mem_map]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hcomm : ∀ x ∈ T₁, ∀ y ∈ T₁, x * (v * y * v⁻¹) = v * y * v⁻¹ * x := by
    intro x hx y hy
    exact hcommT x hx (v * y * v⁻¹) (hmem₂ y hy)
  have hdisj : ∀ x ∈ T₁, ∀ y ∈ T₁, x = v * y * v⁻¹ → x = 1 := by
    intro x hx y hy hxy
    have hxbot : x ∈ T₁ ⊓ T₂ := ⟨hx, hxy ▸ hmem₂ y hy⟩
    rwa [component_inf_eq_bot h.free hT.comp₁ hT.comp₂ hT.ne, Subgroup.mem_bot] at hxbot
  exact CFSG.EvenSporadicStandard.HNRecog.Harada.nonempty_mulEquiv_a5WrTwo_of_components
    T₁ e.symm h.v_sq hcomm hdisj hidx

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
