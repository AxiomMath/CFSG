module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding
open scoped commutatorElement

theorem parabCommOn_idxB_of
    (hGA : CFSG.Open.GriessAllModelsStatement) : ParabCommOn (IsLieOf IdxB) := by
  intro A _ _ Y P p hp hp2 hY h2 hF hpar hne hna
  left
  obtain ⟨r, K, _, _, _, hr, ⟨φ⟩⟩ := Sp.exists_mulEquiv_statedSp_of_isQuasisimple_idxB hGA hY h2 hF
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := Sp.exists_flagStabilizer_of_isParabolicTwo hpar hne φ
  let C : Sp.SpCover Y P r K I := ⟨ρ, hρ⟩
  have hPY : P ≤ Y := hpar.1
  have hbig := Sp.SpCover.exists_big_block C hI htI hmax hPY hna
  have hodd : Odd p := hp.odd_of_ne_two hp2
  intro b₁ b₂ hp₁ hp₂ hp₁₂ hY₁ hY₂ hP₁ hP₂ hW₁ hW₂ y hy
  obtain ⟨k₁, hk₁⟩ := hp₁
  obtain ⟨k₂, hk₂⟩ := hp₂
  obtain ⟨k₁₂, hk₁₂⟩ := hp₁₂
  let N₁ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₁, hY₁⟩
  let N₂ : ↥(Subgroup.normalizer (Y : Set A)) := ⟨b₂, hY₂⟩
  have hcomm : ⁅b₁, b₂⁆ ∈ Subgroup.normalizer (Y : Set A) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hY₁ hY₂) (inv_mem hY₁)) (inv_mem hY₂)
  let Nc : ↥(Subgroup.normalizer (Y : Set A)) := ⟨⁅b₁, b₂⁆, hcomm⟩
  have hNc : Nc = ⁅N₁, N₂⁆ := rfl
  have hα : C.autHom Nc = ⁅C.autHom N₁, C.autHom N₂⁆ := by
    rw [hNc, map_commutatorElement]
  have hmodel : ⁅C.autHom N₁, C.autHom N₂⁆ = 1 :=
    Sp.sp_model_comm hr hI htI hmax hbig (C.odd_orderOf_autHom N₁ hodd hk₁)
      (C.odd_orderOf_autHom N₂ hodd hk₂) (hα ▸ C.odd_orderOf_autHom Nc hodd hk₁₂)
      (C.spNormFix_autHom hI htI hmax hPY N₁ hP₁ hW₁)
      (C.spNormFix_autHom hI htI hmax hPY N₂ hP₂ hW₂)
  exact C.centralizes_of_autHom_eq_one Nc (hα.trans hmodel) y hy

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
