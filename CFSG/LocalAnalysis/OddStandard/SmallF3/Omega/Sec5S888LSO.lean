module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_z_not_conj_mixed (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h514 : Asc82Lemma514) (h52a : Asc82Lemma52a) (hM1 : Asc82FactRhoStar)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {i i' j j' : Fin 4}
    (hi : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0)) (hj : (j = 2 ∧ j' = 3) ∨ (j = 3 ∧ j' = 2))
    {α β : G} (hα : α ∈ Kfam5 K₁ K₂ h i) (hβ : β ∈ Kfam5 K₁ K₂ h j) (hα2 : α * α = z)
    (hβ2 : β * β = z) (w : G) : w⁻¹ * z * w ≠ α * β := by
  intro hw
  obtain ⟨g, hgt, hgs, hgz, hgK, hβt, hαs⟩ := l515S_adapt h37 h514 c hi hj hα hβ hα2 hβ2
  obtain ⟨c₁, hcj1, hcj2⟩ := l515S_ctx_fix c hgz hgK
  have hKeq : Kfam5 K₁ K₂ (g⁻¹ * h * g) = Kfam5 K₁ K₂ h := l515S_kfam_eq hcj1 hcj2
  have hα₁ : α ∈ Kfam5 K₁ K₂ (g⁻¹ * h * g) i := by rw [hKeq]; exact hα
  have hβ₁ : β ∈ Kfam5 K₁ K₂ (g⁻¹ * h * g) j := by rw [hKeq]; exact hβ
  have hs₁ : (g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g) = g⁻¹ * (h⁻¹ * t * h) * g := by
    group
  have hds₁ : (α * β) * ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) =
      ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) * (α * β) := by
    rw [hs₁]
    exact hgs.symm
  have hαs₁ : α * ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) =
      ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) * α := by
    rw [hs₁]
    exact hαs
  obtain ⟨I, -, -, -, -, -, hM₁, -, -, -⟩ :=
    l515S_reduced h36 h37 h514 h52a hM1 c₁ hi hj hα₁ hβ₁ hα2 hβ2 hgt.symm hds₁ hβt hαs₁
  have hcent : w⁻¹ * z * w ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [hw, Subgroup.mem_centralizer_singleton_iff]
    exact hgt.symm
  have h37' := h37 G (g⁻¹ * t * g) (CFSG.conjugate L g) c₁.toSec5Setting.toSec3SettingLB z w
    c₁.pocket hcent
  rw [hw] at h37'
  have hbot : layerCent (CFSG.conjugate L g) (α * β) = ⊥ := h37'
  have hcard := l515S_card_u33 hM₁
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
