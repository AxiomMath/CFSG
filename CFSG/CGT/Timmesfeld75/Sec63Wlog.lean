module

public import CFSG.CGT.Timmesfeld75.Fusion
public import CFSG.CGT.Timmesfeld75.Sec63Basic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ T₃ : Subgroup G} {n m : ℕ} {x : G}

theorem hSub_conjSubgroup {L₁ : Subgroup G} {k : G} (hk : k ∈ Subgroup.normalizer (T : Set G)) :
    hSub T (conjSubgroup k L₁) = hSub T L₁ := by
  refine le_antisymm (sup_le le_sup_left (iSup₂_le fun g hg => ?_))
    (sup_le le_sup_left (iSup₂_le fun g hg => ?_))
  · rw [conjSubgroup_conjSubgroup]
    exact le_sup_of_le_right (le_iSup₂_of_le (g * k)
      ((Subgroup.normalizer (T : Set G)).mul_mem hg hk) le_rfl)
  · have e : conjSubgroup g L₁ = conjSubgroup (g * k⁻¹) (conjSubgroup k L₁) := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    rw [e]
    exact le_sup_of_le_right (le_iSup₂_of_le (g * k⁻¹)
      ((Subgroup.normalizer (T : Set G)).mul_mem hg
        ((Subgroup.normalizer (T : Set G)).inv_mem hk)) le_rfl)

theorem Sec6Ctx.conj_normalizer (hc : Sec6Ctx T T₁ n m) {k : G}
    (hk : k ∈ Subgroup.normalizer (T : Set G)) : Sec6Ctx T (conjSubgroup k T₁) n m := by
  have hL : normIn T (conjSubgroup k T₁) = conjSubgroup k (normIn T T₁) :=
    normIn_conjSubgroup_of_mem_normalizer hk T₁
  have hL₁ : normIn (conjSubgroup k T₁) T = conjSubgroup k (normIn T₁ T) := by
    have := normIn_conj k T₁ T
    rwa [mem_normalizer_iff_conjSubgroup_eq.1 hk] at this
  refine ⟨hc.hy.conj_normalizer hk, hc.hS, hc.hI, ?_, hc.hT, ?_⟩
  · rw [hL, card_conjSubgroup]
    exact hc.hq
  · have hcase := hc.hcase
    unfold Sec6Case at hcase ⊢
    rw [hL₁, hSub_conjSubgroup hk]
    exact hcase

theorem Sec63Cfg.conj_normalizer (c : Sec63Cfg T T₁ n m x T₃) {k : G}
    (hk : k ∈ Subgroup.normalizer (T : Set G)) : Sec63Cfg T (conjSubgroup k T₁) n m x T₃ where
  ctx := c.ctx.conj_normalizer hk
  big := c.big
  hx := c.hx
  hxT := c.hxT
  small := by
    rw [normIn_conjSubgroup_of_mem_normalizer hk T₁, card_conjSubgroup]
    exact c.small
  conj := c.conj
  mem := c.mem

theorem Sec63Cfg.exists_conj_pGroup_sup (c : Sec63Cfg T T₁ n m x T₃) :
    ∃ k ∈ Subgroup.normalizer (T : Set G),
      IsPGroup 2 ↥(normIn T₃ T ⊔ normIn (conjSubgroup k T₁) T) := by
  have := c.ctx.finite
  have hP := c.ctx.hy.pair
  obtain ⟨g, hg⟩ := c.conj
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have hA : IsPGroup 2 (normIn T₃ T) := by
    have : IsElemAbelian 2 T₃ := hg ▸ isElemAbelian_conjSubgroup hP.wc.1 g
    exact (isPGroup_two_of_isElemAbelian this).to_le (normIn_le _ _)
  have hB : IsPGroup 2 (normIn T₁ T) := by
    have : IsElemAbelian 2 T₁ := hx₀ ▸ isElemAbelian_conjSubgroup hP.wc.1 x₀
    exact (isPGroup_two_of_isElemAbelian this).to_le (normIn_le _ _)
  obtain ⟨U, hU, -, hAU, k, hk, hkU⟩ := exists_pGroup_containing_conjSubgroup
    (C := Subgroup.normalizer (T : Set G)) hA hB inf_le_right inf_le_right
  refine ⟨k, hk, hU.to_le (sup_le hAU ?_)⟩
  have := normIn_conj k T₁ T
  rw [mem_normalizer_iff_conjSubgroup_eq.1 hk] at this
  rw [this]
  exact hkU

end CFSG.CGT.Timmesfeld75
