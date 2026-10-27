module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NJ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ND
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SU2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

private theorem E8_le_normalizer_W :
    closure ({t, tau, lam} : Set G) ≤
      Subgroup.normalizer ((ctxWN t tau x₁ x₂ rho : Subgroup G) : Set G) :=
  fun c hc => Subgroup.mem_normalizer_fintype fun w hw => hz.E8_normalizes_W c hc w hw

theorem W_le_ctxVN : ctxWN t tau x₁ x₂ rho ≤ ctxVN t tau x₁ x₂ lam rho := le_sup_left

theorem E8_le_ctxVN : closure ({t, tau, lam} : Set G) ≤ ctxVN t tau x₁ x₂ lam rho := le_sup_right

theorem E0_le_ctxVN : ctxE0N t tau x₁ x₂ rho ≤ ctxVN t tau x₁ x₂ lam rho := by
  unfold ctxE0N ctxVN
  refine sup_le le_sup_left ?_
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

theorem isPGroup_ctxVN : IsPGroup 2 (ctxVN t tau x₁ x₂ lam rho) := by
  unfold ctxVN
  have hW : IsPGroup 2 (ctxWN t tau x₁ x₂ rho) := hz.isPGroup_ctxWN
  have hE : IsPGroup 2 (closure ({t, tau, lam} : Set G)) :=
    IsPGroup.of_card (p := 2) (n := 3) (by rw [hz.card_E8]; norm_num)
  exact IsPGroup.to_sup_of_normal_left' hW hE (E8_le_normalizer_W hz)

theorem U_le_ctxVN : ctxU t tau x₁ x₂ lam ≤ ctxVN t tau x₁ x₂ lam rho := by
  unfold ctxU ctxVN
  rw [hz.O_eq_Q]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact hz.Q_le_ctxWN.trans le_sup_left
  · refine (Subgroup.closure_mono ?_).trans le_sup_right
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))).trans le_sup_right

theorem S_le_ctxVN : S ≤ ctxVN t tau x₁ x₂ lam rho := hz.S_le_U.trans hz.U_le_ctxVN

theorem Y_E16 : IsE16In (ctxVN t tau x₁ x₂ lam rho) (ctxYq t tau x₁ x₂ rho) :=
  ⟨hz.Y_le_ctxWN.trans le_sup_left, hz.Y_isElemAbelian, hz.card_Y⟩

theorem Y_normal_ctxVN : NormalIn (ctxYq t tau x₁ x₂ rho) (ctxVN t tau x₁ x₂ lam rho) := by
  refine ⟨hz.Y_le_ctxWN.trans le_sup_left, ?_⟩
  intro g hg k hk
  obtain ⟨w, hw, e, he, rfl⟩ :=
    (S4B.mem_sup_iff_of_normalizes (H := ctxWN t tau x₁ x₂ rho)
      (K := closure ({t, tau, lam} : Set G)) hz.E8_normalizes_W).mp hg
  have hek : e * k * e⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    hz.normal_Y.2 e (hz.nGood.E_le_M he) k hk
  have hwfix : w * (e * k * e⁻¹) * w⁻¹ = e * k * e⁻¹ := by
    have hcomm := ctxCQ_comm (ctxWN_le_ctxCQ t tau x₁ x₂ rho hw) (hz.Y_le_Q hek)
    rw [hcomm]
    group
  rw [show (w * e) * k * (w * e)⁻¹ = w * (e * k * e⁻¹) * w⁻¹ from by group, hwfix]
  exact hek

theorem cent_Y_ctxVN :
    ctxVN t tau x₁ x₂ lam rho ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxE0N t tau x₁ x₂ rho := by
  apply le_antisymm
  · rintro x ⟨hxV, hxY⟩
    obtain ⟨w, hw, e, he, rfl⟩ :=
      (S4B.mem_sup_iff_of_normalizes (H := ctxWN t tau x₁ x₂ rho)
        (K := closure ({t, tau, lam} : Set G)) hz.E8_normalizes_W).mp hxV
    have hwcent : w ∈ Subgroup.centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (ctxCQ_comm (ctxWN_le_ctxCQ t tau x₁ x₂ rho hw) (hz.Y_le_Q ha)).symm
    have hecent : e ∈ Subgroup.centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hwcent) hxY
      rwa [show w⁻¹ * (w * e) = e from by group] at h
    exact Subgroup.mul_mem_sup hw (hz.E8_cent_Y e he fun a ha =>
      (Subgroup.mem_centralizer_iff.mp hecent a ha).symm)
  · intro e he
    exact ⟨hz.E0_le_ctxVN he, Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (hz.E0_le_cent_Y e he a ha).symm⟩

theorem vn_cosets : ∀ x ∈ ctxVN t tau x₁ x₂ lam rho,
    x ∈ ctxE0N t tau x₁ x₂ rho ∨ t⁻¹ * x ∈ ctxE0N t tau x₁ x₂ rho ∨
      lam⁻¹ * x ∈ ctxE0N t tau x₁ x₂ rho ∨ (t * lam)⁻¹ * x ∈ ctxE0N t tau x₁ x₂ rho := by
  intro x hx
  obtain ⟨w, hw, e, he, rfl⟩ :=
    (S4B.mem_sup_iff_of_normalizes (H := ctxWN t tau x₁ x₂ rho)
      (K := closure ({t, tau, lam} : Set G)) hz.E8_normalizes_W).mp hx
  rcases hz.E8_cosets e he with h | h | h | h
  · exact Or.inl (Subgroup.mul_mem_sup hw h)
  · refine Or.inr (Or.inl ?_)
    rw [show t⁻¹ * (w * e) = (t⁻¹ * w * t) * (t⁻¹ * e) from by group]
    refine Subgroup.mul_mem_sup ?_ h
    have hc : t⁻¹ ∈ closure ({t, tau, lam} : Set G) :=
      Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    simpa using hz.E8_normalizes_W t⁻¹ hc w hw
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [show lam⁻¹ * (w * e) = (lam⁻¹ * w * lam) * (lam⁻¹ * e) from by group]
    refine Subgroup.mul_mem_sup ?_ h
    have hc : lam⁻¹ ∈ closure ({t, tau, lam} : Set G) :=
      Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    simpa using hz.E8_normalizes_W lam⁻¹ hc w hw
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [show (t * lam)⁻¹ * (w * e) = ((t * lam)⁻¹ * w * (t * lam)) * ((t * lam)⁻¹ * e)
      from by group]
    refine Subgroup.mul_mem_sup ?_ h
    have hc : (t * lam)⁻¹ ∈ closure ({t, tau, lam} : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    simpa using hz.E8_normalizes_W (t * lam)⁻¹ hc w hw

end Ctx4Z

namespace ZNW

variable (hw : ZNW t L S x₁ x₂ lam rho tau)
include hw

theorem card_ctxVN : Nat.card ↥(ctxVN t tau x₁ x₂ lam rho) = 2 ^ 11 := by
  unfold ctxVN
  rw [S4B.card_sup_eq_mul (H := ctxWN t tau x₁ x₂ rho)
      (K := closure ({t, tau, lam} : Set G)) hw.toCtx4Z.E8_normalizes_W hw.toCtx4Z.inf_E8_W,
    hw.card_ctxWN, hw.toCtx4Z.card_E8]
  norm_num

end ZNW

end CFSG.OddStandard.SmallF3.HarrisU33
