module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf3A
public import CFSG.ClassicalInvolution.Asc77.AscT7FA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {t u₁ u₂ u₃ : G}

theorem alpha_eq_of_star {u t v : G} (hB : Hyp51 (Subgroup.closure ({u, t, v} : Set G)))
    (hu2 : u * u = 1) (ht2 : t * t = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (ht1 : t ≠ 1)
    (hv1 : v ≠ 1) (hut : u ≠ t) (hvu : v ≠ u) (cut : u * t = t * u) (cuv : u * v = v * u) :
    alphaOf (Subgroup.closure ({u, u * v} : Set G)) = alphaOf (Subgroup.closure ({u, t} : Set G)) := by
  have hA₀ : IsElemAbelian2 (Subgroup.closure ({u, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hu2 ht2 hu1 ht1 hut cut
  have huv2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = (u * u) * (v * v) := by
          rw [mul_assoc, ← mul_assoc v, ← cuv]; group
      _ = 1 := by rw [hu2, hv2]; group
  have huv1 : u * v ≠ 1 := by
    intro h
    apply hvu
    have := eq_inv_of_mul_eq_one_right h
    have hu : u⁻¹ = u := by
      have : u * u = 1 := hu2
      exact inv_eq_of_mul_eq_one_right this
    rw [this, hu]
  have hne : u ≠ u * v := by
    intro h
    apply hv1
    have : u * v = u * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have hcm : u * (u * v) = (u * v) * u := by
    calc u * (u * v) = u * (v * u) := by rw [cuv]
      _ = (u * v) * u := by group
  have hA : IsElemAbelian2 (Subgroup.closure ({u, u * v} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hu2 huv2 hu1 huv1 hne hcm
  have hA₀B : Subgroup.closure ({u, t} : Set G) ≤ Subgroup.closure ({u, t, v} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hAB : Subgroup.closure ({u, u * v} : Set G) ≤ Subgroup.closure ({u, t, v} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  exact (lemma54_odd_and_eq hB hA₀B hA₀).2 _ hAB hA

theorem rLayer_le_normalizer_alpha_of_gen (hd : A7T22.Hyp22G Ω K K' K₃ t u₁ u₂ u₃) {t' : G}
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, t'} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set G)))
    (hgen : rLayer Ω (u₁ * u₂) ≤
      ((rLayer Ω (u₁ * u₂) ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
        (rLayer Ω (u₁ * u₂) ⊓ Subgroup.centralizer ({t'} : Set G))) ⊔
        oddCoreOf (rLayer Ω (u₁ * u₂))) :
    rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set G)) : Set G) := by
  have hΩ : HypOmegaGen Ω := hd.hyp
  set u := u₁ * u₂ with hu
  have hC : ∀ x ∈ rLayer Ω u, u * x = x * u := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (Asc77.rLayer_le_centralizer Ω u hx)).symm
  refine hgen.trans (sup_le (sup_le ?_ ?_) ?_)
  · intro x ⟨hxL, hxt⟩
    apply mem_normalizer_of_conjSub_eq
    have hxu : x * u * x⁻¹ = u := by
      calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [← hC x hxL]
        _ = u := by group
    have hxt' : x * t * x⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hxt
      calc x * t * x⁻¹ = (t * x) * x⁻¹ := by rw [this]
        _ = t := by group
    rw [← alphaOf_conjSub, T7A.conjSub_closure_pair, hxu, hxt']
  · intro x ⟨hxL, hxt⟩
    apply mem_normalizer_of_conjSub_eq
    have hxu : x * u * x⁻¹ = u := by
      calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [← hC x hxL]
        _ = u := by group
    have hxt' : x * t' * x⁻¹ = t' := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hxt
      calc x * t' * x⁻¹ = (t' * x) * x⁻¹ := by rw [this]
        _ = t' := by group
    rw [← hα, ← alphaOf_conjSub, T7A.conjSub_closure_pair, hxu, hxt']
  · have hOle : oddCoreOf (rLayer Ω u) ≤ oddCoreOf (Subgroup.centralizer ({u} : Set G)) :=
      TwinDisc.oddCoreOf_le_of_normalizes (Asc77.rLayer_le_centralizer Ω u)
        (fun g hg => TwinMu.Pf3.conjSub_rLayer hΩ hg)
    have hcz : u * t = t * u := by
      have h1 : Commute t u₁ := hd.comm_z₁
      have h2 : Commute t u₂ := hd.comm_z₂
      exact ((h1.symm).mul_left (h2.symm)).eq
    exact hOle.trans (oddCoreOf_centralizer_le_normalizer_alphaOf hd.hz.sq hd.mul_ne_one hcz)

end Gen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
