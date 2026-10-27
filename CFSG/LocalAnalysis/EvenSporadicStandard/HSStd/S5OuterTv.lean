module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Section
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutLift

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem HSOuterSetup.t_mem_S (h : HSOuterSetup G L t S z n v s) : t ∈ S := by
  have ht2 : t * t = 1 := by rw [← pow_two]; exact h.t_two ▸ pow_orderOf_eq_one t
  exact mem_of_central_two h.ctx.fusion.le h.ctx.fusion.pgroup h.ctx.fusion.index
    (mem_centralizer_singleton_iff.2 rfl) ht2 (fun c hc => mem_centralizer_singleton_iff.1 hc)

theorem HSOuterSetup.t_sq (h : HSOuterSetup G L t S z n v s) : t * t = 1 := by
  rw [← pow_two]
  exact h.t_two ▸ pow_orderOf_eq_one t

theorem HSOuterSetup.centralizer_mul_inf (h : HSOuterSetup G L t S z n v s) :
    centralizer ({t * v} : Set G) ⊓ L = centralizer ({v} : Set G) ⊓ L := by
  have hcl : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 h.t_mem l hl
  ext l
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h1' : t * (l * v) = t * (v * l) := by
      calc t * (l * v) = (l * t) * v := by rw [hcl l h2, mul_assoc]
        _ = l * (t * v) := by rw [mul_assoc]
        _ = (t * v) * l := h1
        _ = t * (v * l) := by rw [mul_assoc]
    exact mul_left_cancel h1'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc l * (t * v) = (l * t) * v := by rw [mul_assoc]
      _ = t * (l * v) := by rw [hcl l h2, mul_assoc]
      _ = t * (v * l) := by rw [h1]
      _ = (t * v) * l := by rw [mul_assoc]

theorem HSOuterSetup.ctx_mul (h : HSOuterSetup G L t S z n v s) :
    HSOuterCtx L t S z n (t * v) s where
  fusion := h.ctx.fusion
  v_mem := S.mul_mem h.t_mem_S h.ctx.v_mem
  v_outer := by
    intro hm
    apply h.ctx.v_outer
    have : v = t * (t * v) := by rw [← mul_assoc, h.t_sq, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_right (mem_zpowers t)) hm
  v_sq := by
    have hvt : t * v = v * t := h.t_comm_v
    calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [← hvt]
      _ = (t * t) * (v * v) := by group
      _ = 1 := by rw [h.t_sq, h.ctx.v_sq, one_mul]
  v_cls := by
    obtain ⟨e⟩ := h.ctx.v_cls
    exact ⟨(MulEquiv.subgroupCongr h.centralizer_mul_inf).trans e⟩
  s_mem := h.ctx.s_mem
  s_conj := by
    have hst : s * t = t * s :=
      mem_centralizer_singleton_iff.1 (h.ctx.fusion.le h.ctx.s_mem)
    calc s * (t * v) * s⁻¹ = (s * t * s⁻¹) * (s * v * s⁻¹) := by group
      _ = t * (v * z) := by rw [hst, mul_inv_cancel_right, h.ctx.s_conj]
      _ = (t * v) * z := by rw [mul_assoc]

theorem HSOuterSetup.mul_t (h : HSOuterSetup G L t S z n v s)
    (hnn : ¬ ((derivedCentralizerIn L (t * v)).subgroupOf
      (centralizer ({t * v} : Set G))).Normal) : HSOuterSetup G L t S z n (t * v) s :=
  ⟨h.setting, h.t_mem, h.t_two, h.index, h.ctx_mul, hnn⟩

end CFSG.EvenSporadicStandard.HSStd
