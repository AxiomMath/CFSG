module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignB

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type} [Group G] [Finite G] {t r : G} {Θ : HModel →* G}

theorem v0_ne_one : v0 ≠ 1 := by decide

theorem FyConf.Phi_eq_redPi (h : FyConf t r Θ) (m : HModel) :
    h.Phi m = redPi r (h.thetaC m) := rfl

theorem FyConf.exists_delta (h : FyConf t r Θ) :
    ∃ δ : DihedralGroup 4, (δ = 1 ∨ δ = DihedralGroup.r 2) ∧
      (∃ x : RedX r, x * h.tauX * x⁻¹ = h.Phi (δ, 1, v0)) ∧
      ¬ ∃ x : RedX r, h.tauX * h.Phi (δ, 1, v0) = x * h.tauX * x⁻¹ := by
  obtain ⟨δ, hδ, ⟨g, hg⟩, hng⟩ := h.v_conj
  set T : RedC r := h.thetaC (DihedralGroup.r 2, 1, 1) with hT
  set W : RedC r := h.thetaC (δ, 1, v0) with hW
  have hT_G : (T : G) = t := h.t_eq
  have hW_G : (W : G) = Θ (δ, 1, v0) := rfl
  refine ⟨δ, hδ, ?_, ?_⟩
  · obtain ⟨g', hg'r, hg'⟩ := h.exists_conj_cent (h.comm_r (δ, 1, v0)) ⟨g, hg⟩
    set gC : RedC r := ⟨g', mem_centralizer_singleton_iff.2 hg'r⟩ with hgC
    have hWT : W = gC * T * gC⁻¹ := by
      apply Subtype.ext
      show (W : G) = g' * (T : G) * g'⁻¹
      rw [hT_G, hW_G]; exact hg'
    refine ⟨redPi r gC, ?_⟩
    rw [h.Phi_eq_redPi, ← hW, hWT, map_mul, map_mul, map_inv]
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hTW : T * W = h.thetaC ((DihedralGroup.r 2, 1, 1) * (δ, 1, v0)) := by
      rw [map_mul]
    have hbb : (T * W) * (T * W) = 1 := by
      rw [hTW, ← map_mul]
      have : ((DihedralGroup.r 2 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
          (δ, 1, v0) * ((DihedralGroup.r 2, 1, 1) * (δ, 1, v0)) = 1 := by
        rcases hδ with rfl | rfl <;> decide
      rw [this, map_one]
    have hTT : T * T = 1 := by
      rw [hT, ← map_mul]
      have : ((DihedralGroup.r 2 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
          (DihedralGroup.r 2, 1, 1) = 1 := by decide
      rw [this, map_one]
    have haa : (y * T * y⁻¹) * (y * T * y⁻¹) = 1 := by
      calc (y * T * y⁻¹) * (y * T * y⁻¹) = y * (T * T) * y⁻¹ := by group
        _ = 1 := by rw [hTT]; group
    have hab : (y * T * y⁻¹)⁻¹ * (T * W) ∈ RedO r := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 : (QuotientGroup.mk (T * W) : RedX r) = QuotientGroup.mk (y * T * y⁻¹) := by
        have : (QuotientGroup.mk (T * W) : RedX r) = h.tauX * h.Phi (δ, 1, v0) := rfl
        rw [this, hx]
        rfl
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 ⊢
      rw [h1]; group
    obtain ⟨m, hmO, hm⟩ := exists_conj_of_odd (O := RedO r) (redO_odd r) haa hbb hab
    apply hng
    refine ⟨((m * y : RedC r) : G), ?_⟩
    have h2 := congrArg Subtype.val hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [hT_G] at h2
    show t * Θ (δ, 1, v0) = ((m * y : RedC r) : G) * t * ((m * y : RedC r) : G)⁻¹
    simp only [Subgroup.coe_mul]
    calc t * Θ (δ, 1, v0) = t * (W : G) := rfl
      _ = (m : G) * ((y : G) * t * (y : G)⁻¹) * (m : G)⁻¹ := h2.symm
      _ = (m : G) * (y : G) * t * ((m : G) * (y : G))⁻¹ := by group

end CFSG.EvenSporadicStandard.TwoHS
