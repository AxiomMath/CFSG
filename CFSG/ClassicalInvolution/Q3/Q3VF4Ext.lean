module

public import CFSG.ClassicalInvolution.Q3.Q3WAut
public import CFSG.ClassicalInvolution.Q3.Q3ZAutAbs
public import CFSG.ClassicalInvolution.WeakCT.Sides

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

private theorem absImg_unip : ∀ j : Fin 4,
    (∃ t : ZMod 3, absImgP j = xp t ∨ absImgP j = xm t) ∧
      (∃ t : ZMod 3, absImgM j = xp t ∨ absImgM j = xm t) := by
  decide +kernel

theorem aut_dichotomy_unip (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) :
    ((∃ t : ZMod 3, α (xp 1) = xp t ∨ α (xp 1) = xm t) ∧
        (∃ t : ZMod 3, α (xm 1) = xp t ∨ α (xm 1) = xm t)) ∨
      (∃ k : Fin 24, gluingComplete k = false ∧
        α autXp = evalW gluingAssign (gluingA k) ∧ α autXm = evalW gluingAssign (gluingB k)) := by
  obtain ⟨k, hp, hm⟩ := aut_pair_cases α
  by_cases hk : k.val < 4
  · left
    obtain ⟨j, rfl⟩ : ∃ j : Fin 4, Fin.castLE (by norm_num) j = k :=
      ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
    rw [evalW_gluingA_castLE] at hp
    rw [evalW_gluingB_castLE] at hm
    have e1 : (xp (1 : ZMod 3) : SL(2, ZMod 3)) = autXp := rfl
    have e2 : (xm (1 : ZMod 3) : SL(2, ZMod 3)) = autXm := rfl
    rw [e1, e2, hp, hm]
    exact absImg_unip j
  · right
    exact ⟨k, decide_eq_false hk, hp, hm⟩

section Extend

private abbrev crM : SL(2, ZMod 3) ≃* SL(2, ZMod 3) := MulAut.conj rotSL

private theorem crM_symm_xp (t : ZMod 3) : crM.symm (xp t) = xm (-t) := by
  show (rotSL : SL(2, ZMod 3))⁻¹ * xp t * (rotSL : SL(2, ZMod 3)) = xm (-t)
  exact rotSL_inv_xp t

private theorem crM_symm_xm (t : ZMod 3) : crM.symm (xm t) = xp (-t) := by
  show (rotSL : SL(2, ZMod 3))⁻¹ * xm t * (rotSL : SL(2, ZMod 3)) = xp (-t)
  exact rotSL_inv_xm t

private theorem crM_symm_xp_neg (t : ZMod 3) : crM.symm (xp (-t)) = xm t :=
  (crM_symm_xp (-t)).trans (congrArg xm (neg_neg t))

private theorem crM_symm_xm_neg (t : ZMod 3) : crM.symm (xm (-t)) = xp t :=
  (crM_symm_xm (-t)).trans (congrArg xp (neg_neg t))

theorem exists_extend_unip_one (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (h₁ : ∃ t : ZMod 3, α (xp 1) = xp t ∨ α (xp 1) = xm t)
    (h₂ : ∃ t : ZMod 3, α (xm 1) = xp t ∨ α (xm 1) = xm t) :
    ∃ β : SL(3, ZMod 3) ≃* SL(3, ZMod 3),
      (∀ A, β (blk (ZMod 3) 1 A) = blk (ZMod 3) 1 (α A)) ∧
        (Bs (ZMod 3) 0).map β.toMonoidHom = Bs (ZMod 3) 0 := by
  let sw : SL(3, ZMod 3) ≃* SL(3, ZMod 3) := MulAut.conj swapSL
  let α₀ : SL(2, ZMod 3) ≃* SL(2, ZMod 3) := crM.symm.trans (α.trans crM.symm)
  have a1 : α (xm (-1)) = (α (xm 1))⁻¹ := by
    rw [← map_inv]
    exact congrArg α (xm_inv 1).symm
  have a2 : α (xp (-1)) = (α (xp 1))⁻¹ := by
    rw [← map_inv]
    exact congrArg α (xp_inv 1).symm
  have hα₀1 : ∃ t : ZMod 3, α₀ (xp 1) = xp t ∨ α₀ (xp 1) = xm t := by
    obtain ⟨s, hs | hs⟩ := h₂
    · refine ⟨s, Or.inr ?_⟩
      show crM.symm (α (crM.symm (xp 1))) = xm s
      rw [crM_symm_xp, a1, hs, xp_inv]
      exact crM_symm_xp_neg s
    · refine ⟨s, Or.inl ?_⟩
      show crM.symm (α (crM.symm (xp 1))) = xp s
      rw [crM_symm_xp, a1, hs, xm_inv]
      exact crM_symm_xm_neg s
  have hα₀2 : ∃ t : ZMod 3, α₀ (xm 1) = xp t ∨ α₀ (xm 1) = xm t := by
    obtain ⟨s, hs | hs⟩ := h₁
    · refine ⟨s, Or.inr ?_⟩
      show crM.symm (α (crM.symm (xm 1))) = xm s
      rw [crM_symm_xm, a2, hs, xp_inv]
      exact crM_symm_xp_neg s
    · refine ⟨s, Or.inl ?_⟩
      show crM.symm (α (crM.symm (xm 1))) = xp s
      rw [crM_symm_xm, a2, hs, xm_inv]
      exact crM_symm_xm_neg s
  obtain ⟨β₀, hβ0, hβ1, -⟩ := exists_extend_unip α₀ hα₀1 hα₀2
  let β₁ : SL(3, ZMod 3) ≃* SL(3, ZMod 3) := sw.trans (β₀.trans sw)
  have hblk : ∀ (u : Fin 2) (A : SL(2, ZMod 3)),
      sw (blk (ZMod 3) u A) = blk (ZMod 3) u.rev (crM A) := fun u A => swap_blk u A
  refine ⟨β₁, fun A => ?_, ?_⟩
  · change sw (β₀ (sw (blk (ZMod 3) 1 A))) = blk (ZMod 3) 1 (α A)
    rw [hblk 1 A]
    change sw (β₀ (blk (ZMod 3) 0 (crM A))) = _
    rw [show blk (ZMod 3) 0 (crM A) = blockSL (ZMod 3) 3 2 0 (by omega) (crM A) from rfl, hβ0]
    change sw (blk (ZMod 3) 0 (α₀ (crM A))) = _
    rw [hblk 0]
    have : crM (α₀ (crM A)) = α A := by
      change crM (crM.symm (α (crM.symm (crM A)))) = α A
      rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    change blk (ZMod 3) 1 (crM (α₀ (crM A))) = _
    rw [this]
  · have hmap : ∀ H : Subgroup SL(3, ZMod 3), H.map β₁.toMonoidHom =
        ((H.map sw.toMonoidHom).map β₀.toMonoidHom).map sw.toMonoidHom := by
      intro H
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    have e0 : Fin.rev (0 : Fin 2) = 1 := rfl
    have e1 : Fin.rev (1 : Fin 2) = 0 := rfl
    show (Bs (ZMod 3) 0).map β₁.toMonoidHom = Bs (ZMod 3) 0
    rw [hmap, show sw.toMonoidHom = (MulAut.conj (swapSL : SL(3, ZMod 3))).toMonoidHom from rfl,
      map_conj_swapSL_Bs 0, e0, show Bs (ZMod 3) 1 = B23 (ZMod 3) from rfl, hβ1,
      show B23 (ZMod 3) = Bs (ZMod 3) 1 from rfl, map_conj_swapSL_Bs 1, e1]

end Extend

end CFSG.ClassicalInvolution.Q3.Q3V
