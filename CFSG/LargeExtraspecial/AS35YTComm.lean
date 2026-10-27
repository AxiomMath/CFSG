module

public import CFSG.LargeExtraspecial.AS35YTSymp
public import CFSG.LargeExtraspecial.A2ModBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem actHat_fix_YT (hc : center S.LbarAsc = ⊥) {v : S.Qt} (hv : v ∈ fixW_YS S)
    (x : S.LbarAsc ⧸ center S.LbarAsc) : actHat_YL hc x v = v := by
  induction x using QuotientGroup.induction_on with
  | H l => exact hv _ l.2

theorem commSpaceOf_actHat_YT (hc : center S.LbarAsc = ⊥) :
    A2Mod.commSpaceOf (actHat_YL hc) ⊤ = commU_YS S := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set C := A2Mod.commSpaceOf (actHat_YL hc) ⊤
  refine le_antisymm ((A2Mod.commSpaceOf_le_iff _).mpr fun x _ => ?_) ?_
  · induction x using QuotientGroup.induction_on with
    | H l => exact commSpace_le_commU_YS l.2
  ·
    have hperp : LinearMap.BilinForm.orthogonal S.q.polarBilin C ≤ fixW_YS S := by
      intro v hv
      rw [OrthoF2.mem_orthogonal_iff_polar] at hv
      intro l hl
      refine sub_eq_zero.mp (S.q_nondegenerate.1 _ fun w => ?_)
      obtain ⟨w', rfl⟩ := ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).surjective w
      have hmem : ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w' ∈ C :=
        A2Mod.commSpace_le_commSpaceOf _ (mem_top (QuotientGroup.mk' (center S.LbarAsc)
          ⟨l, hl⟩)) (mem_commSpace.mpr ⟨w', rfl⟩)
      have h1 := hv _ hmem
      rw [polar_sub_right] at h1
      rw [QuadraticMap.polarBilin_apply_apply, polar_sub_left, polar_O_YS, ← neg_sub, h1,
        neg_zero]
    calc commU_YS S ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin
          (LinearMap.BilinForm.orthogonal S.q.polarBilin C) :=
          LinearMap.BilinForm.orthogonal_le hperp
      _ = C := LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl _

theorem mem_radU_of_mem_YT {v : S.Qt} (hvW : v ∈ fixW_YS S) (hvU : v ∈ commU_YS S) :
    (⟨v, hvU⟩ : commU_YS S) ∈ AS35YS.radU S.q (commU_YS S) :=
  AS35YS.mem_radU.mpr fun u hu => by
    rw [polar_comm]
    exact mem_commU_YS.mp hu _ hvW

theorem finrank_V0_add_radU_YT :
    finrank (ZMod 2) (V0_YS S) + finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) =
      finrank (ZMod 2) (commU_YS S) := by
  have h1 := (finrank_V0_add_YS (S := S)).1
  have h2 := finrank_commU_add_YS (S := S)
  omega

theorem caseB_YT (hst : S.Asc512Standing) {r : S.Qt} (hrW : r ∈ fixW_YS S)
    (hrU : r ∈ commU_YS S) (hr0 : r ≠ 0) :
    ∃ j, finrank (ZMod 2) (V0_YS S) = 2 * j ∧ 2 * j + 1 ≤ finrank (ZMod 2) (commU_YS S) ∧
      Nat.card S.LbarAsc ≤ 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) ∧
      (2 * j + 1 = finrank (ZMod 2) (commU_YS S) →
        ∀ v ∈ fixW_YS S, v ∈ commU_YS S → v = 0 ∨ v = r) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨j, hj, hcard⟩ := card_lbar_le_sp_YT hst
  set R := AS35YS.radU S.q (commU_YS S)
  have hj' : finrank (ZMod 2) (V0_YS S) = 2 * j := hj
  have hsum : finrank (ZMod 2) (V0_YS S) + finrank (ZMod 2) R =
      finrank (ZMod 2) (commU_YS S) := finrank_V0_add_radU_YT
  have hr : (⟨⟨r, hrU⟩, mem_radU_of_mem_YT hrW hrU⟩ : R) ≠ 0 := fun h =>
    hr0 (congrArg (fun x : R => ((x : commU_YS S) : S.Qt)) h)
  have hR1 : 1 ≤ finrank (ZMod 2) R := by
    refine Nat.pos_of_ne_zero fun h0 => hr0 ?_
    have hmem : (⟨r, hrU⟩ : commU_YS S) ∈ R := mem_radU_of_mem_YT hrW hrU
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  refine ⟨j, hj, by omega, hcard, fun heq v hvW hvU => ?_⟩
  have h1 : finrank (ZMod 2) R = 1 := by omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hr).mp h1
    ⟨⟨v, hvU⟩, mem_radU_of_mem_YT hvW hvU⟩
  have hv : c • r = v := congrArg (fun x : R => ((x : commU_YS S) : S.Qt)) hc
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 c with rfl | rfl
  · left
    rw [← hv, zero_smul]
  · right
    rw [← hv, one_smul]

end Setting

end CFSG.LargeExtraspecial
