module

public import CFSG.LargeExtraspecial.AS35YSIrr
public import CFSG.LargeExtraspecial.AS35YRSet

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35YS

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
  (U : Submodule (ZMod 2) V)

theorem radU_le_ker : radU q U ≤ LinearMap.ker (qU q U).polarBilin := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, polar_qU]
  exact mem_radU.mp hx y y.2

theorem radU_le_ker_flip : radU q U ≤ LinearMap.ker (qU q U).polarBilin.flip := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply,
    polar_qU, polar_comm]
  exact mem_radU.mp hx y y.2

@[expose] noncomputable def bQuo : LinearMap.BilinForm (ZMod 2) (Quo q U) :=
  (qU q U).polarBilin.liftQ₂ (radU q U) (radU q U) (radU_le_ker q U) (radU_le_ker_flip q U)

variable {q U}

@[simp] theorem bQuo_mk (x y : U) :
    bQuo q U (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = polar q x y := by
  rw [bQuo, LinearMap.liftQ₂_mk, QuadraticMap.polarBilin_apply_apply, polar_qU]

theorem bQuo_isAlt : (bQuo q U).IsAlt := by
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [bQuo_mk, QuadraticMap.polar_self, two_smul, ZModModule.add_self]

theorem bQuo_nondegenerate : (bQuo q U).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl bQuo_isAlt).nondegenerate_iff_separatingLeft.mpr fun v hv => ?_
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero, mem_radU]
    intro u hu
    have := hv (Submodule.Quotient.mk ⟨u, hu⟩)
    rwa [bQuo_mk] at this

theorem bQuo_quoHom {H : Subgroup (V ≃ₗ[ZMod 2] V)} {hiso : ∀ g ∈ H, ∀ v, q (g v) = q v}
    {hU : ∀ g ∈ H, ∀ u ∈ U, g u ∈ U} (g : H) (v w : Quo q U) :
    bQuo q U (quoHom q U H hiso hU g v) (quoHom q U H hiso hU g w) = bQuo q U v w := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    induction w using Submodule.Quotient.induction_on with
    | H y =>
      rw [quoHom_mk, quoHom_mk, bQuo_mk, bQuo_mk]
      exact polar_map_YS (hiso g g.2) x y

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem bQuo_act0_YS (hst : S.Asc512Standing) (m : S.Mbar) (v w : V0_YS S) :
    AS35YS.bQuo S.q (commU_YS S) (act0_YS hst m v) (act0_YS hst m w) =
      AS35YS.bQuo S.q (commU_YS S) v w :=
  AS35YS.bQuo_quoHom (hiso := mbarL_iso_YS) (hU := mbarL_U_YS hst) _ v w

theorem card_lbar_le_sp_YT (hst : S.Asc512Standing) :
    ∃ j, finrank (ZMod 2) (V0_YS S) = 2 * j ∧
      Nat.card S.LbarAsc ≤ 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Finite (V0_YS S) := Module.finite_of_finite (ZMod 2)
  have : Finite (V0_YS S ≃ₗ[ZMod 2] V0_YS S) := AS35YR.finite_linearEquiv_YR
  obtain ⟨j, hj⟩ := S2.sp_even_finrank (f := AS35YS.bQuo S.q (commU_YS S)) AS35YS.bQuo_isAlt
    AS35YS.bQuo_nondegenerate
  have hdim : finrank (ZMod 2) (V0_YS S) = 2 * j := by
    rw [two_mul]
    exact hj
  refine ⟨j, hdim, ?_⟩
  have hmem : ∀ l : S.LbarAsc, actL_YS hst l ∈
      TauCeti.BilinForm.isometryGroup (AS35YS.bQuo S.q (commU_YS S)) := fun l =>
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun v w => bQuo_act0_YS hst _ v w
  have h1 := Nat.card_le_card_of_injective
    (fun l : S.LbarAsc => (⟨actL_YS hst l, hmem l⟩ :
      TauCeti.BilinForm.isometryGroup (AS35YS.bQuo S.q (commU_YS S))))
    fun a b hab => actL_YS_injective hst (congrArg Subtype.val hab)
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup j
    (AS35YS.bQuo S.q (commU_YS S)) AS35YS.bQuo_isAlt AS35YS.bQuo_nondegenerate hdim,
    Nat.card_zmod] at h1
  exact h1

end Setting

end CFSG.LargeExtraspecial
