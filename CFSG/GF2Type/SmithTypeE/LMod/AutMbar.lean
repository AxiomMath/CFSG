module

public import CFSG.GF2Type.SmithTypeE.LMod.Aut
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.BridgeSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.LargeExtraspecial
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def mbarConj (S : Setting G) : S.Mbar →* MulAut (S14.Mbar0 S) :=
  @MulAut.conjNormal S.Mbar _ (S14.Mbar0 S) (timmesfeldFStar_normal _)

theorem coe_mbarConj (S : Setting G) (m : S.Mbar) (x : S14.Mbar0 S) :
    ((mbarConj S m x : S14.Mbar0 S) : S.Mbar) = m * x * m⁻¹ := rfl


@[expose] noncomputable def mbarHom (S : Setting G) (ψ : S14.Mbar0 S ≃* T6) :
    S.Mbar →* MulAut T6 :=
  (MulAut.congr ψ).toMonoidHom.comp (mbarConj S)

theorem mbarHom_apply (S : Setting G) (ψ : S14.Mbar0 S ≃* T6) (m : S.Mbar)
    (x : S14.Mbar0 S) : mbarHom S ψ m (ψ x) = ψ (mbarConj S m x) :=
  (show mbarHom S ψ m (ψ x) = ψ (mbarConj S m (ψ.symm (ψ x))) from rfl).trans
    (congrArg (fun y => ψ (mbarConj S m y)) (ψ.symm_apply_apply x))

theorem mbarHom_of_mem (S : Setting G) (ψ : S14.Mbar0 S ≃* T6) (m : S14.Mbar0 S) :
    mbarHom S ψ m = MulAut.conj (ψ m) := by
  refine MulEquiv.ext fun y => ?_
  have hx := ψ.apply_symm_apply y
  have h1 : mbarConj S (m : S.Mbar) (ψ.symm y) = m * ψ.symm y * m⁻¹ := Subtype.ext rfl
  have h2 : ψ (m * ψ.symm y * m⁻¹) = ψ m * ψ (ψ.symm y) * (ψ m)⁻¹ := by
    simp only [map_mul, map_inv]
  have h3 := mbarHom_apply S ψ m (ψ.symm y)
  simp only [hx] at h2 h3
  exact h3.trans ((congrArg ψ h1).trans (h2.trans (MulAut.conj_apply _ _).symm))

theorem mbarHom_injective (S : Setting G) (ψ : S14.Mbar0 S ≃* T6) :
    Function.Injective (mbarHom S ψ) := by
  have : Finite S.Mbar := Bridge.finite_Mbar S
  refine (injective_iff_map_eq_one _).2 fun m hm => ?_
  have hc : ∀ x : S14.Mbar0 S, m * (x : S.Mbar) * m⁻¹ = x := by
    intro x
    have h2 : ψ x = ψ (mbarConj S m x) :=
      (congrArg (fun f : MulAut T6 => f (ψ x)) hm).symm.trans (mbarHom_apply S ψ m x)
    exact (congrArg Subtype.val (ψ.injective h2)).symm
  have hcent : m ∈ Subgroup.centralizer (S14.Mbar0 S : Set S.Mbar) :=
    Subgroup.mem_centralizer_iff.2 fun x hx =>
      (congrArg (· * m) (hc ⟨x, hx⟩).symm).trans (by group)
  have hm0 : m ∈ S14.Mbar0 S :=
    CFSG.Adapters.generalized_fitting_self_centralizing S.Mbar hcent
  have hz : ∀ x : S14.Mbar0 S, x * ⟨m, hm0⟩ = ⟨m, hm0⟩ * x := fun x =>
    Subtype.ext (show (x : S.Mbar) * m = m * x from
      (congrArg (· * m) (hc x).symm).trans (by group))
  have hψz : ψ ⟨m, hm0⟩ ∈ Subgroup.center T6 := by
    refine Subgroup.mem_center_iff.2 fun y => ?_
    have h1 := congrArg ψ (hz (ψ.symm y))
    simp only [map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1
  rw [center_T6_eq_bot, Subgroup.mem_bot] at hψz
  have h1 : (⟨m, hm0⟩ : S14.Mbar0 S) = 1 := by
    simpa only [MulEquiv.map_eq_one_iff] using hψz
  exact congrArg Subtype.val h1

theorem nonempty_mbar0_equiv_T6 (S : Setting G)
    (h : Nonempty (S14.Mbar0 S ≃* PSL(6, ZMod 2))) : Nonempty (S14.Mbar0 S ≃* T6) :=
  h.map fun e => e.trans pslT6

theorem autPerm_mbarHom_of_mem (S : Setting G) (ψ : S14.Mbar0 S ≃* T6) (m : S14.Mbar0 S) :
    autPerm (mbarHom S ψ m) = ψ m := by
  rw [mbarHom_of_mem, autPerm_conj]

end CFSG.GF2Type.SmithTypeE.LMod
