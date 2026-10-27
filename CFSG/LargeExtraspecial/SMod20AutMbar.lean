module

public import CFSG.LargeExtraspecial.SMod20AutCent
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.OutSixUnitary
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.Open Matrix
open CFSG.Blueprint.Fischer (K)

local notation "SUK" =>
  CFSG.LieType.Universal.Unitary.SUid CFSG.Fischer.Classification.Unitary.frob 6

theorem SUK_eq_unitarySU : SUK = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 :=
  CFSG.LieType.Universal.Unitary.SUid_eq_statedSU CFSG.Fischer.Classification.Unitary.card_K 6

theorem timmesfeldPSU_six_eq_map : timmesfeldPSU 6 = Subgroup.map ProjGenLinGroup.mk SUK := by
  rw [S14.timmesfeldPSU_eq_map, SUK_eq_unitarySU]

theorem center_GL_subgroupOf_SUK :
    (Subgroup.center (GL (Fin 6) K)).subgroupOf SUK = Subgroup.center SUK := by
  rw [CFSG.Fischer.Classification.Unitary.center_SUid (by norm_num),
    CFSG.Assembly.LowTwoRank.StatedScalars, GeneralLinearGroup.center_eq_range_scalar]

@[expose] noncomputable def tpsuPG : timmesfeldPSU 6 ≃* CFSG.Fischer.Classification.Unitary.PG 6 :=
  (MulEquiv.subgroupCongr timmesfeldPSU_six_eq_map).trans
    ((S14.mapMkEquiv SUK).trans (QuotientGroup.quotientMulEquivOfEq center_GL_subgroupOf_SUK))

end CFSG.LargeExtraspecial.SMod20.Aut

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.Open Matrix Aut

@[expose] noncomputable def tpsuT46 :
    timmesfeldPSU 6 ≃* T46 :=
  tpsuPG.trans pgT46

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def mbarConj (S : Setting G) : S.Mbar →* MulAut (S14.Mbar0 S) :=
  @MulAut.conjNormal S.Mbar _ (S14.Mbar0 S) (timmesfeldFStar_normal _)

theorem coe_mbarConj (S : Setting G) (m : S.Mbar) (x : S14.Mbar0 S) :
    ((mbarConj S m x : S14.Mbar0 S) : S.Mbar) = m * x * m⁻¹ := rfl


@[expose] noncomputable def mbarHom (S : Setting G) (ψ : S14.Mbar0 S ≃* T46) :
    S.Mbar →* MulAut T46 :=
  (MulAut.congr ψ).toMonoidHom.comp (mbarConj S)

theorem mbarHom_apply (S : Setting G) (ψ : S14.Mbar0 S ≃* T46) (m : S.Mbar)
    (x : S14.Mbar0 S) : mbarHom S ψ m (ψ x) = ψ (mbarConj S m x) :=
  (show mbarHom S ψ m (ψ x) = ψ (mbarConj S m (ψ.symm (ψ x))) from rfl).trans
    (congrArg (fun y => ψ (mbarConj S m y)) (ψ.symm_apply_apply x))

theorem mbarHom_of_mem (S : Setting G) (ψ : S14.Mbar0 S ≃* T46) (m : S14.Mbar0 S) :
    mbarHom S ψ m = MulAut.conj (ψ m) := by
  refine MulEquiv.ext fun y => ?_
  have hx := ψ.apply_symm_apply y
  have h1 : mbarConj S (m : S.Mbar) (ψ.symm y) = m * ψ.symm y * m⁻¹ := Subtype.ext rfl
  have h2 : ψ (m * ψ.symm y * m⁻¹) = ψ m * ψ (ψ.symm y) * (ψ m)⁻¹ := by
    simp only [map_mul, map_inv]
  have h3 := mbarHom_apply S ψ m (ψ.symm y)
  simp only [hx] at h2 h3
  exact h3.trans ((congrArg ψ h1).trans (h2.trans (MulAut.conj_apply _ _).symm))

theorem mbarHom_injective
    (S : Setting G) (ψ : S14.Mbar0 S ≃* T46) :
    Function.Injective (mbarHom S ψ) := by
  have : Finite S.Mbar := Bridge.finite_Mbar S
  refine (injective_iff_map_eq_one _).2 fun m hm => ?_
  have hc : ∀ x : S14.Mbar0 S, m * (x : S.Mbar) * m⁻¹ = x := by
    intro x
    have h2 : ψ x = ψ (mbarConj S m x) :=
      (congrArg (fun f : MulAut T46 => f (ψ x)) hm).symm.trans (mbarHom_apply S ψ m x)
    exact (congrArg Subtype.val (ψ.injective h2)).symm
  have hcent : m ∈ Subgroup.centralizer (S14.Mbar0 S : Set S.Mbar) :=
    Subgroup.mem_centralizer_iff.2 fun x hx =>
      (congrArg (· * m) (hc ⟨x, hx⟩).symm).trans (by group)
  have hm0 : m ∈ S14.Mbar0 S :=
    CFSG.Adapters.generalized_fitting_self_centralizing S.Mbar hcent
  have hz : ∀ x : S14.Mbar0 S, x * ⟨m, hm0⟩ = ⟨m, hm0⟩ * x := fun x =>
    Subtype.ext (show (x : S.Mbar) * m = m * x from
      (congrArg (· * m) (hc x).symm).trans (by group))
  have hψz : ψ ⟨m, hm0⟩ ∈ Subgroup.center T46 := by
    refine Subgroup.mem_center_iff.2 fun y => ?_
    have h1 := congrArg ψ (hz (ψ.symm y))
    simp only [map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1
  rw [center_T46_eq_bot, Subgroup.mem_bot] at hψz
  have h1 : (⟨m, hm0⟩ : S14.Mbar0 S) = 1 := by
    simpa only [MulEquiv.map_eq_one_iff] using hψz
  exact congrArg Subtype.val h1

theorem nonempty_mbar0_equiv_T46 (S : Setting G)
    (h : Nonempty (S14.Mbar0 S ≃* timmesfeldPSU 6)) : Nonempty (S14.Mbar0 S ≃* T46) :=
  h.map fun e => e.trans tpsuT46

end CFSG.LargeExtraspecial.SMod20
