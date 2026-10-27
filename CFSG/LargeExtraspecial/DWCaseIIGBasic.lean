module

public import CFSG.LargeExtraspecial.DWRed
public import CFSG.LargeExtraspecial.DWTransFaith
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}

abbrev mbarLin (y : S.Mbar) : S.Qt ≃ₗ[ZMod 2] S.Qt := ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)

theorem mbarLin_mul (y y' : S.Mbar) (v : S.Qt) :
    mbarLin (y * y') v = mbarLin y (mbarLin y' v) := rfl

theorem mbarLin_inv_apply (y : S.Mbar) (v : S.Qt) : mbarLin y (mbarLin y⁻¹ v) = v :=
  LinearEquiv.apply_symm_apply (mbarLin y) v

theorem mbarLin_apply_inv (y : S.Mbar) (v : S.Qt) : mbarLin y⁻¹ (mbarLin y v) = v :=
  LinearEquiv.symm_apply_apply (mbarLin y) v

variable (S) in
@[expose] def secStab (hM : S.M ≤ normalizer (A : Set G)) (W : Submodule (ZMod 2) S.Qt) :
    Subgroup S.Mbar where
  carrier := {y | (∀ w ∈ W, mbarLin y w = w) ∧ ∀ v ∈ S.clSub A, mbarLin y v - v ∈ W}
  mul_mem' {y y'} hy hy' := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [mbarLin_mul, hy'.1 w hw, hy.1 w hw]
    · have h1 := hy'.2 v hv
      rw [mbarLin_mul, show mbarLin y (mbarLin y' v) - v =
        mbarLin y (mbarLin y' v - v) + (mbarLin y v - v) by rw [map_sub]; abel, hy.1 _ h1]
      exact add_mem h1 (hy.2 v hv)
  one_mem' := ⟨fun _ _ => rfl, fun v _ => by
    change v - v ∈ W
    rw [sub_self]
    exact zero_mem _⟩
  inv_mem' {y} hy := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · have := mbarLin_apply_inv y w
      rwa [hy.1 w hw] at this
    · have hu : mbarLin y⁻¹ v ∈ S.clSub A :=
        MaxEA.apply_mem_clSub hM (y⁻¹ : S.Mbar).2 hv
      have h1 := W.neg_mem (hy.2 _ hu)
      rwa [mbarLin_inv_apply, neg_sub] at h1

theorem secStab_normal (hM : S.M ≤ normalizer (A : Set G)) {W : Submodule (ZMod 2) S.Qt}
    (hW : IsMbarInvariant S W) : (secStab S hM W).Normal := by
  have hWm : ∀ g : S.Mbar, ∀ w ∈ W, mbarLin g w ∈ W := by
    rintro ⟨_, m, rfl⟩ w hw
    exact hW m w hw
  refine ⟨fun y hy g => ⟨fun w hw => ?_, fun v hv => ?_⟩⟩
  · rw [mbarLin_mul, mbarLin_mul, hy.1 _ (hWm _ w hw), mbarLin_inv_apply]
  · have hu : mbarLin g⁻¹ v ∈ S.clSub A := MaxEA.apply_mem_clSub hM (g⁻¹ : S.Mbar).2 hv
    have h1 := hWm g _ (hy.2 _ hu)
    rwa [map_sub, mbarLin_inv_apply, ← mbarLin_mul, ← mbarLin_mul] at h1

namespace MaxEA

variable [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
include hA hM

theorem secStab_isPGroup (W : Submodule (ZMod 2) S.Qt) : IsPGroup 2 (secStab S hM W) := by
  intro y
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  rw [pow_one, pow_two]
  refine hA.eq_one_of_forall_clSub hM (S.Mbar.mul_mem (y : S.Mbar).2 (y : S.Mbar).2)
    fun v hv => ?_
  change mbarLin (y : S.Mbar) (mbarLin (y : S.Mbar) v) = v
  have hd := y.2.1 _ (y.2.2 v hv)
  rw [map_sub, sub_eq_iff_eq_add] at hd
  rw [hd, sub_add_eq_add_sub, ZModModule.add_self, zero_sub, ZModModule.neg_eq_self]

theorem eq_one_of_fix_of_sub_mem {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
    {y : S.O} (hy : y ∈ S.Mbar) (hfix : ∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w)
    (hsub : ∀ v ∈ S.clSub A, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ W) : y = 1 := by
  have hle : secStab S hM W ≤ CFSG.pCore 2 S.Mbar :=
    le_sSup ⟨secStab_normal hM hW, hA.secStab_isPGroup hM W⟩
  rw [S.pCore_Mbar_eq_bot] at hle
  have := hle (show (⟨y, hy⟩ : S.Mbar) ∈ secStab S hM W from ⟨hfix, hsub⟩)
  rw [mem_bot] at this
  exact congrArg Subtype.val this

omit [IsElementaryAbelian 2 A] hA in
theorem isMbarInvariant_clSub : IsMbarInvariant S (S.clSub A) :=
  fun m _ hv => apply_mem_clSub hM ⟨m, rfl⟩ hv

end MaxEA

end CFSG.LargeExtraspecial.DW
