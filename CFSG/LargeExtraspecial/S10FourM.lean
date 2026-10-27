module

public import CFSG.LargeExtraspecial.S10FourL
public import CFSG.LargeExtraspecial.S10FlagC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem apply_sub_mem_of_Abar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {x : S.O}
    (hx : x ∈ S.Lbar g ⊓ Nbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  obtain ⟨-, -, -, -, hN⟩ := timmesfeld_10_1_two hCE X hk hb
  refine ⟨?_, hN x (Subgroup.mem_inf.mp hx).2 w hw⟩
  obtain ⟨y, hyQ, rfl⟩ := S.exists_cl w
  have hya : y * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * y := by
    rw [← S.polar_cl_eq_zero_iff hyQ X.haQ, polar_comm]
    exact (mem_Wt.mp hw) _ (cl_a_mem_Vt X.ht)
  exact X.C.comm_le y ⟨hyQ, mem_centralizer_singleton_iff.mpr hya⟩ x
    (Subgroup.mem_inf.mp hx).1

theorem StronglyClosedL.fix_commSpace_conj_of_fix (hSC : StronglyClosedL S g t)
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) (hfixAll : FixVtConj S g t)
    {m : S.M}
    (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) {w : S.Qt}
    (hw : w ∈ commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  have hne' : S.ρ m⁻¹ * t * (S.ρ m⁻¹)⁻¹ ≠ t := fun h => hne (by
    rw [map_inv, inv_inv] at h
    calc S.ρ m * t * (S.ρ m)⁻¹ = S.ρ m * ((S.ρ m)⁻¹ * t * S.ρ m) * (S.ρ m)⁻¹ := by rw [h]
      _ = t := by group)
  have hcomm' : (S.ρ m⁻¹ * t * (S.ρ m⁻¹)⁻¹) * t = t * (S.ρ m⁻¹ * t * (S.ρ m⁻¹)⁻¹) := by
    rw [map_inv, inv_inv]
    calc (S.ρ m)⁻¹ * t * S.ρ m * t = (S.ρ m)⁻¹ * (t * (S.ρ m * t * (S.ρ m)⁻¹)) * S.ρ m := by
          group
      _ = (S.ρ m)⁻¹ * ((S.ρ m * t * (S.ρ m)⁻¹) * t) * S.ρ m := by rw [hcomm]
      _ = t * ((S.ρ m)⁻¹ * t * S.ρ m) := by group
  have hv := (mem_commSpace_conj_iff X m).mp hw
  have h1 := hfixAll _ hne' hcomm' _ hv
  rw [map_inv, inv_inv] at h1
  have h2 := congrArg (fun y => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) h1
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply_O] at h2
  exact h2

theorem exists_fix_of_Abar_of_fix (hSC : StronglyClosedL S g t)
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) (hfixAll : FixVtConj S g t)
    {m : S.M}
    (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) {x : S.O}
    (hx : x ∈ S.Lbar g ⊓ Nbar S g t) :
    ∃ w ∈ commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt), w ≠ 0 ∧
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  have hVmW : commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      Wt S g t := fun w hw => by
    rw [← (commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ).2, mem_fixSpace]
    exact hSC.fix_commSpace_conj_of_fix hCE X F hfixAll hne hcomm hw
  obtain ⟨Vm, hVm⟩ : ∃ Vm : Submodule (ZMod 2) S.Qt,
      Vm = commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨_, rfl⟩
  rw [← hVm] at hVmW ⊢
  have hVm4 : finrank (ZMod 2) Vm = 4 := by rw [hVm]; exact finrank_commSpace_conj_t X m
  obtain ⟨f, hf⟩ : ∃ f : Vm →ₗ[ZMod 2] S.Qt,
      f = (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1).domRestrict Vm := ⟨_, rfl⟩
  have hrange : LinearMap.range f ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
    rintro _ ⟨w, rfl⟩
    rw [hf]
    exact apply_sub_mem_of_Abar hCE X hx (hVmW w.2)
  have h3 := Submodule.finrank_mono hrange
  have h4 := finrank_clSub_inf_Vt_le X
  have h5 := LinearMap.finrank_range_add_finrank_ker f
  rw [hVm4] at h5
  have hker : 1 ≤ finrank (ZMod 2) (LinearMap.ker f) := by omega
  rw [Submodule.one_le_finrank_iff] at hker
  obtain ⟨w, hwk, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h), ?_⟩
  have := LinearMap.mem_ker.mp hwk
  rw [hf] at this
  simp only [LinearMap.domRestrict_apply, LinearMap.sub_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, sub_eq_zero] at this
  exact this

theorem StronglyClosedL.commute_Abar_of_conj_of_fix (hSC : StronglyClosedL S g t)
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) (hfixAll : FixVtConj S g t)
    {m : S.M}
    (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) {x : S.O}
    (hx : x ∈ S.Lbar g ⊓ Nbar S g t) :
    x * (S.ρ m * t * (S.ρ m)⁻¹) = (S.ρ m * t * (S.ρ m)⁻¹) * x := by
  by_contra hxt
  obtain ⟨t', ht'⟩ : ∃ t' : S.O, t' = S.ρ m * t * (S.ρ m)⁻¹ := ⟨_, rfl⟩
  rw [← ht'] at hxt
  have hxL := (Subgroup.mem_inf.mp hx).1
  have hxM : x ∈ S.Mbar := S.Lbar_le_Mbar g hxL
  obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.mp hxM
  have ht'M : t' ∈ S.Mbar := ht' ▸ conj_mem_Mbar X m
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S X.haQ X.ht
  have ht't' : t' * t' = 1 := by
    rw [ht', show S.ρ m * t * (S.ρ m)⁻¹ * (S.ρ m * t * (S.ρ m)⁻¹) = S.ρ m * (t * t) * (S.ρ m)⁻¹
      by group, htt]
    group
  have hxx : x * x = 1 := S4.mul_self_of_mem_Lbar S X.haQ hxL
  have hfixa : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    rw [ht']
    exact hfixAll m hne hcomm _ (cl_a_mem_Vt X.ht)
  have ht'N := mem_normalizer_of_fix_a X ht'M hfixa
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp ht'M
  have hcommt : S.ρ y₀ * t = t * S.ρ y₀ := by rw [hy₀, ht', hcomm]
  have hyA : t' * x * t'⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := Subgroup.mem_inf.mpr
    ⟨(mem_normalizer_iff.mp ht'N x).mp hxL, by
      rw [← hy₀]
      exact conj_mem_Nbar X.haQ hcommt (Subgroup.mem_inf.mp hx).2⟩
  have hxy : (t' * x * t'⁻¹) * x = x * (t' * x * t'⁻¹) :=
    Lbar_comm S X.haQ (Subgroup.mem_inf.mp hyA).1 hxL
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht't'
  have h12 : (x * t' * x⁻¹) * t' = t' * (x * t' * x⁻¹) := by
    rw [hxinv]
    rw [ht'inv] at hxy
    calc x * t' * x * t' = x * (t' * x * t') := by group
      _ = (t' * x * t') * x := hxy.symm
      _ = t' * (x * t' * x) := by group
  have hne2 : x * t' * x⁻¹ ≠ t' := fun h => hxt (by
    calc x * t' = x * t' * x⁻¹ * x := by group
      _ = t' * x := by rw [h])
  obtain ⟨m₃, hm₃⟩ : ∃ m₃ : S.M, m₃ = m⁻¹ * x₀ * m := ⟨_, rfl⟩
  have hρm₃ : S.ρ m₃ = (S.ρ m)⁻¹ * x * S.ρ m := by
    rw [hm₃, map_mul, map_mul, map_inv, hx₀]
  have ht₃ : S.ρ m₃ * t * (S.ρ m₃)⁻¹ = (S.ρ m)⁻¹ * (x * t' * x⁻¹) * S.ρ m := by
    rw [hρm₃, ht']
    group
  have hne₃ : S.ρ m₃ * t * (S.ρ m₃)⁻¹ ≠ t := by
    rw [ht₃]
    intro h
    apply hne2
    calc x * t' * x⁻¹ = S.ρ m * ((S.ρ m)⁻¹ * (x * t' * x⁻¹) * S.ρ m) * (S.ρ m)⁻¹ := by group
      _ = S.ρ m * t * (S.ρ m)⁻¹ := by rw [h]
      _ = t' := ht'.symm
  have hcomm₃ : (S.ρ m₃ * t * (S.ρ m₃)⁻¹) * t = t * (S.ρ m₃ * t * (S.ρ m₃)⁻¹) := by
    rw [ht₃]
    have ht'' : t = (S.ρ m)⁻¹ * t' * S.ρ m := by rw [ht']; group
    conv_lhs => rw [ht'']
    conv_rhs => rw [ht'']
    calc (S.ρ m)⁻¹ * (x * t' * x⁻¹) * S.ρ m * ((S.ρ m)⁻¹ * t' * S.ρ m) =
          (S.ρ m)⁻¹ * ((x * t' * x⁻¹) * t') * S.ρ m := by group
      _ = (S.ρ m)⁻¹ * (t' * (x * t' * x⁻¹)) * S.ρ m := by rw [h12]
      _ = (S.ρ m)⁻¹ * t' * S.ρ m * ((S.ρ m)⁻¹ * (x * t' * x⁻¹) * S.ρ m) := by group
  obtain ⟨w, hwV, hw0, hxw⟩ := exists_fix_of_Abar_of_fix hSC hCE X F hfixAll hne hcomm hx
  have hvV := (mem_commSpace_conj_iff X m).mp hwV
  have hx' : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    conv_lhs => rw [← hxw]
    exact inv_apply_apply_O x _
  have e : (((S.ρ m₃)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
    have e1 : (S.ρ m₃)⁻¹ = (S.ρ m)⁻¹ * x⁻¹ * S.ρ m := by rw [hρm₃]; group
    rw [e1]
    change (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) = _
    rw [apply_inv_apply_O, hx']
  have hvC : (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈
      commSpace ((S.ρ m₃ * t * (S.ρ m₃)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [mem_commSpace_conj_iff X m₃, e]
    exact hvV
  have h0 := hSC.eq_zero_of_mem_inf_of_fix hCE X F hfixAll hne₃ hcomm₃ hvV hvC
  apply hw0
  have h1 := congrArg (fun y => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) h0
  simp only [apply_inv_apply_O, map_zero] at h1
  exact h1

end CFSG.LargeExtraspecial.S10
