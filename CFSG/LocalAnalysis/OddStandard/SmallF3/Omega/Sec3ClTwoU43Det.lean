module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Field.ZMod

import TauCeti.LinearAlgebra.Eigenspace.Separation
import CFSG.Quasithin.EmptyFaithful.A38c15Line
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

private lemma mapsTo_eigenspace_of_comm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {a g : V ≃ₗ[ZMod 3] V} (hg : g * a = a * g) (μ : ZMod 3) :
    ∀ w ∈ Module.End.eigenspace (a : Module.End (ZMod 3) V) μ,
      g w ∈ Module.End.eigenspace (a : Module.End (ZMod 3) V) μ := by
  intro w hw
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  have hcomm : (a : Module.End (ZMod 3) V) (g w) =
      g ((a : Module.End (ZMod 3) V) w) := by
    simpa using (congrArg (fun e : V ≃ₗ[ZMod 3] V => e w) hg).symm
  rw [hcomm, hw, map_smul]

private theorem isSolvable_linearEquiv_of_finrank_eq_two {W : Type} [AddCommGroup W]
    [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
    (h : Module.finrank (ZMod 3) W = 2) : Group.IsSolvable (W ≃ₗ[ZMod 3] W) := by
  have hgl : Group.IsSolvable (LinearMap.GeneralLinearGroup (ZMod 3) W) := by
    let b : Module.Basis (Fin 2) (ZMod 3) W := Module.finBasisOfFinrankEq (ZMod 3) W h
    have e : LinearMap.GeneralLinearGroup (ZMod 3) W ≃*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
      (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
        Matrix.GeneralLinearGroup.toLin.symm
    haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
      CFSG.Quasithin.A38c15.isSolvable_gl2_zmod_three
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Group.IsSolvable (LinearMap.GeneralLinearGroup (ZMod 3) W) := hgl
  exact Group.isSolvable_of_isSolvable_injective
    (f := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).symm.toMonoidHom)
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).symm.injective

private lemma det_neg_eq_neg_one {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    (h : Module.finrank (ZMod 3) W = 1 ∨ Module.finrank (ZMod 3) W = 3) :
    LinearEquiv.det (LinearEquiv.neg (ZMod 3) : W ≃ₗ[ZMod 3] W) = -1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_neg, Units.val_one]
  have hsmul : ((LinearEquiv.neg (ZMod 3) : W ≃ₗ[ZMod 3] W) : W →ₗ[ZMod 3] W) =
      (-1 : ZMod 3) • (1 : W →ₗ[ZMod 3] W) := by
    ext x
    simp [LinearEquiv.neg_apply, neg_one_smul]
  rw [hsmul, LinearMap.det_smul, map_one, mul_one]
  rcases h with h | h <;> rw [h] <;> norm_num

private lemma commutator_le_ker_of_commGroup {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (H : Subgroup G) : ⁅H, H⁆ ≤ f.ker := by
  rw [Subgroup.commutator_le]
  intro g _ h _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (f g) (f h))

private lemma neg_ne_one {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [Nontrivial W] :
    (LinearEquiv.neg (ZMod 3) : W ≃ₗ[ZMod 3] W) ≠ 1 := by
  intro hone
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hw' : (-w : W) = w := by
    have := congrArg (fun e : W ≃ₗ[ZMod 3] W => e w) hone
    simpa [LinearEquiv.neg_apply] using this
  have h2 : (2 : ZMod 3) • w = 0 := by
    have : w + w = w + (-w) := by rw [hw']
    rw [two_smul, this, add_neg_cancel]
  have hw0 : w = 0 := by
    have h3 : w = (2 : ZMod 3)⁻¹ • ((2 : ZMod 3) • w) := by
      simp only [← mul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0), one_smul]
    rw [h3]
    simp [h2]
  exact hw hw0

private lemma neg_not_mem_of_invariant {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {J : Subgroup (V ≃ₗ[ZMod 3] V)}
    {W : Submodule (ZMod 3) V} (hWne : W ≠ ⊥)
    (hfin : Module.finrank (ZMod 3) W = 1 ∨ Module.finrank (ZMod 3) W = 2 ∨
      Module.finrank (ZMod 3) W = 3)
    (hJ : ⁅J, J⁆ = J)
    (hpres : ∀ g ∈ J, ∀ w ∈ W, (g : V ≃ₗ[ZMod 3] V) w ∈ W) :
    LinearEquiv.neg (ZMod 3) ∉ J := by
  intro hneg
  have hmap : ∀ g ∈ J, W.map (g : V →ₗ[ZMod 3] V) = W := by
    intro g hg
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hpres g hg w hw
    · intro w hw
      exact ⟨(g⁻¹ : V ≃ₗ[ZMod 3] V) w, hpres g⁻¹ (J.inv_mem hg) w hw, by simp⟩
  let ρ : J →* (W ≃ₗ[ZMod 3] W) :=
    MonoidHom.mk' (fun g => (g : V ≃ₗ[ZMod 3] V).ofSubmodules W W (hmap g g.2))
      (fun g h => by
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        simp only [LinearEquiv.ofSubmodules_apply, LinearEquiv.mul_apply,
          Subgroup.coe_mul])
  have hρ_apply : ∀ (g : J) (w : W), ((ρ g w : W) : V) = (g : V ≃ₗ[ZMod 3] V) w :=
    fun _ _ => rfl
  have hρneg : ρ ⟨LinearEquiv.neg (ZMod 3), hneg⟩ = LinearEquiv.neg (ZMod 3) := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hρ_apply]
    simp [LinearEquiv.neg_apply]
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  have hdet_case (hodd : Module.finrank (ZMod 3) W = 1 ∨ Module.finrank (ZMod 3) W = 3) :
      False := by
    have htop : (⊤ : Subgroup J) ≤ (LinearEquiv.det.comp ρ).ker := by
      have h := commutator_le_ker_of_commGroup (LinearEquiv.det.comp ρ) (⊤ : Subgroup J)
      rwa [Subgroup.commutator_eq_self] at h
    have hker : (LinearEquiv.det.comp ρ).ker = ⊤ := top_le_iff.mp htop
    have hdet1 : LinearEquiv.det (ρ ⟨LinearEquiv.neg (ZMod 3), hneg⟩) = 1 := by
      have hmem : (LinearEquiv.det.comp ρ) ⟨LinearEquiv.neg (ZMod 3), hneg⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact Subgroup.mem_top _
      simpa using hmem
    rw [hρneg, det_neg_eq_neg_one hodd] at hdet1
    have hval : ((-1 : (ZMod 3)ˣ) : ZMod 3) = 1 :=
      congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hdet1
    rw [Units.val_neg, Units.val_one] at hval
    exact (by decide : (-1 : ZMod 3) ≠ 1) hval
  have hsolv_case (h2 : Module.finrank (ZMod 3) W = 2) : False := by
    haveI : Group.IsSolvable (W ≃ₗ[ZMod 3] W) :=
      isSolvable_linearEquiv_of_finrank_eq_two h2
    haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    have hbot : ρ.range = ⊥ := by
      by_contra hne
      haveI : Nontrivial ρ.range := (Subgroup.nontrivial_iff_ne_bot ρ.range).mpr hne
      exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
    have hone : ρ ⟨LinearEquiv.neg (ZMod 3), hneg⟩ = 1 := by
      have hmem : ρ ⟨LinearEquiv.neg (ZMod 3), hneg⟩ ∈ ρ.range :=
        MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    rw [hρneg] at hone
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
    exact neg_ne_one hone
  rcases hfin with h1 | h2 | h3
  · exact hdet_case (Or.inl h1)
  · exact hsolv_case h2
  · exact hdet_case (Or.inr h3)

theorem cl_neg_not_mem_of_involution {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (hdim : Module.finrank (ZMod 3) V = 6)
    {a : V ≃ₗ[ZMod 3] V} (ha : ∀ v, a (a v) = v) (ha1 : a ≠ 1)
    (ha2 : a ≠ LinearEquiv.neg (ZMod 3)) {J : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hJ : ⁅J, J⁆ = J) (hc : ∀ g ∈ J, g * a = a * g) : LinearEquiv.neg (ZMod 3) ∉ J := by
  classical
  let T : Module.End (ZMod 3) V := (a : Module.End (ZMod 3) V)
  have hT : Function.Involutive T := fun v => by simpa [T] using ha v
  have hcompl : IsCompl (T.eigenspace 1) (T.eigenspace (-1)) :=
    TauCeti.isCompl_eigenspace_one_neg_one
      (isUnit_iff_ne_zero.mpr (by decide : (2 : ZMod 3) ≠ 0)) hT
  let Vp : Submodule (ZMod 3) V := T.eigenspace 1
  let Vm : Submodule (ZMod 3) V := T.eigenspace (-1)
  have hsum : Module.finrank (ZMod 3) Vp + Module.finrank (ZMod 3) Vm = 6 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hdim] at h
    simpa only [Vp, Vm] using h
  have hp : Vp ≠ ⊥ := by
    intro hbot
    apply ha2
    ext v
    have hv : v + T v ∈ T.eigenspace 1 := by
      rw [Module.End.mem_eigenspace_iff]
      rw [map_add, hT v, one_smul]
      exact add_comm _ _
    have hbot' : T.eigenspace 1 = ⊥ := by simpa only [Vp] using hbot
    rw [hbot'] at hv
    have hv0 : v + T v = 0 := by simpa using hv
    have hneg : T v = -v := eq_neg_of_add_eq_zero_right hv0
    simpa [LinearEquiv.neg_apply, T] using hneg
  have hm : Vm ≠ ⊥ := by
    intro hbot
    apply ha1
    ext v
    have hv : v - T v ∈ T.eigenspace (-1) := by
      rw [Module.End.mem_eigenspace_iff]
      simp only [map_sub, hT v, neg_one_smul, neg_sub]
    have hbot' : T.eigenspace (-1) = ⊥ := by simpa only [Vm] using hbot
    rw [hbot'] at hv
    have hv0 : v - T v = 0 := by simpa using hv
    have hpos : T v = v := (sub_eq_zero.mp hv0).symm
    simpa [T] using hpos
  have hp_pos : 0 < Module.finrank (ZMod 3) Vp := by
    haveI : Nontrivial Vp := Submodule.nontrivial_iff_ne_bot.mpr hp
    exact Module.finrank_pos_iff.mpr inferInstance
  have hm_pos : 0 < Module.finrank (ZMod 3) Vm := by
    haveI : Nontrivial Vm := Submodule.nontrivial_iff_ne_bot.mpr hm
    exact Module.finrank_pos_iff.mpr inferInstance
  by_cases hdp : Module.finrank (ZMod 3) Vp ≤ 3
  · refine neg_not_mem_of_invariant hp (by omega) hJ ?_
    intro g hg w hw
    exact mapsTo_eigenspace_of_comm (a := a) (hc g hg) 1 w hw
  · have hdm : Module.finrank (ZMod 3) Vm ≤ 3 := by
      have := not_le.mp hdp
      omega
    refine neg_not_mem_of_invariant hm (by omega) hJ ?_
    intro g hg w hw
    exact mapsTo_eigenspace_of_comm (a := a) (hc g hg) (-1) w hw

end CFSG.OddStandard.SmallF3.Omega
