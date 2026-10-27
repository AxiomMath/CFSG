module

public import CFSG.LargeExtraspecial.S13TwoB
public import CFSG.LargeExtraspecial.S13TwoE
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

namespace Hyp13

variable (Y : Hyp13 S g K) {σ : S.O} (hσ : σ ∈ S.Lbar g) (hσE : σ ∉ Ebar S g K)
  (hpts : ∀ v ∈ Vt S g σ, v ≠ 0 → ∃ m : S.M, v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧
    σ ∈ S.Lbar ((m : G) * g) ∧ Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)))
  {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) {c : S.M}
  (hcU : S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∉
    Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
include Y

include hk hk1 hcU in
theorem false_of_mem_U₀ {w : S.Qt} (hw : w ∈ Fbar S ((c : G) * g) K) (hw0 : w ≠ 0)
    (hwU : w ∈ Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
    (hkwU : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈
      Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap) : False := by
  have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
  apply hcU
  have hle : Fbar S ((c : G) * g) K ≤
      Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [← Yc.span_pair_eq hw hw0 hk hk1, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hwU
    · exact hkwU
  exact hle (cl_mem_Fbar Yc.H)

include hk hk1 hcU in
theorem Fbar_inf_Vt_eq_bot : Fbar S ((c : G) * g) K ⊓ Vt S g σ = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  by_contra hw0
  obtain ⟨hwF, hwV⟩ := Submodule.mem_inf.mp hw
  exact Y.false_of_mem_U₀ hk hk1 hcU hwF hw0 (Submodule.mem_sup_left hwV)
    (Submodule.mem_sup_right ⟨w, hwV, rfl⟩)

include hσ hσE hpts in
theorem Fbar_inf_Vt_le : Fbar S g K ⊓ Vt S g σ ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  intro w hw
  obtain ⟨hwF, hwV⟩ := Submodule.mem_inf.mp hw
  by_cases hw0 : w = 0
  · rw [hw0]; exact zero_mem _
  by_cases hwa : w = S.cl (g * S.z * g⁻¹)
  · rw [hwa]; exact Submodule.mem_span_singleton_self _
  exfalso
  obtain ⟨m, hmK, rfl⟩ := Y.exists_eq_cl_of_mem_Fbar hwF hw0
  obtain ⟨m', hm', hσm', -⟩ := hpts _ hwV hw0
  have hm1 : S.ρ m ≠ 1 := by
    intro h1
    apply hwa
    rw [← ρ_cl_conj_z S m Y.haQ, h1]
    rfl
  have hmQ := conj_mem_QG' S m.2 Y.haQ
  have hmz := conj_ne_z' S m.2 Y.hne
  have hL : S.Lbar ((m' : G) * g) = S.Lbar ((m : G) * g) :=
    Lbar_eq_of_cl_eq S hmQ hmz (conj_mem_QG' S m'.2 Y.haQ) hm'.symm
  rw [hL] at hσm'
  exact hσE ((Y.Ebar_eq_inf hmK hm1).symm ▸ Subgroup.mem_inf.mpr ⟨hσ, hσm'⟩)

include hσ hk hk1 in
theorem Fbar_le_U₀ : Fbar S g K ≤
    Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
  rw [← Y.span_pair_eq (cl_mem_Fbar Y.H) (cl_conj_z_ne_zero S Y.haQ Y.hne) hk hk1,
    Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.mem_sup_left (cl_a_mem_Vt hσ)
  · exact Submodule.mem_sup_right ⟨_, cl_a_mem_Vt hσ, rfl⟩

include hσ hσE hpts hk hk1 hcU in
theorem not_mem_Dbar {e : S.Qt} (he : e ∈ Vt S g σ)
    (hea : e ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) : e ∉ Fbar S g K ⊔ Fbar S ((c : G) * g) K := by
  intro heD
  obtain ⟨f₀, hf₀, f₁, hf₁, hsum⟩ := Submodule.mem_sup.mp heD
  have hU := Y.Fbar_le_U₀ hσ hk hk1
  by_cases hf₁0 : f₁ = 0
  · rw [hf₁0, add_zero] at hsum
    exact hea (Y.Fbar_inf_Vt_le hσ hσE hpts (Submodule.mem_inf.mpr ⟨hsum ▸ hf₀, he⟩))
  · have e1 : f₁ = e - f₀ := by rw [← hsum]; abel
    refine Y.false_of_mem_U₀ hk hk1 hcU hf₁ hf₁0 ?_ ?_
    · rw [e1]
      exact sub_mem (Submodule.mem_sup_left he) (hU hf₀)
    · rw [e1, map_sub]
      exact sub_mem (Submodule.mem_sup_right ⟨e, he, rfl⟩)
        (hU (apply_mem_Fbar_of_mem_K hk hf₀))

end Hyp13

end CFSG.LargeExtraspecial.S13
