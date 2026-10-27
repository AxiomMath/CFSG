module

public import CFSG.LargeExtraspecial.S13SevenE
public import CFSG.LargeExtraspecial.S13Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem sup_ne_top {V : Submodule (ZMod 2) S.Qt} (hV : V ≤ S.clSub (S.QG ⊓ S.Qa g)) {k : S.O}
    (hk : k ∈ K) (hk1 : k ≠ 1) :
    V ⊔ V.map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap ≠ ⊤ := by
  obtain ⟨m, rfl⟩ := Y.exists_ρ_eq hk
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set P' := S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) with hP'
  have hle : V ⊔ V.map ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap ≤ P ⊔ P' := by
    refine sup_le (hV.trans le_sup_left) ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Submodule.mem_sup_right (apply_mem_clSub_Qa_mul m g (hV hv))
  have hinf : P ⊓ P' = Fbar S g K := by
    have hzB : S.z ∈ S.QG ⊓ S.Qa ((m : G) * g) := Subgroup.mem_inf.mpr ⟨S.z_mem_QG,
      S.z_mem_Qa_of_mem_QG rfl (conj_mem_QG' S m.2 Y.haQ) (conj_ne_z' S m.2 Y.hne)⟩
    rw [hP, hP', clSub_inf hzB, ← Y.timmesfeld_13_1 hk hk1]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hdP : finrank (ZMod 2) P = S.width :=
    finrank_clSub_QG_inf_Qa Y.haQ Y.hne Y.C.card_QG_inf_Qa
  have hdP' : finrank (ZMod 2) P' = S.width :=
    finrank_clSub_QG_inf_Qa (conj_mem_QG' S m.2 Y.haQ) (conj_ne_z' S m.2 Y.hne)
      (Y.mul rfl).C.card_QG_inf_Qa
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P P'
  rw [hinf, Y.finrank_Fbar, hdP, hdP'] at h1
  intro htop
  have h2 := Submodule.finrank_mono hle
  rw [htop, finrank_top, S.finrank_Qt_eq_two_mul_width] at h2
  omega

omit Y in
theorem false_of_four (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {σ : S.O}
    (hσ : σ ∈ S.Lbar g) (hσE : σ ∉ Ebar S g K)
    (hpts : ∀ v ∈ Vt S g σ, v ≠ 0 → ∃ m : S.M, v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧
      σ ∈ S.Lbar ((m : G) * g) ∧ Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)))
    (hVP : Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa g)) {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) {c : S.M}
    (hcU : S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∉
      Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
    (ha : S.cl (g * S.z * g⁻¹) ∈ perp S (Fbar S ((c : G) * g) K))
    (h4 : 4 ≤ finrank (ZMod 2) (Vt S g σ)) : False := by
  obtain ⟨x, -, -, hxV, hWx, hcodim⟩ := Y.exists_x hCE hσ hσE hpts hVP hk hk1 hcU ha
  have hσx := Y.mem_Lbar_of_le_clSub hσ hσE
    (U := Vt S g σ ⊓ perp S (Fbar S ((c : G) * g) K)) (by omega)
    (fun v hv hv0 => by
      obtain ⟨m, h1, h2, h3⟩ := hpts v (Submodule.mem_inf.mp hv).1 hv0
      exact ⟨m, h1, h2, inf_le_left.trans h3⟩)
    (fun h => hxV (Submodule.mem_inf.mp h).1) hWx
  exact hxV (cl_mem_Vt hσx)

omit Y in
theorem finrank_Vt_le_three (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {σ : S.O}
    (hσ : σ ∈ S.Lbar g) (hσE : σ ∉ Ebar S g K) (hL : LinCase S g hσ) :
    finrank (ZMod 2) (Vt S g σ) ≤ 3 := by
  by_contra h4
  push Not at h4
  have hpts : ∀ v ∈ Vt S g σ, v ≠ 0 → ∃ m : S.M,
      v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧ σ ∈ S.Lbar ((m : G) * g) ∧
      Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) :=
    fun v hv hv0 => linCase_pt Y.H hσ hL hv hv0
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  obtain ⟨c, hcU⟩ := exists_pt_not_mem Y.H Y.irr
    (Y.sup_ne_top (Vt_le_clSub_of_V_le hL.le_Qa) hk hk1)
  have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
  have hdim := finrank_inf_perp_ge (Vt S g σ) (Fbar S ((c : G) * g) K)
  rw [Yc.finrank_Fbar] at hdim
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h0 => by
    rw [h0, finrank_bot] at hdim; omega :
      Vt S g σ ⊓ perp S (Fbar S ((c : G) * g) K) ≠ ⊥)
  obtain ⟨hdV, hdP⟩ := Submodule.mem_inf.mp hd
  obtain ⟨md, rfl, hσd, hVd⟩ := hpts _ hdV hd0
  have Y' : Hyp13 S ((md : G) * g) K := Y.mul rfl
  have hVt' : Vt S ((md : G) * g) σ = Vt S g σ := Vt_mul md σ
  have hσE' : σ ∉ Ebar S ((md : G) * g) K := fun h =>
    hσE (mem_Ebar.mpr ⟨hσ, (mem_Ebar.mp h).2⟩)
  refine false_of_four hCE Y' hσd hσE' (c := c * md⁻¹) ?_ (hVt' ▸ hVd) hk hk1 ?_ ?_
    (hVt' ▸ h4)
  · intro v hv hv0
    rw [hVt'] at hv ⊢
    obtain ⟨m, rfl, h1, h2⟩ := hpts v hv hv0
    exact ⟨m * md⁻¹, by rw [coe_mul_inv_mul], by rwa [coe_mul_inv_mul],
      by rwa [coe_mul_inv_mul]⟩
  · rw [coe_mul_inv_mul, hVt']
    exact hcU
  · rw [coe_mul_inv_mul]
    exact hdP

end Hyp13

end CFSG.LargeExtraspecial.S13
