module

public import CFSG.LargeExtraspecial.S8KS
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LargeExtraspecial.S8KR

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem finrank_commSpace_ne {d : S.O} (hd : d ∈ conjD S t) :
    finrank (ZMod 2) (commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≠
      finrank (ZMod 2) ↥(Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  rw [finrank_commSpace_of_mem_conjD H C ht ht1 hVQ hd, B.finrank_sup, D.hdim, B.red.hm4]
  norm_num

theorem map_eq_of_mem {gg : S.O} (hgM : gg ∈ S.Mbar) {e : S.O}
    (he : e ∈ closure (insert τ (N1bar S g t τ : Set S.O))) (he1 : e ≠ 1)
    (hge : gg⁻¹ * e * gg ∈ closure (insert τ (N1bar S g t τ : Set S.O))) :
    (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
      ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  set Y := Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hYdef
  have he'1 : gg⁻¹ * e * gg ≠ 1 := fun h => he1 (by
    have := congrArg (fun z => gg * z * gg⁻¹) h
    simpa [mul_assoc] using this)
  have hee : e = gg * (gg⁻¹ * e * gg) * gg⁻¹ := by group
  have hcs : commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (commSpace ((gg⁻¹ * e * gg : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
        ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    conv_lhs => rw [hee]
    exact S7.commSpace_conj gg _
  rcases B.classify he he1 with ⟨⟨y, hyM, hy⟩, heY⟩ | heY <;>
    rcases B.classify hge he'1 with ⟨⟨y', hy'M, hy'⟩, he'Y⟩ | he'Y
  ·
    have h1 := B.map_eq_of_commSpace_le hyM (hy ▸ heY)
    have h2 := B.map_eq_of_commSpace_le hy'M (hy' ▸ he'Y)
    have h3 : commSpace (((gg * y') * t * (gg * y')⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Y := by
      have e1 : (gg * y') * t * (gg * y')⁻¹ = e := by rw [hee, hy']; group
      rw [e1]
      exact heY
    have h4 := B.map_eq_of_commSpace_le (mul_mem hgM hy'M) h3
    calc Y.map ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        (Y.map ((y' : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)).map
          ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by rw [h2]
      _ = Y.map (((gg * y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
          rw [← Submodule.map_comp]
          rfl
      _ = Y := h4
  · exfalso
    apply B.finrank_commSpace_ne ⟨y, hyM, hy⟩
    rw [hcs, he'Y, LinearEquiv.finrank_map_eq]
  · exfalso
    apply B.finrank_commSpace_ne ⟨y', hy'M, hy'⟩
    rw [← heY, hcs, LinearEquiv.finrank_map_eq]
  · calc Y.map ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        (commSpace ((gg⁻¹ * e * gg : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
          ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by rw [he'Y]
      _ = commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) := hcs.symm
      _ = Y := heY

omit B in
theorem mem_ET {x : S.Mbar} :
    x ∈ (closure (insert τ (N1bar S g t τ : Set S.O))).subgroupOf S.Mbar ↔
      (x : S.O) ∈ closure (insert τ (N1bar S g t τ : Set S.O)) :=
  mem_subgroupOf

omit B in
theorem mem_conjSubgroup_ET {gg x : S.Mbar} :
    x ∈ conjSubgroup gg ((closure (insert τ (N1bar S g t τ : Set S.O))).subgroupOf S.Mbar) ↔
      ((gg : S.O))⁻¹ * x * gg ∈ closure (insert τ (N1bar S g t τ : Set S.O)) := by
  rw [mem_conjSubgroup, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem conjSubgroup_eq {gg : S.Mbar}
    (hY : (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
      (((gg : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    conjSubgroup gg ((closure (insert τ (N1bar S g t τ : Set S.O))).subgroupOf S.Mbar) =
      (closure (insert τ (N1bar S g t τ : Set S.O))).subgroupOf S.Mbar := by
  have hE := B.map_conj_E_of_map_eq gg.2 hY
  ext x
  rw [mem_conjSubgroup_ET, mem_ET]
  constructor
  · intro h
    have h1 : (x : S.O) ∈
        (closure (insert τ (N1bar S g t τ : Set S.O))).map (MulAut.conj (gg : S.O)).toMonoidHom :=
      ⟨_, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rwa [hE] at h1
  · intro h
    rw [← hE] at h
    obtain ⟨e, he, hex⟩ := h
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hex
    rw [← hex]
    simpa [mul_assoc] using he

end Bad4

end CFSG.LargeExtraspecial.S8
