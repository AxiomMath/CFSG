module

public import CFSG.LargeExtraspecial.S10TwoA
public import CFSG.LargeExtraspecial.S10One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] noncomputable def fixWstar (X : Hyp10 S g t) : Subgroup S.O where
  carrier := {r | r ∈ Rbar S g t ∧
    ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t}
  mul_mem' := by
    rintro r s ⟨hr, hrw⟩ ⟨hs, hsw⟩
    refine ⟨mul_mem hr hs, fun w hw => ?_⟩
    have e : ((r * s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) +
          ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, map_sub]
      abel
    rw [e]
    exact add_mem (apply_mem_Vt_of_mem_Rbar X.haQ hr (hsw w hw)) (hrw w hw)
  one_mem' := ⟨one_mem _, fun w _ => by simp⟩
  inv_mem' := by
    rintro r ⟨hr, hrw⟩
    refine ⟨inv_mem hr, fun w hw => ?_⟩
    have hw' := apply_mem_Wt X.H (inv_mem hr) hw
    have e : ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
        -(((r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) -
          ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
      rw [apply_inv_apply_O]
      abel
    rw [e]
    exact neg_mem (hrw _ hw')

theorem mem_fixWstar {X : Hyp10 S g t} {r : S.O} : r ∈ fixWstar X ↔ r ∈ Rbar S g t ∧
    ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := Iff.rfl

theorem conj_mem_fixWstar (X : Hyp10 S g t) {r x : S.O} (hr : r ∈ Rbar S g t)
    (hx : x ∈ fixWstar X) : r * x * r⁻¹ ∈ fixWstar X := by
  refine ⟨mul_mem (mul_mem hr hx.1) (inv_mem hr), fun w hw => ?_⟩
  have hw' := apply_mem_Wt X.H (inv_mem hr) hw
  have e : ((r * x * r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    rw [map_sub, apply_inv_apply_O, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]
  rw [e]
  exact apply_mem_Vt_of_mem_Rbar X.haQ hr (hx.2 _ hw')

theorem Nbar_le_fixWstar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    Nbar S g t ≤ fixWstar X := by
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  obtain ⟨-, -, -, -, hN⟩ := timmesfeld_10_1_two hCE X hk hb
  exact fun x hx => ⟨Nbar_le_Rbar hx, hN x hx⟩

theorem not_mem_Qa_of_beta (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hβ : beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht) (orbV X.haQ X.ht hk) = 1) :
    (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa g := by
  intro hbQa
  have hbQ := conj_mem_QG' S k.2 X.haQ
  have hmem : (orbV X.haQ X.ht hk : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [coe_orbV, ρ_cl_conj_z S k X.haQ]
    exact S.cl_mem_clSub ⟨hbQ, hbQa⟩ hbQ
  rw [← beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ] at hmem
  rw [hmem] at hβ
  exact zero_ne_one hβ

theorem false_of_mem_fixWstar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t)
    (hβ : beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht) (orbV X.haQ X.ht hk) = 1)
    (hkW : S.ρ k ∈ fixWstar X) : False := by
  have hb := not_mem_Qa_of_beta X hk hβ
  obtain ⟨-, hint, hdim, -, -⟩ := timmesfeld_10_1_two hCE X hk hb
  set Pa := S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t with hPa
  set Pb := S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t with hPb
  have h5 := X.five_le_width
  have hnot : ¬ Pa ≤ Vt S g t := by
    intro hle
    rw [sup_eq_right.mpr hle, X.h4] at hdim
    omega
  obtain ⟨p, hp, hpV⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  apply hpV
  rw [← hint]
  refine ⟨Submodule.mem_sup_left hp, ?_⟩
  have h1 := hkW.2 p hp.2
  have h2 : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ Pb :=
    ⟨apply_mem_clSub_Qa_mul k hp.1, apply_mem_Wt X.H hk hp.2⟩
  have e : p = ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p -
      (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) := by abel
  rw [e]
  exact sub_mem (Submodule.mem_sup_left h2) (Submodule.mem_sup_right h1)

theorem orbV_eq_resV (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    orbV X.haQ X.ht hk = resV X.haQ t ⟨S.ρ k, hk⟩ (aV X.ht) := Subtype.ext rfl

theorem pi_eq_τ₁_or_τ₂ (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) {x : S.O}
    (hxL : x ∈ S.Lbar g) (hxN : x ∉ Nbar S g t) (hxW : x ∈ fixWstar X) :
    F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁ ∨ F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₂ := by
  have hst := F.π_mem_stabA hxL
  rw [mem_stabA, act_E00_iff] at hst
  rcases hst with h1 | h1 | h2 | hd
  · exact absurd ((F.ker _).mp h1) hxN
  · exact Or.inl h1
  · exact Or.inr h2
  exfalso
  obtain ⟨s, hs3, hspf⟩ := exists_pf_eq_one
  obtain ⟨δ₁, δ₂, hδ⟩ := diag_closure s hs3
  obtain ⟨r₁, hr₁⟩ := F.surj δ₁
  obtain ⟨r₂, hr₂⟩ := F.surj δ₂
  have e1 : F.π (r₁ * ⟨x, Lbar_le_Rbar X.ht hxL⟩ * r₁⁻¹) = δ₁ * (τ₁ * τ₂) * δ₁⁻¹ := by
    rw [map_mul, map_mul, map_inv, hr₁, hd]
  have e2 : F.π (r₂ * ⟨x, Lbar_le_Rbar X.ht hxL⟩ * r₂⁻¹) = δ₂ * (τ₁ * τ₂) * δ₂⁻¹ := by
    rw [map_mul, map_mul, map_inv, hr₂, hd]
  obtain ⟨y, hyd⟩ : ∃ y : Rbar S g t, y = (r₁ * ⟨x, Lbar_le_Rbar X.ht hxL⟩ * r₁⁻¹) *
      (r₂ * ⟨x, Lbar_le_Rbar X.ht hxL⟩ * r₂⁻¹) := ⟨_, rfl⟩
  have hπy : F.π y = s := by
    rw [hyd, map_mul, e1, e2, hδ]
  have hyK : (y : S.O) ∈ fixWstar X := by
    rw [hyd]
    exact mul_mem (conj_mem_fixWstar X r₁.2 hxW) (conj_mem_fixWstar X r₂.2 hxW)
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar y.2)
  have hkR : S.ρ k ∈ Rbar S g t := hk ▸ y.2
  have hyk : (⟨S.ρ k, hkR⟩ : Rbar S g t) = y := Subtype.ext hk
  have hkK : S.ρ k ∈ fixWstar X := hk ▸ hyK
  refine false_of_mem_fixWstar hCE X hkR ?_ hkK
  rw [orbV_eq_resV X, F.beta_eq, F.compat, hyk, hπy, F.base]
  exact hspf

end CFSG.LargeExtraspecial.S10
