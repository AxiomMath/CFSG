module

public import CFSG.LargeExtraspecial.S8A5C
public import CFSG.LargeExtraspecial.S8ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem finrank_comm_sup_bounds (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) {x σ : S.O} (hxM : x ∈ S.Mbar)
    (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    2 ^ (D.m - 1) ∣ finrank (ZMod 2) (((Wt S g t).map
        ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) ∧
      (D.IsMinus → 2 ^ D.m ∣ finrank (ZMod 2) (((Wt S g t).map
        ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ)) ∧
      finrank (ZMod 2) (((Wt S g t).map
        ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) +
        finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 2 * D.m ∧
      2 * D.m ≤ finrank (ZMod 2) (((Wt S g t).map
        ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) +
        2 * finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  set f := (σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1 with hf
  set K := (Wt S g t).map f with hK
  set U := K ⊔ Vt S g t with hU
  have hVW := Vt_le_Wt H ht1
  have hUW : U ≤ Wt S g t := by
    refine sup_le ?_ hVW
    rintro _ ⟨w, hw, rfl⟩
    exact (Wt S g t).sub_mem (apply_mem_Wt_of_commute H C ht ht1 hVQ hσt hw) hw
  have hVU : Vt S g t ≤ U := le_sup_right
  obtain ⟨h1, h2, -⟩ := finrank_map_mkQ_of_invariant hCE hNo hΩ D hVU hUW
    (comm_sup_Vt_invariant D hσM hσt hσV)
  refine ⟨h1, h2, ?_⟩
  have hdimσ : finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxσ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hdimV := D.hdim
  have e1 := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ U
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVU] at e1
  have e2 := finrank_map_Wt_add (S := S) (g := g) (t := t) σ
  rw [← hf, ← hK] at e2
  have e3 := Submodule.finrank_sup_add_finrank_inf_eq K (Vt S g t)
  rw [← hU] at e3
  have hKc : K ≤ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rintro _ ⟨w, -, rfl⟩
    exact sub_mem_commSpace _ w
  have e4 : finrank (ZMod 2) ↥(K ⊓ Vt S g t) ≤
      finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
    Submodule.finrank_mono (by rw [inf_comm]; exact inf_le_inf_left _ hKc)
  have hUle : U ≤ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    sup_le (hKc.trans le_sup_right) le_sup_left
  have e5 := Submodule.finrank_mono hUle
  have e6 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
    (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  constructor <;> omega

theorem finrank_inf_of_three (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm3 : D.m = 3) {x σ : S.O}
    (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hnf : ¬ ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    finrank (ZMod 2) (((Wt S g t).map
        ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) = 4 ∧
      (finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 1 ∨
        finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2) := by
  obtain ⟨h1, -, h3, h4⟩ := finrank_comm_sup_bounds hCE hNo hΩ D hxM hxσ hσt hσV
  rw [hm3] at h1 h3 h4
  have hpos : finrank (ZMod 2) (((Wt S g t).map
      ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) ≠ 0 := by
    intro h0
    apply hnf
    intro w hw
    have hle := Submodule.finrank_eq_zero.mp h0
    have hmem : (Vt S g t).mkQ (((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) w) ∈
        (((Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map
          (Vt S g t).mkQ) :=
      Submodule.mem_map_of_mem (Submodule.mem_sup_left ⟨w, hw, rfl⟩)
    rw [hle, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  obtain ⟨c, hc⟩ := h1
  norm_num at hc
  constructor <;> omega

theorem finrank_inf_of_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4) {x σ : S.O}
    (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hnf : ¬ ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    finrank (ZMod 2) (((Wt S g t).map
        ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) = 8 ∧
      Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  obtain ⟨h1, -, h3, h4⟩ := finrank_comm_sup_bounds hCE hNo hΩ D hxM hxσ hσt hσV
  rw [hm4] at h1 h3 h4
  have hpos : finrank (ZMod 2) (((Wt S g t).map
      ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) ≠ 0 := by
    intro h0
    apply hnf
    intro w hw
    have hle := Submodule.finrank_eq_zero.mp h0
    have hmem : (Vt S g t).mkQ (((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) w) ∈
        (((Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map
          (Vt S g t).mkQ) :=
      Submodule.mem_map_of_mem (Submodule.mem_sup_left ⟨w, hw, rfl⟩)
    rw [hle, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  obtain ⟨c, hc⟩ := h1
  norm_num at hc
  have hk : finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 0 := by
    omega
  refine ⟨by omega, Submodule.finrank_eq_zero.mp hk⟩

theorem mem_Nbar_of_flag (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x σ : S.O} (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hflag : ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    σ ∈ Nbar S g t := by
  by_contra hσN
  have hk := finrank_Vt_inf_le_two D hfus hsub hxM hxσ hσN
  obtain ⟨-, -, -, h4⟩ := finrank_comm_sup_bounds hCE hNo hΩ D hxM hxσ hσt hσV
  have h0 : finrank (ZMod 2) (((Wt S g t).map
      ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) = 0 := by
    rw [Submodule.finrank_eq_zero, eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨w, hw, rfl⟩ := hy
    exact (Vt S g t).add_mem (hflag w hw) hv
  omega

end CFSG.LargeExtraspecial.S8
