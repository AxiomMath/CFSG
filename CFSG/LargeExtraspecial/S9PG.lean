module

public import CFSG.LargeExtraspecial.S9One
public import CFSG.LargeExtraspecial.S9PA
public import CFSG.LargeExtraspecial.S9PC
public import CFSG.LargeExtraspecial.S9PE
public import CFSG.LargeExtraspecial.S9TwoC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

@[expose] def PGL25ConjResidual : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} → S5.Irr S →
    8 ≤ S.width → ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O}
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g), PGL25Case H C ht ht1 hVQ →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t

@[expose] def PGL25TypeIIResidual : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} → S5.Irr S →
    8 ≤ S.width → ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O}
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g), PGL25Case H C ht ht1 hVQ →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
        (∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) →
        ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem pgl25TypeIIResidual_of_step5Residual (h : PGL25Step5Residual.{u}) :
    PGL25TypeIIResidual.{u} := by
  intro G _ _ S g hCE hIrr _ H hNo C t ht ht1 hVQ hP hA hR x hxM hτt hβ
  exact h hCE hIrr H hNo C ht ht1 hVQ hP hA hR x hxM hτt hβ

theorem eq_t_of_typeII_pgl25 (hP5 : PGL25TypeIIResidual.{u}) (hCE : CentralExtInput.{u})
    (hIrr : S5.Irr S) (hn8 : 8 ≤ S.width) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hP : PGL25Case H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) {x : S.O}
    (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) : x * t * x⁻¹ = t := by
  by_contra hne
  have hL : ∀ y ∈ S.Mbar, y * t * y⁻¹ ∈ S.Lbar g → y * t * y⁻¹ ∈ Nbar S g t :=
    fun y hy hyL => by rw [hR y hy hyL]; exact self_mem_Nbar H ht
  have hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t →
      x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t := by
    intro k hk hmem
    have hkt := commute_of_mem_Rbar H.conj_mem hk
    have h1 := (mem_Lbar_mul_iff S k g).mp (mem_inf.mp hmem).1
    have e : (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k =
        ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by group
    rw [e] at h1
    have h2 := hR _ (S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM) h1
    apply hne
    calc x * t * x⁻¹ = S.ρ k * (((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹) * (S.ρ k)⁻¹ := by
          group
      _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [h2]
      _ = t := by rw [hkt, mul_inv_cancel_right]
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hP.transitive hL hxM hβ
  have hW := hP5 hCE hIrr hn8 H hNo C ht ht1 hVQ hP hA hR x hxM hτt hβ
  have h4 := finrank_commWV_of_inf_eq_bot H C ht ht1 hVQ hinf
  rw [hP.finrank_eq] at h4
  have hbot : S8.commWV S g t (x * t * x⁻¹) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨w, hw, rfl⟩ := S8.mem_commWV.mp hu
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hW w hw
  rw [hbot, finrank_bot] at h4
  omega

theorem noPGL25_of_width (hP4 : PGL25ConjResidual.{u}) (hP5 : PGL25TypeIIResidual.{u})
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hn8 : 8 ≤ S.width) :
    ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {τ : S.O} (hτ : τ ∈ S.Lbar g)
      (hτ1 : τ ≠ 1) (hVQ : ¬ V S g τ ≤ S.Qa g), Rbar S g τ ≠ S.Lbar g →
      S.Lbar g ⊓ Nbar S g τ ≠ zpowers τ → ¬ PGL25Case H C hτ hτ1 hVQ := by
  intro H hNo C t ht ht1 hVQ _ hA hP
  have hn := four_lt_width_pgl25 H C ht ht1 hVQ hP hA
  have hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t :=
    hP4 hCE hIrr hn8 H hNo C ht ht1 hVQ hP hA
  have hiso : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t :=
    fun _ hxM hτt => eq_t_of_typeII_pgl25 hP5 hCE hIrr hn8 H hNo C ht ht1 hVQ hP hA hR hxM hτt
  exact hA (Lbar_inf_Nbar_eq_zpowers_of_isolated H hNo C hn ht ht1 hiso)

end CFSG.LargeExtraspecial.S9
