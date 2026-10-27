module

public import CFSG.LargeExtraspecial.S9TwoB
public import CFSG.LargeExtraspecial.S9TwoC
public import CFSG.LargeExtraspecial.S9GenG
public import CFSG.LargeExtraspecial.S9GenA
public import CFSG.LargeExtraspecial.S9TwoN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

@[expose] def Timmesfeld92Step5Residual : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} → S5.Irr S →
    ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
      (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g), A6Case H C ht ht1 hVQ →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
        (∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) →
        ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem conj_eq_t_a6 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hA6 : A6Case H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O}
    (hxM : x ∈ S.Mbar) (hxL : x * t * x⁻¹ ∈ S.Lbar g) : x * t * x⁻¹ = t := by
  have hstr : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, ∀ y : S.O, y * α * y⁻¹ ∈ S.Lbar g →
      y * α * y⁻¹ ∈ Nbar S g t :=
    fun α hα y hyL => conj_mem_Nbar_a6 hCE H hNo C ht ht1 hVQ hA6 hA hα hyL
  obtain ⟨n, hnM, hnL, hτ⟩ := exists_normalizer_conj_eq H C ht ⟨hxL, x, hxM, rfl⟩
  have hnA : n ∈ normalizer ((S.Lbar g ⊓ Nbar S g t : Subgroup S.O) : Set S.O) := by
    rw [mem_normalizer_iff]
    intro a
    have hL := (mem_normalizer_iff.mp hnL) a
    constructor
    · intro ha
      have ha' : a ∈ S.Lbar g ⊓ Nbar S g t := ha
      have h1 : n * a * n⁻¹ ∈ S.Lbar g := hL.mp (mem_inf.mp ha').1
      exact mem_inf.mpr ⟨h1, hstr a ha' n h1⟩
    · intro ha
      have ha' : n * a * n⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := ha
      have h1 : a ∈ S.Lbar g := hL.mpr (mem_inf.mp ha').1
      have e : n⁻¹ * (n * a * n⁻¹) * n⁻¹⁻¹ = a := by group
      have h2 := hstr _ ha' n⁻¹ (by rw [e]; exact h1)
      rw [e] at h2
      exact mem_inf.mpr ⟨h1, h2⟩
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hcard : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width := by
    have h1 := card_Abar_mul_four_a6 hCE H hNo C ht ht1 hVQ hA6
    have hn := four_lt_width_a6 hCE H hNo C ht ht1 hVQ hA6 hA
    obtain ⟨k, hk⟩ : ∃ k, S.width = k + 1 := ⟨S.width - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel] at h1
    rw [hA6.finrank_eq, hk]
    calc Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 2 ^ (4 - 1) =
        Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 4 * 2 := by ring
      _ = 2 ^ (k + 1) := by rw [h1, pow_succ]
  have hnt := conj_eq_of_normalizer_Abar_of H hNo C ht ht1 hVQ hh hb hcard
    (radBound_of_tau_not_mem H C ht ht1 hVQ hA6.tau_not_mem) hnM hnL hnA
  rw [hτ, hnt]

theorem eq_t_of_step5 (hR5 : Timmesfeld92Step5Residual.{u}) (hCE : CentralExtInput.{u})
    (hIrr : S5.Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hA6 : A6Case H C ht ht1 hVQ)
    (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
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
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hA6.transitive hL hxM hβ
  have hW := hR5 hCE hIrr H hNo C ht ht1 hVQ hA6 hA hR x hxM hτt hβ
  refine false_of_fix_clSub_inf_Wt H C ht ht1 hVQ hxM hτt hinf fun w hw => ?_
  have h1 := hW w (Submodule.mem_inf.mp hw).2
  have h2 : ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
      Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Submodule.mem_inf.mpr ⟨h1, sub_mem_commSpace _ w⟩
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at h2
  exact h2

theorem timmesfeld_9_2 (hR5 : Timmesfeld92Step5Residual.{u}) (hCE : CentralExtInput.{u})
    (hIrr : S5.Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : ¬ A6Case H C ht ht1 hVQ := by
  intro hA6
  have hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t :=
    fun x hxM hxL => conj_eq_t_a6 hCE H hNo C ht ht1 hVQ hA6 hA hxM hxL
  have hiso : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t :=
    fun x hxM hτt => eq_t_of_step5 hR5 hCE hIrr H hNo C ht ht1 hVQ hA6 hA hR hxM hτt
  exact hA (Lbar_inf_Nbar_eq_zpowers_of_isolated H hNo C
    (four_lt_width_a6 hCE H hNo C ht ht1 hVQ hA6 hA) ht ht1 hiso)

end CFSG.LargeExtraspecial.S9
