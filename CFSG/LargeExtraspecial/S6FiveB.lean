module

public import CFSG.LargeExtraspecial.S6Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

section Abstract

variable {X : Type*} [Group X] {A B Z : Subgroup X}

theorem comm_mem_of_le_sup (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hZ : ∀ x ∈ A ⊔ B, ∀ z ∈ Z, x * z = z * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  let K : X → Subgroup X := fun c =>
    { carrier := {x | x ∈ A ⊔ B ∧ x * c * x⁻¹ * c⁻¹ ∈ Z}
      mul_mem' := by
        rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
        refine ⟨mul_mem hx hy, ?_⟩
        have e : x * y * c * (x * y)⁻¹ * c⁻¹ =
            x * (y * c * y⁻¹ * c⁻¹) * x⁻¹ * (x * c * x⁻¹ * c⁻¹) := by group
        rw [e, show x * (y * c * y⁻¹ * c⁻¹) * x⁻¹ = y * c * y⁻¹ * c⁻¹ by
          rw [hZ x hx _ hyc]; group]
        exact mul_mem hyc hxc
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hxc⟩
        refine ⟨inv_mem hx, ?_⟩
        have e : x⁻¹ * c * x⁻¹⁻¹ * c⁻¹ = x⁻¹ * (x * c * x⁻¹ * c⁻¹)⁻¹ * x := by group
        rw [e, show x⁻¹ * (x * c * x⁻¹ * c⁻¹)⁻¹ * x = (x * c * x⁻¹ * c⁻¹)⁻¹ by
          rw [hZ x⁻¹ (inv_mem hx) _ (inv_mem hxc)]; group]
        exact inv_mem hxc }
  have hK : ∀ c, (A ≤ K c) → (B ≤ K c) → ∀ x ∈ A ⊔ B, x * c * x⁻¹ * c⁻¹ ∈ Z :=
    fun c h1 h2 x hx => ((sup_le h1 h2 : A ⊔ B ≤ K c) hx).2
  have ha : ∀ a ∈ A, ∀ x ∈ A ⊔ B, x * a * x⁻¹ * a⁻¹ ∈ Z := by
    intro a ha
    refine hK a (fun x hx => ⟨mem_sup_left hx, ?_⟩) (fun x hx => ⟨mem_sup_right hx, ?_⟩)
    · rw [hA x hx a ha]; simp [one_mem]
    · have := inv_mem (hAB a ha x hx)
      rwa [show (a * x * a⁻¹ * x⁻¹)⁻¹ = x * a * x⁻¹ * a⁻¹ by group] at this
  have hb : ∀ b ∈ B, ∀ x ∈ A ⊔ B, x * b * x⁻¹ * b⁻¹ ∈ Z := by
    intro b hb
    refine hK b (fun x hx => ⟨mem_sup_left hx, hAB x hx b hb⟩)
      (fun x hx => ⟨mem_sup_right hx, ?_⟩)
    rw [hB x hx b hb]; simp [one_mem]
  let L : Subgroup X :=
    { carrier := {c | c ∈ A ⊔ B ∧ ∀ x ∈ A ⊔ B, x * c * x⁻¹ * c⁻¹ ∈ Z}
      mul_mem' := by
        rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
        refine ⟨mul_mem hc hd, fun x hx => ?_⟩
        have e : x * (c * d) * x⁻¹ * (c * d)⁻¹ =
            (x * c * x⁻¹ * c⁻¹) * (c * (x * d * x⁻¹ * d⁻¹) * c⁻¹) := by group
        rw [e, show c * (x * d * x⁻¹ * d⁻¹) * c⁻¹ = x * d * x⁻¹ * d⁻¹ by
          rw [hZ c hc _ (hd' x hx)]; group]
        exact mul_mem (hc' x hx) (hd' x hx)
      one_mem' := ⟨one_mem _, fun x _ => by simp [one_mem]⟩
      inv_mem' := by
        rintro c ⟨hc, hc'⟩
        refine ⟨inv_mem hc, fun x hx => ?_⟩
        have e : x * c⁻¹ * x⁻¹ * c⁻¹⁻¹ = c⁻¹ * (x * c * x⁻¹ * c⁻¹)⁻¹ * c := by group
        rw [e, show c⁻¹ * (x * c * x⁻¹ * c⁻¹)⁻¹ * c = (x * c * x⁻¹ * c⁻¹)⁻¹ by
          rw [hZ c⁻¹ (inv_mem hc) _ (inv_mem (hc' x hx))]; group]
        exact inv_mem (hc' x hx) }
  have hL : A ⊔ B ≤ L := sup_le (fun a haA => ⟨mem_sup_left haA, ha a haA⟩)
    (fun b hbB => ⟨mem_sup_right hbB, hb b hbB⟩)
  exact fun x hx y hy => (hL hy).2 x hx

theorem sq_mem_of_le_sup (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hZ : ∀ x ∈ A ⊔ B, ∀ z ∈ Z, x * z = z * x) (hA2 : ∀ x ∈ A, x * x = 1)
    (hB2 : ∀ x ∈ B, x * x = 1) : ∀ x ∈ A ⊔ B, x * x ∈ Z := by
  have hc := comm_mem_of_le_sup hA hB hAB hZ
  let K : Subgroup X :=
    { carrier := {x | x ∈ A ⊔ B ∧ x * x ∈ Z}
      mul_mem' := by
        rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
        refine ⟨mul_mem hx hy, ?_⟩
        have hyx := hc y hy x hx
        have e : x * y * (x * y) = (y * x * y⁻¹ * x⁻¹) * (x * x) * (y * y) := by
          rw [show (y * x * y⁻¹ * x⁻¹) * (x * x) * (y * y) =
            x * (x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x) * x * (y * y) by group,
            show x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x = y * x * y⁻¹ * x⁻¹ by
              rw [hZ x⁻¹ (inv_mem hx) _ hyx]; group]
          group
        rw [e]
        exact mul_mem (mul_mem hyx hxx) hyy
      one_mem' := ⟨one_mem _, by simp [one_mem]⟩
      inv_mem' := by
        rintro x ⟨hx, hxx⟩
        refine ⟨inv_mem hx, ?_⟩
        rw [show x⁻¹ * x⁻¹ = (x * x)⁻¹ by group]
        exact inv_mem hxx }
  have hK : A ⊔ B ≤ K :=
    sup_le (fun a haA => ⟨mem_sup_left haA, by rw [hA2 a haA]; exact one_mem _⟩)
    (fun b hbB => ⟨mem_sup_right hbB, by rw [hB2 b hbB]; exact one_mem _⟩)
  exact fun x hx => (hK hx).2

end Abstract

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_center_t (H : Hyp4 S g) {t x : S.O} (hx : x ∈ Rbar S g t) {y : S.O}
    (hy : y ∈ zpowers t) : x * y = y * x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact Commute.zpow_right (commute_of_mem_Rbar H.conj_mem hx) k

section Five

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
  (hk' : S.ρ k' ∈ Rbar S g t)
  (hgen : Rbar S g t ≤ (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t)
  (hN0 : Nbar S g t = N0bar S g t)
include H C ht ht1 hVQ hk hk' hgen hN0

theorem timmesfeld_6_5_comm :
    ∀ x ∈ Nbar S g t, ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have hN := (timmesfeld_6_5_N H ht hk hk' hgen hN0).1
  have hinf := timmesfeld_6_5_inf H ht hk hk' hgen hN0 C ht1 hVQ
  rw [hN]
  refine comm_mem_of_le_sup (fun x hx y hy => Lbar_comm S (H.mul k).conj_mem hx.1 hy.1)
    (fun x hx y hy => Lbar_comm S (H.mul k').conj_mem hx.1 hy.1) (fun x hx y hy => ?_)
    (fun x hx z hz => mem_center_t H (Nbar_le_Rbar (hN ▸ hx)) hz)
  rw [← hinf]
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp
    (comm_mem_Lbar_inf_Nbar H (Lbar_mul_mem_Dset htk) hx.1 hy.2)).1, ?_⟩
  have := (Subgroup.mem_inf.mp (comm_mem_Lbar_inf_Nbar H (Lbar_mul_mem_Dset htk') hy.1 hx.2)).1
  have := inv_mem this
  rwa [show (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at this

theorem timmesfeld_6_5_sq : ∀ x ∈ Nbar S g t, x * x ∈ zpowers t := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have hN := (timmesfeld_6_5_N H ht hk hk' hgen hN0).1
  have hinf := timmesfeld_6_5_inf H ht hk hk' hgen hN0 C ht1 hVQ
  rw [hN]
  refine sq_mem_of_le_sup (fun x hx y hy => Lbar_comm S (H.mul k).conj_mem hx.1 hy.1)
    (fun x hx y hy => Lbar_comm S (H.mul k').conj_mem hx.1 hy.1) (fun x hx y hy => ?_)
    (fun x hx z hz => mem_center_t H (Nbar_le_Rbar (hN ▸ hx)) hz)
    (fun x hx => mul_self_of_mem_Lbar S (H.mul k).conj_mem hx.1)
    (fun x hx => mul_self_of_mem_Lbar S (H.mul k').conj_mem hx.1)
  rw [← hinf]
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp
    (comm_mem_Lbar_inf_Nbar H (Lbar_mul_mem_Dset htk) hx.1 hy.2)).1, ?_⟩
  have := (Subgroup.mem_inf.mp (comm_mem_Lbar_inf_Nbar H (Lbar_mul_mem_Dset htk') hy.1 hx.2)).1
  have := inv_mem this
  rwa [show (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at this

end Five

end CFSG.LargeExtraspecial.S6
