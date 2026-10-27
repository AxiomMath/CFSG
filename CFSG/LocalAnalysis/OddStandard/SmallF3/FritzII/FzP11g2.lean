module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11b
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AS81
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {T R Y : Subgroup G}

private theorem mem_fzBar_of_mem {A : Subgroup G} {x : ↥(centralizer ({z} : Set G))}
    (hx : (x : G) ∈ A) :
    QuotientGroup.mk' (zpowers (zC z)) x ∈ fzBar z A := by
  show QuotientGroup.mk' (zpowers (zC z)) x ∈
    (A.subgroupOf (centralizer ({z} : Set G))).map (QuotientGroup.mk' (zpowers (zC z)))
  exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

private theorem fz_commutator_mul_mul {y₁ r₁ y₂ r₂ : G}
    (h₁₁ : Commute y₁ r₁) (h₁₂ : Commute y₁ r₂)
    (h₂₁ : Commute y₂ r₁) (h₂₂ : Commute y₂ r₂) :
    ⁅y₁ * r₁, y₂ * r₂⁆ = ⁅y₁, y₂⁆ * ⁅r₁, r₂⁆ := by
  set d := ⁅r₁, r₂⁆ with hd
  have h3 : Commute y₁ d := by
    rw [hd, commutatorElement_def]
    exact ((h₁₁.mul_right h₁₂).mul_right h₁₁.inv_right).mul_right h₁₂.inv_right
  have h4 : Commute y₂ d := by
    rw [hd, commutatorElement_def]
    exact ((h₂₁.mul_right h₂₂).mul_right h₂₁.inv_right).mul_right h₂₂.inv_right
  have k1 : r₁ * y₂ * r₁⁻¹ = y₂ := by rw [h₂₁.eq.symm]; group
  have k2 : r₁ * r₂ * r₁⁻¹ = d * r₂ := by rw [hd, commutatorElement_def]; group
  have k3 : y₁ * d * y₁⁻¹ = d := by rw [h3.eq]; group
  have k4 : y₁ * r₂ * y₁⁻¹ = r₂ := by rw [h₁₂.eq]; group
  have k5 : d * y₂⁻¹ = y₂⁻¹ * d := (h4.symm.inv_right).eq
  calc ⁅y₁ * r₁, y₂ * r₂⁆
      = y₁ * ((r₁ * y₂ * r₁⁻¹) * (r₁ * r₂ * r₁⁻¹)) * y₁⁻¹ * r₂⁻¹ * y₂⁻¹ := by
        rw [commutatorElement_def]; group
    _ = (y₁ * y₂ * y₁⁻¹) * (y₁ * d * y₁⁻¹) * (y₁ * r₂ * y₁⁻¹)
          * r₂⁻¹ * y₂⁻¹ := by rw [k1, k2]; group
    _ = (y₁ * y₂ * y₁⁻¹) * (d * y₂⁻¹) := by rw [k3, k4]; group
    _ = ⁅y₁, y₂⁆ * d := by rw [k5, commutatorElement_def]; group

private theorem fz_mem_sup_of_commute {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hz
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have hba : b * a' = a' * b := (hc a' ha' b hb).eq.symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hba]
      _ = a * a' * (b * b') := by group
  | inv y _ hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have hba : b * a = a * b := (hc a ha b hb).eq.symm
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hba]

private theorem fz_commutator_le_sup (hzR : z ∈ R) (hTYR : T = Y ⊔ R)
    (hYR : Y ≤ centralizer (R : Set G))
    (hRq : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ zpowers z) :
    ⁅T, T⁆ ≤ Y ⊔ zpowers z := by
  rw [hTYR, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hcomm : ∀ y ∈ Y, ∀ r ∈ R, Commute y r := fun y hy r hr =>
    (mem_centralizer_iff.mp (hYR hy) r hr).symm
  obtain ⟨y₁, hy₁, r₁, hr₁, hg₁eq⟩ := fz_mem_sup_of_commute hcomm hg₁
  obtain ⟨y₂, hy₂, r₂, hr₂, hg₂eq⟩ := fz_mem_sup_of_commute hcomm hg₂
  subst g₁
  subst g₂
  have h₁₁ : Commute y₁ r₁ := (mem_centralizer_iff.mp (hYR hy₁) r₁ hr₁).symm
  have h₁₂ : Commute y₁ r₂ := (mem_centralizer_iff.mp (hYR hy₁) r₂ hr₂).symm
  have h₂₁ : Commute y₂ r₁ := (mem_centralizer_iff.mp (hYR hy₂) r₁ hr₁).symm
  have h₂₂ : Commute y₂ r₂ := (mem_centralizer_iff.mp (hYR hy₂) r₂ hr₂).symm
  rw [fz_commutator_mul_mul h₁₁ h₁₂ h₂₁ h₂₂]
  exact Subgroup.mul_mem_sup
    ((Subgroup.commutator_le_of_le (le_refl Y) (le_refl Y))
      (Subgroup.commutator_mem_commutator hy₁ hy₂))
    (hRq r₁ hr₁ r₂ hr₂)

theorem fz_bar_le (hRT : R ≤ T) : fzBar z R ≤ fzBar z T := by
  exact Subgroup.map_mono (f := QuotientGroup.mk' (zpowers (zC z)))
    (Subgroup.subgroupOf_mono (centralizer ({z} : Set G)) hRT)

theorem fz_bar_strong (hzR : z ∈ R) (hRT : R ≤ T) (hTz : T ≤ centralizer ({z} : Set G))
    (hcl : ∀ a ∈ R, ∀ g ∈ centralizer ({z} : Set G), g * a * g⁻¹ ∈ T → g * a * g⁻¹ ∈ R) :
    ∀ t ∈ fzBar z R, ∀ g : FzCbar z, g⁻¹ * t * g ∈ fzBar z T → g⁻¹ * t * g ∈ fzBar z R := by
  intro t ht g hg
  obtain ⟨r, hr, hr_eq⟩ := Subgroup.mem_map.mp ht
  have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (zpowers (zC z)) g
  rw [← hr_eq] at hg ⊢
  have hg' : QuotientGroup.mk' (zpowers (zC z)) (c⁻¹ * r * c) ∈ fzBar z T := by
    simpa using hg
  obtain ⟨s, hs, hs_eq⟩ := Subgroup.mem_map.mp hg'
  have hsT : (s : G) ∈ T := Subgroup.mem_subgroupOf.mp hs
  have hds : (c⁻¹ * r * c) / s ∈ zpowers (zC z) :=
    QuotientGroup.eq_iff_div_mem.mp hs_eq.symm
  have hdsG : (((c⁻¹ * r * c) / s : ↥(centralizer ({z} : Set G))) : G) ∈ zpowers z :=
    mem_zpowers_zC.mp hds
  have hzR' : zpowers z ≤ R := Subgroup.zpowers_le.mpr hzR
  have hdT : (((c⁻¹ * r * c) / s : ↥(centralizer ({z} : Set G))) : G) ∈ T :=
    (hzR'.trans hRT) hdsG
  have haT : ((c⁻¹ * r * c : ↥(centralizer ({z} : Set G))) : G) ∈ T := by
    have h1 : ((c⁻¹ * r * c : ↥(centralizer ({z} : Set G))) : G)
        = (((c⁻¹ * r * c) / s : ↥(centralizer ({z} : Set G))) : G) * (s : G) := by
      rw [div_eq_mul_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact T.mul_mem hdT hsT
  have hcC : ((c⁻¹ : ↥(centralizer ({z} : Set G))) : G) ∈ centralizer ({z} : Set G) :=
    (c⁻¹).2
  have h2 : ((c⁻¹ : ↥(centralizer ({z} : Set G))) : G) * (r : G)
      * ((c⁻¹ : ↥(centralizer ({z} : Set G))) : G)⁻¹
      = ((c⁻¹ * r * c : ↥(centralizer ({z} : Set G))) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hconjT : ((c⁻¹ : ↥(centralizer ({z} : Set G))) : G) * (r : G)
      * ((c⁻¹ : ↥(centralizer ({z} : Set G))) : G)⁻¹ ∈ T := by
    rw [h2]; exact haT
  have haR : ((c⁻¹ * r * c : ↥(centralizer ({z} : Set G))) : G) ∈ R := by
    rw [← h2]
    exact hcl (r : G) hrR (((c⁻¹ : ↥(centralizer ({z} : Set G))) : G)) hcC hconjT
  simpa using mem_fzBar_of_mem (z := z) (A := R) (x := c⁻¹ * r * c) haR

theorem fz_weak_of_strong {X : Type} [Group X] [Finite X] {S Q : Subgroup X}
    (hsc : ∀ t ∈ Q, ∀ g : X, g⁻¹ * t * g ∈ S → g⁻¹ * t * g ∈ Q) :
    ∀ g : X, rightConjugate Q g ≤ S → rightConjugate Q g = Q := by
  intro g hg
  have hle : rightConjugate Q g ≤ Q := by
    intro x hx
    have hxQ : g * x * g⁻¹ ∈ Q := (mem_rightConjugate_iff Q g x).mp hx
    have hxS : g⁻¹ * (g * x * g⁻¹) * g ∈ S := by
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hg hx
    have hxQ' := hsc (g * x * g⁻¹) hxQ g hxS
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hxQ'
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])

theorem fz_bar_comm (hzR : z ∈ R) (hRT : R ≤ T) (hTz : T ≤ centralizer ({z} : Set G))
    (hRq : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ zpowers z) (hTYR : T = Y ⊔ R)
    (hYR : Y ≤ centralizer (R : Set G)) (hYRz : Y ⊓ R ≤ zpowers z) :
    fzBar z R ⊓ ⁅fzBar z T, fzBar z T⁆ = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, hr_eq⟩ := Subgroup.mem_map.mp hu.1
  have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hbarT : fzBar z T = (T.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (zpowers (zC z))) := rfl
  rw [hbarT, ← Subgroup.map_commutator] at hu
  obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp hu.2
  have hrc : QuotientGroup.mk' (zpowers (zC z)) r
      = QuotientGroup.mk' (zpowers (zC z)) c := hr_eq.trans hc_eq.symm
  have hdv : r / c ∈ zpowers (zC z) := QuotientGroup.eq_iff_div_mem.mp hrc
  have hdvG : (((r / c : ↥(centralizer ({z} : Set G))) : G)) ∈ zpowers z :=
    mem_zpowers_zC.mp hdv
  have hzR' : zpowers z ≤ R := Subgroup.zpowers_le.mpr hzR
  have hcR : (c : G) ∈ R := by
    have h1 : (c : G)
        = (((r / c : ↥(centralizer ({z} : Set G))) : G))⁻¹ * (r : G) := by
      rw [div_eq_mul_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact R.mul_mem (R.inv_mem (hzR' hdvG)) hrR
  have hcComm : (c : G) ∈ ⁅T, T⁆ := by
    have hmap : (⁅T.subgroupOf (centralizer ({z} : Set G)),
        T.subgroupOf (centralizer ({z} : Set G))⁆).map
        (centralizer ({z} : Set G)).subtype = ⁅T, T⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTz]
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
  have hcYs : (c : G) ∈ Y ⊔ zpowers z :=
    fz_commutator_le_sup hzR hTYR hYR hRq hcComm
  have hcommz : ∀ y ∈ Y, ∀ w ∈ zpowers z, Commute y w := fun y hy w hw =>
    (mem_centralizer_iff.mp (hYR hy) w (hzR' hw)).symm
  obtain ⟨y, hy, w, hw, hyw⟩ := fz_mem_sup_of_commute hcommz hcYs
  have hyR : y ∈ R := by
    have h2 : y = (c : G) * w⁻¹ := by rw [hyw]; group
    rw [h2]
    exact R.mul_mem hcR (R.inv_mem (hzR' hw))
  have hyz : y ∈ zpowers z := hYRz (Subgroup.mem_inf.mpr ⟨hy, hyR⟩)
  have hcz : (c : G) ∈ zpowers z := by
    rw [hyw]
    exact (zpowers z).mul_mem hyz hw
  have hcN : c ∈ zpowers (zC z) := mem_zpowers_zC.mpr hcz
  have hc1 : QuotientGroup.mk' (zpowers (zC z)) c = 1 :=
    (QuotientGroup.eq_one_iff c).mpr hcN
  rw [← hc_eq, hc1]

end CFSG.OddStandard.SmallF3.FritzII
