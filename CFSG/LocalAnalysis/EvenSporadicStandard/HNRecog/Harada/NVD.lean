module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMASetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NVIndex

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

private lemma add_self_eq_zero_V6 (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma conj_fix_zpowers {a z g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g ∈ zpowers z) : a * g * a⁻¹ = g := by
  have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp ha
  have hza : z ∈ centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr haz.symm
  have hle : zpowers z ≤ centralizer ({a} : Set G) := Subgroup.zpowers_le.mpr hza
  have hcomm : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  rw [← hcomm]
  group

theorem Setting25.t_sq (h : Setting25 G t z z₁ ι zv R0 F) : t ^ 2 = 1 := by
  rw [pow_two, ← h.ι_tv, ← coordElt_add, add_self_eq_zero_V6, coordElt_zero]

theorem Setting25.t_mul_z_comm (h : Setting25 G t z z₁ ι zv R0 F) : t * z = z * t := by
  rw [← h.ι_tv, ← h.coord_z, ← coordElt_add, ← coordElt_add, add_comm]

theorem R0_le_normalizer_V (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) :
    R0 ≤ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) := by
  calc R0 ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := h.hD2.R0_le
    _ = normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) ⊓
          centralizer ({t} : Set G) :=
        (normalizer_V_inf_centralizer_t h.t_sq h.z_sq h.t_mul_z_comm hzt htz).symm
    _ ≤ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) := inf_le_left

theorem R0_conj_of_mem_normalizer_V (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) {n x : G}
    (hn : n ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G)) (hx : x ∈ R0) :
    n * x * n⁻¹ ∈ R0 := by
  let P : Subgroup G := R0.map (MulAut.conj n).toMonoidHom
  have hxP : n * x * n⁻¹ ∈ P := by
    rw [Subgroup.mem_map]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hP_le : P ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    exact conj_mem_centralizer_of_mem_normalizer_V h.t_sq h.z_sq h.t_mul_z_comm hzt htz hn
      (h.hD2.R0_le hr)
  have hP2 : IsPGroup 2 P := by
    refine IsPGroup.of_card (p := 2) (n := 8) ?_
    have hcard : Nat.card P = Nat.card R0 := by
      change Nat.card (R0.map (MulAut.conj n).toMonoidHom) = Nat.card R0
      exact (Nat.card_congr (Subgroup.equivMapOfInjective R0
        (MulAut.conj n).toMonoidHom (MulAut.conj n).injective).toEquiv).symm
    rw [hcard, h.hD2.card_R0]
  have hPnorm : ∀ c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G), ∀ y ∈ P,
      c * y * c⁻¹ ∈ P := by
    intro c hc y hy
    rw [Subgroup.mem_map] at hy ⊢
    obtain ⟨r, hr, rfl⟩ := hy
    have hc' : n⁻¹ * c * n ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
      simpa using conj_mem_centralizer_of_mem_normalizer_V h.t_sq h.z_sq h.t_mul_z_comm hzt htz
        (inv_mem hn) hc
    refine ⟨n⁻¹ * c * n * r * (n⁻¹ * c * n)⁻¹, h.hD2.R0_normal _ hc' r hr, ?_⟩
    change n * (n⁻¹ * c * n * r * (n⁻¹ * c * n)⁻¹) * n⁻¹ = c * (n * r * n⁻¹) * c⁻¹
    group
  exact h.hD2.R0_max P hP_le hP2 hPnorm hxP

@[expose] def Dgrp (t z : G) (R0 : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) ∧
    g ∈ centralizer ({z} : Set G) ∧ ∀ r ∈ R0, g * r * g⁻¹ * r⁻¹ ∈ zpowers z}
  mul_mem' := by
    intro a b ha hb
    refine ⟨mul_mem ha.1 hb.1, mul_mem ha.2.1 hb.2.1, ?_⟩
    intro r hr
    have hb' : b * r * b⁻¹ * r⁻¹ ∈ zpowers z := hb.2.2 r hr
    have ha' : a * r * a⁻¹ * r⁻¹ ∈ zpowers z := ha.2.2 r hr
    have hfix : a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ = b * r * b⁻¹ * r⁻¹ :=
      conj_fix_zpowers ha.2.1 hb'
    rw [show (a * b) * r * (a * b)⁻¹ * r⁻¹ =
        a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ * (a * r * a⁻¹ * r⁻¹) by group, hfix]
    exact mul_mem hb' ha'
  one_mem' := by
    refine ⟨one_mem _, one_mem _, ?_⟩
    intro r _
    have h1 : (1 : G) * r * 1⁻¹ * r⁻¹ = 1 := by group
    rw [h1]
    exact one_mem _
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, inv_mem ha.2.1, ?_⟩
    intro r hr
    have ha' : a * r * a⁻¹ * r⁻¹ ∈ zpowers z := ha.2.2 r hr
    have hmem : (a * r * a⁻¹ * r⁻¹)⁻¹ ∈ zpowers z := inv_mem ha'
    have hfix : a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * (a⁻¹)⁻¹ = (a * r * a⁻¹ * r⁻¹)⁻¹ :=
      conj_fix_zpowers (inv_mem ha.2.1) hmem
    rw [show a⁻¹ * r * (a⁻¹)⁻¹ * r⁻¹ =
        a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * (a⁻¹)⁻¹ by group, hfix]
    exact hmem

theorem mem_Dgrp {g : G} : g ∈ Dgrp t z R0 ↔
    g ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) ∧
      g ∈ centralizer ({z} : Set G) ∧ ∀ r ∈ R0, g * r * g⁻¹ * r⁻¹ ∈ zpowers z := Iff.rfl

theorem Dgrp_conj (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) {n g : G}
    (hn : n ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G)) (hg : g ∈ Dgrp t z R0) :
    n * g * n⁻¹ ∈ Dgrp t z R0 := by
  rw [mem_Dgrp] at hg ⊢
  obtain ⟨hgN, hgC, hgcomm⟩ := hg
  have hnC : n ∈ centralizer ({z} : Set G) :=
    normalizer_V_le_centralizer_z h.t_sq h.z_sq h.t_mul_z_comm hzt htz hn
  refine ⟨mul_mem (mul_mem hn hgN) (inv_mem hn), mul_mem (mul_mem hnC hgC) (inv_mem hnC), ?_⟩
  intro r hr
  have hr' : n⁻¹ * r * n ∈ R0 := by
    simpa using R0_conj_of_mem_normalizer_V h hzt htz (inv_mem hn) hr
  have hgc : g * (n⁻¹ * r * n) * g⁻¹ * (n⁻¹ * r * n)⁻¹ ∈ zpowers z := hgcomm _ hr'
  have hfix : n * (g * (n⁻¹ * r * n) * g⁻¹ * (n⁻¹ * r * n)⁻¹) * n⁻¹ =
      g * (n⁻¹ * r * n) * g⁻¹ * (n⁻¹ * r * n)⁻¹ := conj_fix_zpowers hnC hgc
  rw [show (n * g * n⁻¹) * r * (n * g * n⁻¹)⁻¹ * r⁻¹ =
      n * (g * (n⁻¹ * r * n) * g⁻¹ * (n⁻¹ * r * n)⁻¹) * n⁻¹ by group, hfix]
  exact hgc

theorem Dgrp_inf_C (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) :
    Dgrp t z R0 ⊓ (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) = R0 := by
  apply le_antisymm
  · intro c hc
    rw [Subgroup.mem_inf, mem_Dgrp] at hc
    exact h.hD2.R0_faith c hc.2 (fun x hx => hc.1.2.2 x hx)
  · intro r hr
    rw [Subgroup.mem_inf, mem_Dgrp]
    exact ⟨⟨R0_le_normalizer_V h hzt htz hr,
        (Subgroup.mem_inf.mp (h.hD2.R0_le hr)).2,
        fun x hx => h.hD2.R0_comm r hr x hx⟩,
      h.hD2.R0_le hr⟩

theorem card_Dgrp_le (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) : Nat.card (Dgrp t z R0) ≤ 2 ^ 9 := by
  have hP : Dgrp t z R0 ≤ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) :=
    fun g hg => (mem_Dgrp.mp hg).1
  have hle := card_le_two_mul_card_inf_centralizer_t h.t_sq h.z_sq h.t_mul_z_comm hzt htz hP
  have hDz : Dgrp t z R0 ≤ centralizer ({z} : Set G) := fun g hg => (mem_Dgrp.mp hg).2.1
  have hinf : Dgrp t z R0 ⊓ centralizer ({t} : Set G) =
      Dgrp t z R0 ⊓ (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1, hx.2, hDz hx.1⟩
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
  rw [hinf, Dgrp_inf_C h hzt htz, h.hD2.card_R0] at hle
  calc Nat.card (Dgrp t z R0) ≤ 2 * 2 ^ 8 := hle
    _ = 2 ^ 9 := by norm_num

end CFSG.EvenSporadicStandard.HNRecog.Harada
