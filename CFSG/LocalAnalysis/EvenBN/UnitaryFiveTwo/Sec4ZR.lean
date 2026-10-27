module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4W
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA1
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement

@[expose] def Data.z {G : Type} [Group G] (d : Data G) : G := d.ι zSU

@[expose] def Data.ZR {G : Type} [Group G] (d : Data G) : Subgroup G := d.withT d.ZX₄

theorem fld_mem_A₁sub {a : SU52} (ha : a ∈ A₁sub) : fld a ∈ A₁sub := by
  have hle : A₁sub ≤ A₁sub.comap fld.toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx
    · exact X₂sub_le_A₁sub (fld_mem_X₂ hx)
    · exact X₃sub_le_A₁sub (fld_mem_X₃ hx)
    · exact X₄sub_le_A₁sub' (fld_mem_X₄ hx)
  exact hle ha

theorem eq_one_or_eq_zSU {a : SU52} (ha : a ∈ ZX₄sub) : a = 1 ∨ a = zSU := by
  obtain ⟨α, β, hα, hm⟩ := mem_x₄Sub.1 ha
  subst hα
  rcases eq_zero_or_one_of_valid β (x₄_coord_rel hm) with rfl | rfl
  · exact Or.inl (ext_mat (by rw [hm, x₄Mat_zero, mat_one]))
  · exact Or.inr (ext_mat hm)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem z_mem_ZX₄ : d.z ∈ d.ZX₄ := ⟨zSU, zSU_mem, rfl⟩

omit [Finite G] in
theorem eq_one_or_eq_z {a : G} (ha : a ∈ d.ZX₄) : a = 1 ∨ a = d.z := by
  obtain ⟨α, hα, rfl⟩ := ha
  rcases eq_one_or_eq_zSU hα with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

omit [Finite G] in
theorem z_ne_one : d.z ≠ 1 := fun e =>
  zSU_ne_one (d.ι_injective (by rw [map_one]; exact e))

theorem eq_one_or_eq_t (h : d.Hyp) {c : G} (hc : c ∈ zpowers d.t) : c = 1 ∨ c = d.t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  rw [← zpow_mod_orderOf, h.t_two]
  have : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
  rcases this with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem act_mem_A₁sub_of_comm_z (h : d.Hyp) {x : d.H} (hx : (x : G) * d.z = d.z * x)
    {a : SU52} (ha : a ∈ A₁sub) : h.act x a ∈ A₁sub := by
  have hz : h.act x zSU = zSU := d.ι_injective (by
    rw [h.ι_act_apply, show d.ι zSU = d.z from rfl, hx, mul_inv_cancel_right])
  obtain ⟨s, hs | hs⟩ := exists_eq_conj_or_eq_conj_mul_fld (h.act x)
  · rw [hs, MulAut.conj_apply] at hz ⊢
    have hsz : s * zSU = zSU * s := by
      calc s * zSU = s * zSU * s⁻¹ * s := by group
        _ = zSU * s := by rw [hz]
    exact conj_mem_A₁sub_of_comm_z hsz ha
  · rw [hs, MulAut.mul_apply, fld_zSU, MulAut.conj_apply] at hz
    rw [hs, MulAut.mul_apply, MulAut.conj_apply]
    have hsz : s * zSU = zSU * s := by
      calc s * zSU = s * zSU * s⁻¹ * s := by group
        _ = zSU * s := by rw [hz]
    exact conj_mem_A₁sub_of_comm_z hsz (fld_mem_A₁sub ha)

theorem conj_mem_A₁_of_comm_z (h : d.Hyp) {x : G} (hxH : x ∈ d.H) (hx : x * d.z = d.z * x)
    {a : G} (ha : a ∈ d.A₁) : x * a * x⁻¹ ∈ d.A₁ := by
  obtain ⟨α, hα, rfl⟩ := ha
  exact ⟨_, h.act_mem_A₁sub_of_comm_z (x := ⟨x, hxH⟩) hx hα, h.ι_act_apply _ _⟩

theorem mem_ZR_of_comm_A₁
    (h : d.Hyp) {x : G} (hxH : x ∈ d.H)
    (hx : ∀ a ∈ d.A₁, x * a = a * x) : x ∈ d.ZR := by
  have hfix : ∀ a ∈ A₁sub, h.act ⟨x, hxH⟩ a = a := fun a ha => d.ι_injective (by
    rw [h.ι_act_apply]
    change x * d.ι a * x⁻¹ = d.ι a
    rw [hx _ ⟨a, ha, rfl⟩, mul_inv_cancel_right])
  obtain ⟨s, hs | hs⟩ := exists_eq_conj_or_eq_conj_mul_fld (h.act ⟨x, hxH⟩)
  · have hsA : ∀ a ∈ A₁sub, s * a = a * s := fun a ha => by
      have e := hfix a ha
      rw [hs, MulAut.conj_apply] at e
      calc s * a = s * a * s⁻¹ * s := by group
        _ = a * s := by rw [e]
    have hsZ := mem_ZX₄sub_of_comm_A₁ hsA
    obtain ⟨c, hc, e⟩ := exists_eq_mul_of_act_eq_conj d.L d.η ⟨x, h.H_le_normalizer hxH⟩ s hs
    change x = d.ι s * c at e
    have hcH : c ∈ d.H := by
      have := mul_mem (inv_mem (h.L_le_H (d.ι_mem s))) hxH
      rwa [e, inv_mul_cancel_left] at this
    have hct : c ∈ zpowers d.t := by
      rw [← h.centralizer_inf_H_eq]
      exact Subgroup.mem_inf.2 ⟨hc, hcH⟩
    rw [e]
    exact mul_mem (mem_sup_left ⟨s, hsZ, rfl⟩) (mem_sup_right hct)
  · exfalso
    refine not_conj_fld_fix s fun a ha => ?_
    have e := hfix a ha
    rwa [hs, MulAut.mul_apply, MulAut.conj_apply] at e

theorem exists_eq_mul_of_mem_ZR (h : d.Hyp) {y : G} (hy : y ∈ d.ZR) :
    ∃ a ∈ d.ZX₄, ∃ c ∈ zpowers d.t, a * c = y :=
  CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (fun a ha c hc => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    exact (Commute.zpow_right (h.t_comm_F (d.ZX₄_le_F ha)) k).eq) hy

theorem W_crossed_mem_ZX₄
    (h : d.Hyp) {w : G}
    (hw : w ∈ d.W) : w⁻¹ * d.t * w * d.t ∈ d.ZX₄ := by
  have hU : w ∈ d.U := h.E₂_le_U (h.Y_eq_E₂ ▸ d.W_le_Y hw)
  obtain ⟨ξ, hξ, e⟩ := h.U_crossed_mem_F hU
  have hc : ∀ c : F4, ξ * x₂SU c = x₂SU c * ξ := fun c => d.ι_injective (by
    have hyc := mem_centralizer_iff.1 (d.W_le_centralizer hw) _ (d.ι_x₂SU_mem_S c)
    have hcomm := crossed_conj (x := w) (h := d.ι (x₂SU c))
      (h.Lev_comm_t (X₂_le_Lev ⟨x₂SU c, x₂SU_mem c, rfl⟩))
    rw [show d.ι (x₂SU c) * w * (d.ι (x₂SU c))⁻¹ = w by rw [hyc, mul_inv_cancel_right],
      ← e] at hcomm
    rw [map_mul, map_mul]
    calc d.ι ξ * d.ι (x₂SU c) = d.ι (x₂SU c) * d.ι ξ * (d.ι (x₂SU c))⁻¹ * d.ι (x₂SU c) := by
          rw [← hcomm]
      _ = d.ι (x₂SU c) * d.ι ξ := by group)
  rw [← e]
  exact ⟨ξ, mem_ZX₄sub_of_comm hξ (hc 1) (hc F4.ω), rfl⟩

theorem W_comm_z
    (h : d.Hyp) {w : G}
    (hw : w ∈ d.W) : w * d.z = d.z * w :=
  h.U_comm_F (h.E₂_le_U (h.Y_eq_E₂ ▸ d.W_le_Y hw)) (d.ZX₄_le_F z_mem_ZX₄)

theorem conj_of_mem_normalizer_ZR
    (h : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.ZR : Set G)) :
    g⁻¹ * d.t * g * d.t ∈ d.ZX₄ ∧ g * d.z = d.z * g := by
  have htZ : d.t ∈ d.ZR := mem_sup_right (mem_zpowers _)
  have hzZ : d.z ∈ d.ZR := mem_sup_left z_mem_ZX₄
  refine ⟨?_, ?_⟩
  · have hm : g⁻¹ * d.t * g⁻¹⁻¹ ∈ d.ZR := (mem_normalizer_iff.1 (inv_mem hg) _).1 htZ
    rw [inv_inv] at hm
    obtain ⟨a, ha, c, hc, e⟩ := h.exists_eq_mul_of_mem_ZR hm
    rcases h.eq_one_or_eq_t hc with rfl | rfl
    · exfalso
      rw [mul_one] at e
      exact h.conj_t_not_mem_L g (e ▸ h.F_le_L (d.ZX₄_le_F ha))
    · rw [← e, mul_assoc, h.t_mul_t, mul_one]
      exact ha
  · have hm : g * d.z * g⁻¹ ∈ d.ZR := (mem_normalizer_iff.1 hg _).1 hzZ
    obtain ⟨a, ha, c, hc, e⟩ := h.exists_eq_mul_of_mem_ZR hm
    rcases h.eq_one_or_eq_t hc with rfl | rfl
    · rw [mul_one] at e
      rcases eq_one_or_eq_z ha with rfl | rfl
      · exfalso
        apply z_ne_one (d := d)
        calc d.z = g⁻¹ * (g * d.z * g⁻¹) * g := by group
          _ = 1 := by rw [← e]; group
      · calc g * d.z = g * d.z * g⁻¹ * g := by group
          _ = d.z * g := by rw [← e]
    · exfalso
      obtain ⟨w, -, hw⟩ := (h.sec4_9_W).2.2.1 a ha
      apply h.conj_t_not_mem_L (w * g)
      have hz : (w * g)⁻¹ * d.t * (w * g) = d.z := by
        calc (w * g)⁻¹ * d.t * (w * g) = g⁻¹ * (w⁻¹ * d.t * w) * g := by group
          _ = g⁻¹ * (a * d.t) * g := by rw [hw]
          _ = g⁻¹ * (g * d.z * g⁻¹) * g := by rw [e]
          _ = d.z := by group
      rw [hz]
      exact h.F_le_L (d.ZX₄_le_F z_mem_ZX₄)

theorem mem_normalizer_ZR_of_comm_z (_h : d.Hyp) {x : G} (hxH : x ∈ d.H)
    (hx : x * d.z = d.z * x) : x ∈ normalizer (d.ZR : Set G) := by
  have hle : d.ZR ≤ d.ZR.comap (MulAut.conj x).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro a ha
      rcases eq_one_or_eq_z ha with rfl | rfl
      · exact one_mem _
      · change x * d.z * x⁻¹ ∈ d.ZR
        rw [hx, mul_inv_cancel_right]
        exact mem_sup_left z_mem_ZX₄
    · rw [zpowers_le]
      change x * d.t * x⁻¹ ∈ d.ZR
      rw [show x * d.t = d.t * x from mem_centralizer_singleton_iff.1 hxH,
        mul_inv_cancel_right]
      exact mem_sup_right (mem_zpowers _)
  exact mem_normalizer_fintype fun y hy => hle hy

theorem mem_normalizer_ZR_of_mem_W
    (h : d.Hyp) {w : G} (hw : w ∈ d.W) :
    w ∈ normalizer (d.ZR : Set G) := by
  have hle : d.ZR ≤ d.ZR.comap (MulAut.conj w).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro a ha
      rcases eq_one_or_eq_z ha with rfl | rfl
      · exact one_mem _
      · change w * d.z * w⁻¹ ∈ d.ZR
        rw [h.W_comm_z hw, mul_inv_cancel_right]
        exact mem_sup_left z_mem_ZX₄
    · rw [zpowers_le]
      change w * d.t * w⁻¹ ∈ d.ZR
      have hc := h.W_crossed_mem_ZX₄ (inv_mem hw)
      rw [inv_inv] at hc
      rw [show w * d.t * w⁻¹ = (w * d.t * w⁻¹ * d.t) * d.t by
        rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
      exact mul_mem (mem_sup_left hc) (mem_sup_right (mem_zpowers _))
  exact mem_normalizer_fintype fun y hy => hle hy

theorem exists_eq_mul_of_mem_normalizer_ZR
    (h : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.ZR : Set G)) :
    ∃ c ∈ d.H, c * d.z = d.z * c ∧ ∃ w ∈ d.W, g = c * w := by
  obtain ⟨ha, hgz⟩ := h.conj_of_mem_normalizer_ZR hg
  obtain ⟨w, hw, hwt⟩ := (h.sec4_9_W).2.2.1 _ ha
  rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one] at hwt
  refine ⟨g * w⁻¹, mem_centralizer_singleton_iff.2 ?_, ?_, w, hw, by group⟩
  · calc g * w⁻¹ * d.t = g * (w⁻¹ * d.t * w) * w⁻¹ := by group
      _ = g * (g⁻¹ * d.t * g) * w⁻¹ := by rw [hwt]
      _ = d.t * (g * w⁻¹) := by group
  · have hwz := h.W_comm_z (inv_mem hw)
    calc g * w⁻¹ * d.z = g * (w⁻¹ * d.z) := by group
      _ = g * (d.z * w⁻¹) := by rw [hwz]
      _ = (g * d.z) * w⁻¹ := by group
      _ = d.z * (g * w⁻¹) := by rw [hgz]; group

theorem card_normalizer_ZR
    (h : d.Hyp) :
    Nat.card (normalizer (d.ZR : Set G)) =
      Nat.card (centralizer ({d.z} : Set G) ⊓ d.H : Subgroup G) * 2 := by
  have hB : (normalizer (d.ZR : Set G)) ≤ centralizer (d.ZX₄ : Set G) := fun g hg =>
    mem_centralizer_iff.2 fun a ha => by
      rcases eq_one_or_eq_z ha with rfl | rfl
      · group
      · exact ((h.conj_of_mem_normalizer_ZR hg).2).symm
  have hY : ∀ y ∈ normalizer (d.ZR : Set G), y⁻¹ * d.t * y * d.t ∈ d.ZX₄ := fun y hy =>
    (h.conj_of_mem_normalizer_ZR hy).1
  have honto : ∀ b ∈ d.ZX₄, ∃ y ∈ normalizer (d.ZR : Set G), y⁻¹ * d.t * y * d.t = b := by
    intro b hb
    obtain ⟨w, hw, e⟩ := (h.sec4_9_W).2.2.1 b hb
    exact ⟨w, h.mem_normalizer_ZR_of_mem_W hw, by rw [e, mul_assoc, h.t_mul_t, mul_one]⟩
  have hset : (normalizer (d.ZR : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) =
      centralizer ({d.z} : Set G) ⊓ d.H := by
    ext x
    constructor
    · rintro ⟨hxN, hxt⟩
      exact ⟨mem_centralizer_singleton_iff.2 (h.conj_of_mem_normalizer_ZR hxN).2, hxt⟩
    · rintro ⟨hxz, hxH⟩
      exact ⟨h.mem_normalizer_ZR_of_comm_z hxH (mem_centralizer_singleton_iff.1 hxz), hxH⟩
  rw [card_eq_of_crossed_onto h.t_mul_t hB hY honto, hset, Data.ZX₄, d.card_pull, card_ZX₄sub]

theorem conj_mem_A₁_of_mem_normalizer_ZR
    (h : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.ZR : Set G)) {a : G} (ha : a ∈ d.A₁) : g * a * g⁻¹ ∈ d.A₁ := by
  obtain ⟨c, hcH, hcz, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_normalizer_ZR hg
  have hwa : w * a * w⁻¹ = a := by
    rw [← mem_centralizer_iff.1 (h.sec4_9_W.2.2.2.2.2 hw) a ha, mul_inv_cancel_right]
  rw [show c * w * a * (c * w)⁻¹ = c * (w * a * w⁻¹) * c⁻¹ by group, hwa]
  exact h.conj_mem_A₁_of_comm_z hcH hcz ha

theorem mem_withT_W_of_comm_A₁
    (h : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.ZR : Set G)) (hgA : ∀ a ∈ d.A₁, g * a = a * g) :
    g ∈ d.withT d.W := by
  obtain ⟨c, hcH, -, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_normalizer_ZR hg
  have hwA : ∀ a ∈ d.A₁, w * a = a * w := fun a ha =>
    (mem_centralizer_iff.1 (h.sec4_9_W.2.2.2.2.2 hw) a ha).symm
  have hcA : ∀ a ∈ d.A₁, c * a = a * c := fun a ha => by
    have e := hgA a ha
    calc c * a = c * w * a * w⁻¹ := by rw [mul_assoc c w a, hwA a ha]; group
      _ = a * (c * w) * w⁻¹ := by rw [e]
      _ = a * c := by group
  obtain ⟨b, hb, e, he, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha c hc => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      exact (Commute.zpow_right (h.t_comm_F (d.ZX₄_le_F ha)) k).eq)
    (h.mem_ZR_of_comm_A₁ hcH hcA)
  have hbW : b ∈ d.W := by
    rw [← h.W_inf_H] at hb
    exact (Subgroup.mem_inf.1 hb).1
  have hwt : e * w * e⁻¹ ∈ d.W := by
    rcases h.eq_one_or_eq_t he with rfl | rfl
    · rw [one_mul, inv_one, mul_one]
      exact hw
    · have hc := h.W_crossed_mem_ZX₄ (inv_mem hw)
      rw [inv_inv] at hc
      have hzW : w * d.t * w⁻¹ * d.t ∈ d.W := by
        rw [← h.W_inf_H] at hc
        exact (Subgroup.mem_inf.1 hc).1
      rw [h.t_inv]
      have : d.t * w * d.t = (w * d.t * w⁻¹ * d.t)⁻¹ * w := by
        rw [show (w * d.t * w⁻¹ * d.t)⁻¹ = d.t⁻¹ * w * d.t⁻¹ * w⁻¹ by group, h.t_inv]
        group
      rw [this]
      exact mul_mem (inv_mem hzW) hw
  rw [show b * e * w = (b * (e * w * e⁻¹)) * e by group]
  exact mul_mem (mem_sup_left (mul_mem hbW hwt)) (mem_sup_right he)

theorem withT_W_le_normalizer_ZR
    (h : d.Hyp) :
    d.withT d.W ≤ normalizer (d.ZR : Set G) :=
  sup_le (fun _ hw => h.mem_normalizer_ZR_of_mem_W hw) ((zpowers_le).2
    (h.mem_normalizer_ZR_of_comm_z h.t_mem_H (comm_of_mem_centralizer h.t_mem (d.ι_mem zSU)).symm))

theorem withT_W_le_centralizer_A₁
    (h : d.Hyp) :
    d.withT d.W ≤ centralizer (d.A₁ : Set G) :=
  sup_le h.sec4_9_W.2.2.2.2.2 ((zpowers_le).2 (mem_centralizer_iff.2 fun _ ha =>
    comm_of_mem_centralizer h.t_mem (d.pull_le_L _ ha)))

theorem conj_mem_withT_W
    (h : d.Hyp) {g : G}
    (hg : g ∈ normalizer (d.ZR : Set G)) {x : G} (hx : x ∈ d.withT d.W) :
    g * x * g⁻¹ ∈ d.withT d.W := by
  refine h.mem_withT_W_of_comm_A₁
    (mul_mem (mul_mem hg (h.withT_W_le_normalizer_ZR hx)) (inv_mem hg)) fun a ha => ?_
  have ha' := h.conj_mem_A₁_of_mem_normalizer_ZR (inv_mem hg) ha
  rw [inv_inv] at ha'
  have hc := mem_centralizer_iff.1 (h.withT_W_le_centralizer_A₁ hx) _ ha'
  calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by rw [← hc]
    _ = a * (g * x * g⁻¹) := by group

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
