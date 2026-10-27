module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65CaseA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Cfg

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

structure AB65 (S K₁ : Subgroup G) (a b : G) : Prop where
  ha : a ∈ Pof S K₁
  hb : b ∈ Pof S K₁
  ha8 : orderOf a = 8
  conj : ∀ y ∈ Pof S K₁, y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a⁻¹
  cent : ∀ y ∈ Pof S K₁, y * a = a * y → y ∈ zpowers a
  binv : b * a * b⁻¹ = a⁻¹
  bsq : b * b = a ^ 4

omit [Finite G] in
theorem a₂_order {a b : G} (hAB : AB65 S K₁ a b) : orderOf (t * a * t⁻¹) = 8 := by
  rw [orderOf_conj_eq'']; exact hAB.ha8

omit [Finite G] in
theorem b₂_inv {a b : G} (hAB : AB65 S K₁ a b) :
    (t * b * t⁻¹) * (t * a * t⁻¹) * (t * b * t⁻¹)⁻¹ = (t * a * t⁻¹)⁻¹ := by
  have e : (t * b * t⁻¹) * (t * a * t⁻¹) * (t * b * t⁻¹)⁻¹ = t * (b * a * b⁻¹) * t⁻¹ := by group
  rw [e, hAB.binv]; group

omit [Finite G] in
theorem a₂_sq_order {a b : G} (hAB : AB65 S K₁ a b) : orderOf ((t * a * t⁻¹) ^ 2) = 4 := by
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [a₂_order hAB]; norm_num), a₂_order hAB]

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t) {a b : G} (hAB : AB65 S K₁ a b)

include h hAB

theorem a_four (hII : II4_4_4_center) : a ^ 4 = z :=
  pow_four_eq_z_of_order_eight h.std hII hAB.ha.2 hAB.ha8

omit hAB in
theorem tz_comm' (hII : II4_4_4_center) : t * z * t⁻¹ = z := by
  have := h.t_comm hII
  calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [this]
    _ = z := by group

theorem a₂_mem : t * a * t⁻¹ ∈ Pof S K₂ := h.t_conj_P₁ hAB.ha

theorem a₂_four (hII : II4_4_4_center) : (t * a * t⁻¹) ^ 4 = z := by
  rw [conj_pow, h.a_four hAB hII, h.tz_comm' hII]

theorem a_comm_a₂ (hII : II4_4_4_center) : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a :=
  h.P_comm hII a hAB.ha _ (h.a₂_mem hAB)

theorem b₂_mem : t * b * t⁻¹ ∈ Pof S K₂ := h.t_conj_P₁ hAB.hb

theorem conj_a₂ {y : G} (hy : y ∈ Pof S K₂) :
    y * (t * a * t⁻¹) * y⁻¹ = t * a * t⁻¹ ∨ y * (t * a * t⁻¹) * y⁻¹ = (t * a * t⁻¹)⁻¹ := by
  have key : ∀ w : G, w * (t * a * t⁻¹) * w⁻¹ = t * ((t⁻¹ * w * t) * a * (t⁻¹ * w * t)⁻¹) * t⁻¹ := by
    intro w; group
  have hy'' : t⁻¹ * y * t ∈ Pof S K₁ := by
    have e : t⁻¹ * y * t = t * y * t⁻¹ := by rw [h.t_inv]
    rw [e]; exact h.t_conj_P₂ hy
  rw [key y]
  rcases hAB.conj _ hy'' with h1 | h1
  · left; rw [h1]
  · right; rw [h1]; group

theorem cent_a₂ {y : G} (hy : y ∈ Pof S K₂) (hc : y * (t * a * t⁻¹) = (t * a * t⁻¹) * y) :
    y ∈ zpowers (t * a * t⁻¹) := by
  have hy'' : t⁻¹ * y * t ∈ Pof S K₁ := by
    have e : t⁻¹ * y * t = t * y * t⁻¹ := by rw [h.t_inv]
    rw [e]; exact h.t_conj_P₂ hy
  have hc' : (t⁻¹ * y * t) * a = a * (t⁻¹ * y * t) := by
    have e1 : (t⁻¹ * y * t) * a = t⁻¹ * (y * (t * a * t⁻¹)) * t := by group
    have e2 : a * (t⁻¹ * y * t) = t⁻¹ * ((t * a * t⁻¹) * y) * t := by group
    rw [e1, e2, hc]
  have := hAB.cent _ hy'' hc'
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  rw [conj_zpow, hn]
  group

theorem b₂_sq (hII : II4_4_4_center) : (t * b * t⁻¹) * (t * b * t⁻¹) = z := by
  have e : (t * b * t⁻¹) * (t * b * t⁻¹) = t * (b * b) * t⁻¹ := by group
  rw [e, hAB.bsq, h.a_four hAB hII, h.tz_comm' hII]

end Cfg65

@[expose] def aTwo (t a : G) : G := t * a * t⁻¹

@[expose] def uElt (t a : G) : G := a ^ 2 * (aTwo t a) ^ 2

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t) {a b : G} (hAB : AB65 S K₁ a b)

include h hAB

theorem a_comm_a₂' (hII : II4_4_4_center) : Commute a (aTwo t a) := h.a_comm_a₂ hAB hII

theorem a_sq_comm_a₂_sq (hII : II4_4_4_center) : Commute (a ^ 2) ((aTwo t a) ^ 2) :=
  (h.a_comm_a₂' hAB hII).pow_pow 2 2

theorem a_sq_sq (hII : II4_4_4_center) : a ^ 2 * a ^ 2 = z := by
  rw [← pow_add]; exact h.a_four hAB hII

theorem aTwo_sq_sq (hII : II4_4_4_center) : (aTwo t a) ^ 2 * (aTwo t a) ^ 2 = z := by
  rw [← pow_add]; exact h.a₂_four hAB hII

theorem u_sq (hII : II4_4_4_center) : uElt t a * uElt t a = 1 := by
  unfold uElt
  have hxy := h.a_sq_comm_a₂_sq hAB hII
  have e : (a ^ 2 * (aTwo t a) ^ 2) * (a ^ 2 * (aTwo t a) ^ 2) =
      (a ^ 2 * a ^ 2) * ((aTwo t a) ^ 2 * (aTwo t a) ^ 2) := by
    calc (a ^ 2 * (aTwo t a) ^ 2) * (a ^ 2 * (aTwo t a) ^ 2)
        = a ^ 2 * (((aTwo t a) ^ 2 * a ^ 2) * (aTwo t a) ^ 2) := by group
      _ = a ^ 2 * ((a ^ 2 * (aTwo t a) ^ 2) * (aTwo t a) ^ 2) := by rw [← hxy.eq]
      _ = (a ^ 2 * a ^ 2) * ((aTwo t a) ^ 2 * (aTwo t a) ^ 2) := by group
  rw [e, h.a_sq_sq hAB hII, h.aTwo_sq_sq hAB hII]
  exact h.z_sq

theorem u_mem_P (hII : II4_4_4_center) : uElt t a ∈ Pz S z := by
  rw [h.Pz_eq_sup hII]
  have h1 : a ^ 2 ∈ Pof S K₁ := pow_mem hAB.ha 2
  have h2 : (aTwo t a) ^ 2 ∈ Pof S K₂ := pow_mem (h.a₂_mem hAB) 2
  exact mul_mem (mem_sup_left h1) (mem_sup_right h2)

theorem u_mem_S (hII : II4_4_4_center) : uElt t a ∈ S := (h.u_mem_P hAB hII).1

theorem u_ne_one_of (hII : II4_4_4_center) (hu : uElt t a = 1 ∨ uElt t a = z) : False := by
  have hM := h.m4 hII
  have h1 : a ^ 2 ∈ Pof S K₁ := pow_mem hAB.ha 2
  have h2 : (aTwo t a) ^ 2 ∈ Pof S K₂ := pow_mem (h.a₂_mem hAB) 2
  have hzP₁ : z ∈ Pof S K₁ := h.z_mem_P hII (Or.inl rfl)
  have hmem : (aTwo t a) ^ 2 ∈ Pof S K₁ := by
    rcases hu with hu | hu
    · have : (aTwo t a) ^ 2 = (a ^ 2)⁻¹ := by
        unfold uElt at hu
        exact eq_inv_of_mul_eq_one_right hu
      rw [this]; exact inv_mem h1
    · have : (aTwo t a) ^ 2 = (a ^ 2)⁻¹ * z := by
        unfold uElt at hu
        calc (aTwo t a) ^ 2 = (a ^ 2)⁻¹ * (a ^ 2 * (aTwo t a) ^ 2) := by group
          _ = (a ^ 2)⁻¹ * z := by rw [hu]
      rw [this]; exact mul_mem (inv_mem h1) hzP₁
  have hz : (aTwo t a) ^ 2 ∈ zpowers z := by
    rw [← h.P_inf hII]
    exact ⟨hmem, h2⟩
  have h4 := orderOf_dvd_of_mem_zpowers hz
  have h5 : orderOf ((aTwo t a) ^ 2) = 4 := a₂_sq_order hAB
  rw [h5, h.std.orderOf_z] at h4
  omega

theorem u_ne_one (hII : II4_4_4_center) : uElt t a ≠ 1 := fun hu => h.u_ne_one_of hAB hII (Or.inl hu)

theorem u_ne_z (hII : II4_4_4_center) : uElt t a ≠ z := fun hu => h.u_ne_one_of hAB hII (Or.inr hu)

theorem a_comm_u (hII : II4_4_4_center) : a * uElt t a = uElt t a * a := by
  unfold uElt
  have h1 : a * a ^ 2 = a ^ 2 * a := (Commute.refl a).pow_right 2 |>.eq
  have h2 : a * (aTwo t a) ^ 2 = (aTwo t a) ^ 2 * a :=
    ((h.a_comm_a₂' hAB hII).pow_right 2).eq
  calc a * (a ^ 2 * (aTwo t a) ^ 2) = (a * a ^ 2) * (aTwo t a) ^ 2 := by group
    _ = a ^ 2 * (a * (aTwo t a) ^ 2) := by rw [h1]; group
    _ = a ^ 2 * ((aTwo t a) ^ 2 * a) := by rw [h2]
    _ = a ^ 2 * (aTwo t a) ^ 2 * a := by group

theorem u_mem_normalizer (hII : II4_4_4_center) : uElt t a ∈ normalizer (K₁ : Set G) := by
  have hM := h.m4 hII
  have h1 : a ^ 2 ∈ K₁ := pow_mem hAB.ha.2 2
  have h2 : (aTwo t a) ^ 2 ∈ K₂ := pow_mem (h.a₂_mem hAB).2 2
  exact mul_mem (Subgroup.le_normalizer h1) (hM.n₂₁ h2)

theorem u_not_conj (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) :
    ¬ IsConj z (uElt t a) :=
  not_isConj_of_order_eight h.std hII hrec h.d₁ hAB.ha.2 hAB.ha8 (h.u_ne_z hAB hII)
    (((h.m4 hII).S_syl.1 (h.u_mem_S hAB hII))) (h.u_mem_normalizer hAB hII) (h.a_comm_u hAB hII)

theorem t_u (hII : II4_4_4_center) : t * uElt t a * t⁻¹ = uElt t a := by
  have hti : t⁻¹ = t := h.t_inv
  have hsq : t * t = 1 := h.t_sq
  have e2 : t * (t * a * t⁻¹) * t⁻¹ = a := by
    calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
      _ = a := by rw [hsq, hti, hsq]; group
  have e1 : t * uElt t a * t⁻¹ = (aTwo t a) ^ 2 * a ^ 2 := by
    unfold uElt aTwo
    simp only [pow_two]
    calc t * (a * a * (t * a * t⁻¹ * (t * a * t⁻¹))) * t⁻¹
        = (t * a * t⁻¹) * (t * a * t⁻¹) * ((t * (t * a * t⁻¹) * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹)) := by
          group
      _ = (t * a * t⁻¹) * (t * a * t⁻¹) * (a * a) := by rw [e2]
  rw [e1]
  unfold uElt
  exact (h.a_sq_comm_a₂_sq hAB hII).symm.eq

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
