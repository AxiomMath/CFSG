module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_of_commute [Finite G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  let μ : A × B →* G := A.subtype.noncommCoprod B.subtype fun a b =>
    (hcomm a a.2 b b.2 : Commute (A.subtype a) (B.subtype b))
  have hrange : μ.range = A ⊔ B := by
    have := MonoidHom.noncommCoprod_range A.subtype B.subtype
      (fun a b => (hcomm a a.2 b b.2 : Commute (A.subtype a) (B.subtype b)))
    rw [range_subtype, range_subtype] at this
    exact this
  have hker : Nat.card μ.ker = Nat.card (A ⊓ B : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : G), mem_inf.mpr ⟨p.1.1.2, ?_⟩⟩
        invFun := fun c => ⟨(⟨c, (mem_inf.mp c.2).1⟩, ⟨(c : G)⁻¹, inv_mem (mem_inf.mp c.2).2⟩),
          by rw [MonoidHom.mem_ker]; exact mul_inv_cancel (c : G)⟩
        left_inv := fun p => ?_
        right_inv := fun c => rfl }
    · have h1 : (p.1.1 : G) * p.1.2 = 1 := p.2
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem p.1.2.2
    · have h1 : (p.1.1 : G) * p.1.2 = 1 := p.2
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact (eq_inv_of_mul_eq_one_right h1).symm
  have h := card_eq_card_ker_mul_card_range μ
  rw [Nat.card_prod, hker, hrange] at h
  rw [h, mul_comm]

theorem card_le_sq_of_elem [Finite G] {E : Subgroup G} {t : G} (ht : t * t = 1)
    (htE : t ∈ normalizer (E : Set G)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ Nat.card (E ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hEB : E ≤ centralizer ((E ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    fun x hx => mem_centralizer_iff.mpr fun y hy => hcomm y (mem_inf.mp hy).1 x hx
  have hY : ∀ y ∈ E, y⁻¹ * t * y * t ∈ E ⊓ centralizer ({t} : Set G) := by
    intro y hy
    have hty : t * y * t ∈ E := by
      have := (mem_normalizer_iff.mp htE y).mp hy
      rwa [ht'] at this
    refine mem_inf.mpr ⟨by
      rw [show y⁻¹ * t * y * t = y⁻¹ * (t * y * t) by group]
      exact mul_mem (inv_mem hy) hty, mem_centralizer_singleton_iff.mpr ?_⟩
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
    have hti : (t * y * t)⁻¹ = t * y * t := inv_eq_of_mul_eq_one_right (hsq _ hty)
    have hc := hcomm y hy _ hty
    have h1 : t * (y⁻¹ * t * y * t) * t = (t * y * t)⁻¹ * y := by
      calc t * (y⁻¹ * t * y * t) * t = t * y⁻¹ * t * y * (t * t) := by group
        _ = t⁻¹ * y⁻¹ * t⁻¹ * y := by rw [ht, mul_one, ht']
        _ = (t * y * t)⁻¹ * y := by group
    have h2 : t * (y⁻¹ * t * y * t) * t = y⁻¹ * t * y * t := by
      rw [h1, hti, ← hc, hyi]
      group
    calc y⁻¹ * t * y * t * t = (t * (y⁻¹ * t * y * t) * t) * t := by rw [h2]
      _ = t * (y⁻¹ * t * y * t) * (t * t) := by group
      _ = t * (y⁻¹ * t * y * t) := by rw [ht, mul_one]
  have h := card_le_of_crossed ht hEB hY
  rwa [sq]

theorem mem_conjW {d : Data G} {B : Subgroup G} {x : G} :
    x ∈ d.conjW B ↔ ∃ y ∈ B, d.w₂ * y * d.w₂⁻¹ = x := by
  simp [Data.conjW, MulAut.conj_apply]

namespace Hyp

variable {d : Data G} (h : Hyp d) (hB : HypB d)
include h hB

theorem D₄_sq [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {y : G} (hy : y ∈ d.D₄) : y * y = 1 :=
  h.D₂_sq hB hV (h.D₄_le_D₂ hy)

omit hB in
theorem t_mem_normalizer_D₁ [Finite G] : d.t ∈ normalizer (d.D₁ : Set G) :=
  XV_le_normalizer_D₁ (h.C₀_le_XV h.t_mem_C₀)

omit hB in
theorem t_mem_normalizer_V₂ [Finite G] : d.t ∈ normalizer (d.V₂ : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro y hy
  rw [h.t_inv, show d.t * y * d.t = y * (y⁻¹ * d.t * y * d.t) by group]
  exact mul_mem hy (h.Z₂S_le_V₂ (h.crossed_V₂ hy))

theorem w₂_comm_t : d.w₂ * d.t = d.t * d.w₂ :=
  h.comm_of_mem_L (h.K₁_le_L hB.w₂_mem_K₁)

theorem t_mem_normalizer_conjW [Finite G] {B : Subgroup G} (htB : d.t ∈ normalizer (B : Set G)) :
    d.t ∈ normalizer (d.conjW B : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_conjW.mp hx
  refine mem_conjW.mpr ⟨d.t * y * d.t⁻¹, (mem_normalizer_iff.mp htB y).mp hy, ?_⟩
  have e := h.w₂_comm_t hB
  have e' : d.w₂⁻¹ * d.t⁻¹ = d.t⁻¹ * d.w₂⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, e]
  calc d.w₂ * (d.t * y * d.t⁻¹) * d.w₂⁻¹ = (d.w₂ * d.t) * y * (d.t⁻¹ * d.w₂⁻¹) := by group
    _ = (d.t * d.w₂) * y * (d.w₂⁻¹ * d.t⁻¹) := by rw [e, e']
    _ = d.t * (d.w₂ * y * d.w₂⁻¹) * d.t⁻¹ := by group

omit h hB in
theorem w₂_conj_V₁ {v : G} (hw : d.w₂ ∈ centralizer (d.V₁ : Set G)) (hv : v ∈ d.V₁) :
    d.w₂ * v * d.w₂⁻¹ = v := by
  rw [← mem_centralizer_iff.mp hw v hv, mul_inv_cancel_right]

theorem V₂_inf_conjW [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.V₂ ⊓ d.conjW d.V₂ = d.V₁ := by
  have hw₂V : d.w₂ ∈ centralizer (d.V₁ : Set G) := h.K₁_le_cent_V₁ hB.w₂_mem_K₁
  have hle : d.V₁ ≤ d.V₂ ⊓ d.conjW d.V₂ := le_inf le_sup_right fun v hv =>
    mem_conjW.mpr ⟨v, mem_sup_right hv, w₂_conj_V₁ hw₂V hv⟩
  refine (eq_of_le_of_card_ge hle ?_).symm
  have hH : ∀ {x}, x ∈ d.H → d.w₂⁻¹ * x * d.w₂ ∈ d.H := fun hx =>
    mul_mem (mul_mem (inv_mem (h.L_le_H (h.K₁_le_L hB.w₂_mem_K₁))) hx)
      (h.L_le_H (h.K₁_le_L hB.w₂_mem_K₁))
  have hcent : (d.V₂ ⊓ d.conjW d.V₂) ⊓ centralizer ({d.t} : Set G) ≤ zpowers d.z := by
    intro x hx
    obtain ⟨⟨hx2, hxw⟩, hxt⟩ := hx
    obtain ⟨y, hy, rfl⟩ := mem_conjW.mp hxw
    have hyH : y ∈ d.H := by
      have := hH hxt
      rwa [show d.w₂⁻¹ * (d.w₂ * y * d.w₂⁻¹) * d.w₂ = y by group] at this
    have hyZ : y ∈ d.Z₂S := h.V₂_inf_H ▸ (mem_inf.mpr ⟨hy, hyH⟩ : y ∈ d.V₂ ⊓ d.H)
    have hxZ : d.w₂ * y * d.w₂⁻¹ ∈ d.Z₂S :=
      h.V₂_inf_H ▸ (mem_inf.mpr ⟨hx2, hxt⟩ : _ ∈ d.V₂ ⊓ d.H)
    exact hB.Z₂S_inf (mem_inf.mpr ⟨hxZ, mem_conjW.mpr ⟨y, hyZ, rfl⟩⟩)
  have hD : ∀ {x}, x ∈ d.V₂ ⊓ d.conjW d.V₂ → x ∈ d.D₄ := fun hx => h.V₂_le_D₄ (mem_inf.mp hx).1
  have h1 := card_le_sq_of_elem h.t_sq (mem_normalizer_inf h.t_mem_normalizer_V₂
    (h.t_mem_normalizer_conjW hB h.t_mem_normalizer_V₂)) (fun x hx y hy => h.D₄_comm (hD hx)
    (hD hy)) (fun x hx => h.D₄_sq hB hV (hD hx))
  have h2 := card_le_of_le hcent
  rw [h.card_zpowers_z] at h2
  rw [h.card_V₁]
  calc Nat.card (d.V₂ ⊓ d.conjW d.V₂ : Subgroup G) ≤ _ := h1
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 4 := by norm_num

omit hB in
theorem V₂_le_D₂ [Finite G] : d.V₂ ≤ d.D₂ := h.V₂_le_D₄.trans h.D₄_le_D₂

theorem conjW_V₂_le_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.conjW d.V₂ ≤ d.D₁ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_conjW.mp hx
  exact (mem_normalizer_iff.mp (XV_le_normalizer_D₁ (h.K₁_le_XV hB.w₂_mem_K₁)) y).mp
    (h.V₂_le_D₁ hB hV hy)

theorem conjW_V₂_le_D₂ [Finite G] : d.conjW d.V₂ ≤ d.D₂ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_conjW.mp hx
  exact (mem_normalizer_iff.mp (h.K₂_le_normalizer_D₂ hB hB.w₂_mem_K₂) y).mp (h.V₂_le_D₂ hy)

omit hB in
theorem mem_A₁_of_AV_A₂ [Finite G] {g : G} (hg : g ∈ d.AV) (hg2 : g ∈ d.A₂) : g ∈ d.A₁ := by
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hg
  have hvH : v ∈ d.H := by
    have := mul_mem (inv_mem (h.L_le_H (h.A₁_le_L ha))) (h.L_le_H (h.A₂_le_L hg2))
    rwa [inv_mul_cancel_left] at this
  exact mul_mem ha ((zpowers_le.mpr h.z_mem_A₁) (h.V₁_inf_H_le (mem_inf.mpr ⟨hv, hvH⟩)))

theorem D₁_inf_D₂ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) :
    d.D₁ ⊓ d.D₂ = d.V₂ ⊔ d.conjW d.V₂ := by
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf (h.V₂_le_D₁ hB hV) h.V₂_le_D₂)
    (le_inf (h.conjW_V₂_le_D₁ hB hV) (h.conjW_V₂_le_D₂ hB)))
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  have hxC : x ∈ d.C₂ := (mem_inf.mp hx2).1
  have hθ : d.theta x ∈ d.A₁ ⊓ d.A₂ :=
    mem_inf.mpr ⟨h.mem_A₁_of_AV_A₂ (h.crossed_D₁ hB hV hx1) (h.crossed_C₂ hxC), h.crossed_C₂ hxC⟩
  have hZA : d.Z₂S ≤ d.A₂ := h.Z₂S_le_A₄.trans h.A₄_le_A₂
  have hZwA : d.conjW d.Z₂S ≤ d.A₂ := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := mem_conjW.mp hc
    exact (mem_normalizer_iff.mp (hB.K₂_le_normalizer hB.w₂_mem_K₂) b).mp (hZA hb)
  obtain ⟨b, hb, c, hc, hbc⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun b hb c hc => h.A₂_comm b (hZA hb) c (hZwA hc)) (hB.A₁_inf_A₂ hθ)
  obtain ⟨y₁, hy₁, hy₁t⟩ := h.exists_V₂_conj hb
  obtain ⟨b', hb', rfl⟩ := mem_conjW.mp hc
  obtain ⟨y', hy', hy't⟩ := h.exists_V₂_conj hb'
  set y₂ := d.w₂ * y' * d.w₂⁻¹ with hy₂def
  have hy₂ : y₂ ∈ d.conjW d.V₂ := mem_conjW.mpr ⟨y', hy', rfl⟩
  have hy₂t : y₂⁻¹ * d.t * y₂ * d.t = d.w₂ * b' * d.w₂⁻¹ := by
    rw [hy₂def, crossed_conj (h.w₂_comm_t hB), hy't]
  have hC : ∀ {y}, y ∈ d.V₂ ⊔ d.conjW d.V₂ → y ∈ d.C₂ := fun hy =>
    (mem_inf.mp ((sup_le (h.V₂_le_D₂) (h.conjW_V₂_le_D₂ hB)) hy)).1
  set y := y₁ * y₂ with hydef
  have hy : y ∈ d.V₂ ⊔ d.conjW d.V₂ := mul_mem (mem_sup_left hy₁) (mem_sup_right hy₂)
  have hyt : y⁻¹ * d.t * y * d.t = d.theta x := by
    rw [hydef, crossed_mul h.t_sq (mem_centralizer_iff.mp (h.C₂_le_cent (hC (mem_sup_right hy₂)))
      _ (h.crossed_C₂ (hC (mem_sup_left hy₁)))), hy₁t, hy₂t, hbc]
  have hxy : (x * y⁻¹)⁻¹ * d.t * (x * y⁻¹) * d.t = 1 := by
    have hyC := hC hy
    rw [crossed_mul h.t_sq (mem_centralizer_iff.mp (h.C₂_le_cent (inv_mem hyC)) _
      (h.crossed_C₂ hxC)), crossed_inv h.t_sq (mem_centralizer_iff.mp (h.C₂_le_cent hyC) _
      (h.crossed_C₂ hyC)), hyt]
    exact mul_inv_cancel _
  have hxyH : x * y⁻¹ ∈ d.H := mem_centralizer_singleton_iff.mpr
    ((crossed_eq_one_iff h.t_sq).mp hxy)
  have hyD₁ : y ∈ d.D₁ := (sup_le (h.V₂_le_D₁ hB hV) (h.conjW_V₂_le_D₁ hB hV)) hy
  have hyD₂ : y ∈ d.D₂ := (sup_le h.V₂_le_D₂ (h.conjW_V₂_le_D₂ hB)) hy
  have hA₁ : x * y⁻¹ ∈ d.A₁ := (h.D₁_inf_H hB hV) ▸
    (mem_inf.mpr ⟨mul_mem hx1 (inv_mem hyD₁), hxyH⟩ : _ ∈ d.D₁ ⊓ d.H)
  have hA₂ : x * y⁻¹ ∈ d.A₂ := h.D₂_inf_H ▸
    (mem_inf.mpr ⟨mul_mem hx2 (inv_mem hyD₂), hxyH⟩ : _ ∈ d.D₂ ⊓ d.H)
  have hmem : x * y⁻¹ ∈ d.V₂ ⊔ d.conjW d.V₂ :=
    sup_le_sup h.Z₂S_le_V₂ (map_mono h.Z₂S_le_V₂) (hB.A₁_inf_A₂ (mem_inf.mpr ⟨hA₁, hA₂⟩))
  have e : x = (x * y⁻¹) * y := by group
  rw [e]
  exact mul_mem hmem hy

theorem card_D₁_inf_D₂ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) :
    Nat.card (d.D₁ ⊓ d.D₂ : Subgroup G) = 2 ^ 10 := by
  rw [h.D₁_inf_D₂ hB hV]
  have h1 := card_sup_mul_card_inf_of_commute (A := d.V₂) (B := d.conjW d.V₂)
    fun a ha b hb => h.D₂_comm hB (h.V₂_le_D₂ ha) (h.conjW_V₂_le_D₂ hB hb)
  have h2 : Nat.card (d.conjW d.V₂) = Nat.card d.V₂ :=
    card_map_of_injective (MulEquiv.injective _)
  rw [h.V₂_inf_conjW hB hV, h2, h.card_V₁, h.card_V₂] at h1
  omega

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
