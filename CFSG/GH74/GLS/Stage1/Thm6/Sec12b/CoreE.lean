module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Derived

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G]

theorem isFour_eq_pair {V : Subgroup G} (hV : IsFour V) {p q : G} (hp : p ∈ V) (hq : q ∈ V)
    (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hpq : p ≠ q) :
    V = Subgroup.zpowers p ⊔ Subgroup.zpowers q := by
  have hp2 := (hV.1 p hp).1
  have hq2 := (hV.1 q hq).1
  have hc : p * q = q * p := (hV.1 p hp).2 q hq
  have hW := isFour_pair hp2 hq2 hp1 hq1 hpq hc
  have hle : Subgroup.zpowers p ⊔ Subgroup.zpowers q ≤ V :=
    sup_le ((Subgroup.zpowers_le).2 hp) ((Subgroup.zpowers_le).2 hq)
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV.2]; norm_num)
  symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hV.2, hW.2])

theorem isFour_mem_cases {V : Subgroup G} (hV : IsFour V) {p q : G} (hp : p ∈ V) (hq : q ∈ V)
    (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hpq : p ≠ q) {w : G} (hw : w ∈ V) :
    w = 1 ∨ w = p ∨ w = q ∨ w = p * q := by
  have hp2 := (hV.1 p hp).1
  have hq2 := (hV.1 q hq).1
  have hE := isFour_eq_pair hV hp hq hp1 hq1 hpq
  have hcomm : ∀ u ∈ Subgroup.zpowers p, ∀ v ∈ Subgroup.zpowers q, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow (show Commute p q from (hV.1 p hp).2 q hq) k l).eq
  rw [hE] at hw
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_commute hcomm hw
  rcases zpowers_sq_cases hp2 hu with rfl | rfl <;> rcases zpowers_sq_cases hq2 hv with rfl | rfl <;>
    simp

theorem comm_of_sq_comm {f p : G} (hf : Is3 f) (h : f * f * p = p * (f * f)) : f * p = p * f := by
  obtain ⟨k, hk⟩ := hf
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have hfm : f = (f ^ 2) ^ (m + 1) := by
    have h1 : f ^ (2 * m + 1) = 1 := by rw [← hm]; exact hk
    calc f = f ^ (2 * m + 1) * f := by rw [h1, one_mul]
      _ = f ^ (2 * (m + 1)) := by rw [← pow_succ]; ring_nf
      _ = (f ^ 2) ^ (m + 1) := by rw [pow_mul]
  have hc : Commute (f ^ 2) p := by rw [pow_two]; exact h
  have := (hc.pow_left (m + 1)).eq
  rw [← hfm] at this
  exact this

theorem conj_inj (f : G) {u v : G} (h : f * u * f⁻¹ = f * v * f⁻¹) : u = v := by
  have := congrArg (fun t => f⁻¹ * t * f) h
  simpa [mul_assoc] using this

theorem V_cycle {V : Subgroup G} (hV : IsFour V) {f : G} (hf : Is3 f)
    (hfV : ∀ w ∈ V, f * w * f⁻¹ ∈ V) (hfn : ∃ w ∈ V, f * w * f⁻¹ ≠ w) {p : G} (hp : p ∈ V)
    (hp1 : p ≠ 1) :
    f * p * f⁻¹ ≠ p ∧ f * p * f⁻¹ ≠ 1 ∧ f * (f * p * f⁻¹) * f⁻¹ = p * (f * p * f⁻¹) := by
  have hp2 : p * p = 1 := (hV.1 p hp).1
  have hne1 : f * p * f⁻¹ ≠ 1 := by
    intro h
    exact hp1 (conj_inj f (h.trans (by group)))
  have hsq : ∀ q : G, q ∈ V → (f * f * q = q * (f * f)) → f * q * f⁻¹ = q := by
    intro q _ h
    have := comm_of_sq_comm hf h
    rw [this]; group
  have hfne : f * p * f⁻¹ ≠ p := by
    intro hfix
    obtain ⟨w0, hw0V, hw0⟩ := hfn
    have hw01 : w0 ≠ 1 := by
      rintro rfl
      exact hw0 (by group)
    have hw0p : w0 ≠ p := by
      rintro rfl
      exact hw0 hfix
    have hq := hfV w0 hw0V
    have hcases := isFour_mem_cases hV hp hw0V hp1 hw01 hw0p.symm hq
    have hq2 : f * w0 * f⁻¹ = p * w0 := by
      rcases hcases with h | h | h | h
      · exact absurd (conj_inj f (h.trans (by group))) hw01
      · exact absurd (conj_inj f (h.trans hfix.symm)) hw0p
      · exact absurd h hw0
      · exact h
    have hw0sq : f * (f * w0 * f⁻¹) * f⁻¹ = w0 := by
      rw [hq2]
      calc f * (p * w0) * f⁻¹ = (f * p * f⁻¹) * (f * w0 * f⁻¹) := by group
        _ = p * (p * w0) := by rw [hfix, hq2]
        _ = (p * p) * w0 := by group
        _ = w0 := by rw [hp2, one_mul]
    have hcomm : f * f * w0 = w0 * (f * f) := by
      calc f * f * w0 = (f * (f * w0 * f⁻¹) * f⁻¹) * (f * f) := by group
        _ = w0 * (f * f) := by rw [hw0sq]
    exact hw0 (hsq w0 hw0V hcomm)
  refine ⟨hfne, hne1, ?_⟩
  have hp'V := hfV p hp
  have hcases := isFour_mem_cases hV hp hp'V hp1 hne1 hfne.symm (hfV _ hp'V)
  rcases hcases with h | h | h | h
  · exact absurd (conj_inj f (h.trans (by group))) hne1
  · exact absurd (hsq p hp (by
      calc f * f * p = (f * (f * p * f⁻¹) * f⁻¹) * (f * f) := by group
        _ = p * (f * f) := by rw [h])) hfne
  · exact absurd (conj_inj f h) hfne
  · exact h

structure Tri (V : Subgroup G) (f p0 p1 p2 : G) : Prop where
  m0 : p0 ∈ V
  m1 : p1 ∈ V
  m2 : p2 ∈ V
  n0 : p0 ≠ 1
  n1 : p1 ≠ 1
  n2 : p2 ≠ 1
  d01 : p0 ≠ p1
  f0 : f * p0 * f⁻¹ = p1
  f1 : f * p1 * f⁻¹ = p2
  f2 : f * p2 * f⁻¹ = p0
  m01 : p0 * p1 = p2
  allV : ∀ w ∈ V, w = 1 ∨ w = p0 ∨ w = p1 ∨ w = p2

theorem exists_tri {V : Subgroup G} (hV : IsFour V) {f : G} (hf : Is3 f)
    (hfV : ∀ w ∈ V, f * w * f⁻¹ ∈ V) (hfn : ∃ w ∈ V, f * w * f⁻¹ ≠ w) {p : G} (hp : p ∈ V)
    (hp1 : p ≠ 1) : ∃ p1 p2 : G, Tri V f p p1 p2 := by
  obtain ⟨hne, hne1, hf1⟩ := V_cycle hV hf hfV hfn hp hp1
  have hp'V := hfV p hp
  have hp2 : p * p = 1 := (hV.1 p hp).1
  have hp'2 : (f * p * f⁻¹) * (f * p * f⁻¹) = 1 := (hV.1 _ hp'V).1
  have hcomm : p * (f * p * f⁻¹) = (f * p * f⁻¹) * p := (hV.1 p hp).2 _ hp'V
  have hprodV : p * (f * p * f⁻¹) ∈ V := mul_mem hp hp'V
  have hprod1 : p * (f * p * f⁻¹) ≠ 1 := by
    intro h
    apply hne
    have h' : f * p * f⁻¹ = p⁻¹ := by
      calc f * p * f⁻¹ = p⁻¹ * (p * (f * p * f⁻¹)) := by group
        _ = p⁻¹ := by rw [h, mul_one]
    rw [h']
    exact inv_eq_of_mul_eq_one_right hp2
  refine ⟨f * p * f⁻¹, p * (f * p * f⁻¹),
    ⟨hp, hp'V, hprodV, hp1, hne1, hprod1, hne.symm, rfl, hf1, ?_, rfl, ?_⟩⟩
  · calc f * (p * (f * p * f⁻¹)) * f⁻¹
        = (f * p * f⁻¹) * (f * (f * p * f⁻¹) * f⁻¹) := by group
      _ = (f * p * f⁻¹) * (p * (f * p * f⁻¹)) := by rw [hf1]
      _ = ((f * p * f⁻¹) * p) * (f * p * f⁻¹) := by group
      _ = (p * (f * p * f⁻¹)) * (f * p * f⁻¹) := by rw [hcomm]
      _ = p * ((f * p * f⁻¹) * (f * p * f⁻¹)) := by group
      _ = p := by rw [hp'2, mul_one]
  · intro w hw
    exact isFour_mem_cases hV hp hp'V hp1 hne1 hne.symm hw

@[expose] def ConjTo (x e : G) : Prop := ∃ h : G, h * x * h⁻¹ = e

theorem ConjTo.refl' (x : G) : ConjTo x x := ⟨1, by group⟩

theorem ConjTo.conj {x e : G} (h : ConjTo x e) (g : G) : ConjTo x (g * e * g⁻¹) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨g * k, by group⟩

theorem ConjTo.conj_iff {x e : G} (g : G) : ConjTo x (g * e * g⁻¹) ↔ ConjTo x e := by
  refine ⟨fun h => ?_, fun h => h.conj g⟩
  have := h.conj g⁻¹
  rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at this

theorem not_conjTo_one {x : G} (hx : x ≠ 1) : ¬ ConjTo x 1 := by
  rintro ⟨h, hh⟩
  apply hx
  have := congrArg (fun t => h⁻¹ * t * h) hh
  simpa [mul_assoc] using this

structure Ctx (V : Subgroup G) (x f a y : G) : Prop where
  hV : IsFour V
  hx2 : x * x = 1
  hxV : ∀ w ∈ V, x * w = w * x
  hxn : x ∉ V
  hf3 : Is3 f
  hfx : f * x * f⁻¹ = x
  hfV : ∀ w ∈ V, f * w * f⁻¹ ∈ V
  hfn : ∃ w ∈ V, f * w * f⁻¹ ≠ w
  haN : a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)
  hfN : f ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)
  hax : a * x * a⁻¹ ≠ x
  hyE : y ∈ V ⊔ Subgroup.zpowers x
  hy1 : y ≠ 1
  hya : a * y * a⁻¹ = y
  hyc : ¬ ConjTo x y

namespace Ctx

variable {V : Subgroup G} {x f a y : G} (c : Ctx V x f a y)

include c

theorem hx1 : x ≠ 1 := fun h => c.hxn (by rw [h]; exact V.one_mem)

theorem xw_notV {w : G} (hw : w ∈ V) : x * w ∉ V := by
  intro h
  apply c.hxn
  have := mul_mem h (inv_mem hw)
  simpa using this

theorem E_cases {e : G} (he : e ∈ V ⊔ Subgroup.zpowers x) : e ∈ V ∨ ∃ w ∈ V, e = x * w := by
  have hc : ∀ u ∈ V, ∀ v ∈ Subgroup.zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_right (show Commute u x from (c.hxV u hu).symm) k).eq
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_commute hc he
  rcases zpowers_sq_cases c.hx2 hv with rfl | rfl
  · left; simpa using hu
  · right; exact ⟨u, hu, (c.hxV u hu).symm⟩

omit c in
theorem x_mem_E : x ∈ V ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

omit c in
theorem V_le_E {w : G} (hw : w ∈ V) : w ∈ V ⊔ Subgroup.zpowers x := Subgroup.mem_sup_left hw

omit c in
theorem xw_mem_E {w : G} (hw : w ∈ V) : x * w ∈ V ⊔ Subgroup.zpowers x :=
  mul_mem Ctx.x_mem_E (Ctx.V_le_E hw)

omit c in
theorem conjE {g : G}
    (hg : g ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) {e : G}
    (he : e ∈ V ⊔ Subgroup.zpowers x) : g * e * g⁻¹ ∈ V ⊔ Subgroup.zpowers x :=
  (Subgroup.mem_normalizer_iff.1 hg e).1 he

theorem prod2 {w1 w2 : G} (h1 : w1 ∈ V) : (x * w1) * (x * w2) = w1 * w2 := by
  calc (x * w1) * (x * w2) = x * (w1 * x) * w2 := by group
    _ = x * (x * w1) * w2 := by rw [← c.hxV w1 h1]
    _ = (x * x) * (w1 * w2) := by group
    _ = w1 * w2 := by rw [c.hx2, one_mul]

theorem prod3 {c0 c1 c2 : G} (h0 : c0 ∈ V) (h1 : c1 ∈ V) :
    (x * c0) * (x * c1) * (x * c2) = x * (c0 * c1 * c2) := by
  rw [c.prod2 h0]
  calc (c0 * c1) * (x * c2) = ((c0 * c1) * x) * c2 := by group
    _ = (x * (c0 * c1)) * c2 := by rw [← c.hxV _ (mul_mem h0 h1)]
    _ = x * (c0 * c1 * c2) := by group

theorem hfinvx : f⁻¹ * x * f = x := by
  calc f⁻¹ * x * f = f⁻¹ * (f * x * f⁻¹) * f := by rw [c.hfx]
    _ = x := by group

theorem tri_y_exists {p : G} (hp : p ∈ V) (hp1 : p ≠ 1) : ∃ p1 p2 : G, Tri V f p p1 p2 :=
  exists_tri c.hV c.hf3 c.hfV c.hfn hp hp1

theorem hfinvV {w : G} (hw : w ∈ V) : f⁻¹ * w * f ∈ V := by
  obtain ⟨w0, hw0, hw0f⟩ := c.hfn
  have hw01 : w0 ≠ 1 := by
    rintro rfl
    exact hw0f (by group)
  obtain ⟨p1, p2, T⟩ := c.tri_y_exists hw0 hw01
  rcases T.allV w hw with h | h | h | h
  · rw [h]; simp
  · rw [h]
    have : f⁻¹ * w0 * f = p2 := by rw [← T.f2]; group
    rw [this]; exact T.m2
  · rw [h]
    have : f⁻¹ * p1 * f = w0 := by rw [← T.f0]; group
    rw [this]; exact hw0
  · rw [h]
    have : f⁻¹ * p2 * f = p1 := by rw [← T.f1]; group
    rw [this]; exact T.m1

theorem xw_ne_one {w : G} (hw : w ∈ V) : x * w ≠ 1 := by
  intro h
  apply c.xw_notV hw
  rw [h]
  exact V.one_mem

theorem notV : a * x * a⁻¹ ∉ V := by
  intro hu
  have hu1 : a * x * a⁻¹ ≠ 1 := by
    intro h
    apply c.hx1
    have := congrArg (fun t => a⁻¹ * t * a) h
    simpa [mul_assoc] using this
  obtain ⟨u1, u2, T⟩ := c.tri_y_exists hu hu1
  have nc_u : ConjTo x (a * x * a⁻¹) := ⟨a, rfl⟩
  have nc_u1 : ConjTo x u1 := by rw [← T.f0]; exact nc_u.conj f
  have nc_u2 : ConjTo x u2 := by rw [← T.f1]; exact nc_u1.conj f
  have ncV : ∀ w ∈ V, w ≠ 1 → ConjTo x w := by
    intro w hw hw1
    rcases T.allV w hw with h | h | h | h
    · exact absurd h hw1
    · rw [h]; exact nc_u
    · rw [h]; exact nc_u1
    · rw [h]; exact nc_u2
  rcases c.E_cases c.hyE with hyV | ⟨w, hw, hyw⟩
  · exact c.hyc (ncV y hyV c.hy1)
  · have hw1 : w ≠ 1 := by
      rintro rfl
      apply c.hyc
      rw [hyw, mul_one]
      exact ConjTo.refl' x
    obtain ⟨w1, w2, W⟩ := c.tri_y_exists hw hw1
    have hy_1 : f * y * f⁻¹ = x * w1 := by
      rw [hyw]
      calc f * (x * w) * f⁻¹ = (f * x * f⁻¹) * (f * w * f⁻¹) := by group
        _ = x * w1 := by rw [c.hfx, W.f0]
    have hy_2 : f * (x * w1) * f⁻¹ = x * w2 := by
      calc f * (x * w1) * f⁻¹ = (f * x * f⁻¹) * (f * w1 * f⁻¹) := by group
        _ = x * w2 := by rw [c.hfx, W.f1]
    have hnV : ∀ e : G, e ≠ 1 → (ConjTo x e → ConjTo x y) → a * e * a⁻¹ ∉ V := by
      intro e he1 hey hb
      have hb1 : a * e * a⁻¹ ≠ 1 := by
        intro h
        exact he1 (conj_inj a (h.trans (by group)))
      have := ncV _ hb hb1
      exact c.hyc (hey ((ConjTo.conj_iff a).1 this))
    have hn0 : ConjTo x (x * w) → ConjTo x y := by
      intro h; rw [hyw]; exact h
    have hn1 : ConjTo x (x * w1) → ConjTo x y := by
      intro h; rw [← hy_1] at h; exact (ConjTo.conj_iff f).1 h
    have hn2 : ConjTo x (x * w2) → ConjTo x y := by
      intro h; rw [← hy_2] at h; exact hn1 ((ConjTo.conj_iff f).1 h)
    obtain ⟨c0, hc0, hc0e⟩ := (c.E_cases (Ctx.conjE c.haN (Ctx.xw_mem_E hw))).resolve_left
      (hnV _ (c.xw_ne_one hw) hn0)
    obtain ⟨c1, hc1, hc1e⟩ := (c.E_cases (Ctx.conjE c.haN (Ctx.xw_mem_E W.m1))).resolve_left
      (hnV _ (c.xw_ne_one W.m1) hn1)
    obtain ⟨c2, hc2, hc2e⟩ := (c.E_cases (Ctx.conjE c.haN (Ctx.xw_mem_E W.m2))).resolve_left
      (hnV _ (c.xw_ne_one W.m2) hn2)
    have hx_eq : (x * w) * (x * w1) * (x * w2) = x := by
      rw [c.prod3 hw W.m1, W.m01, (c.hV.1 w2 W.m2).1, mul_one]
    have hu_eq : a * x * a⁻¹ =
        (a * (x * w) * a⁻¹) * (a * (x * w1) * a⁻¹) * (a * (x * w2) * a⁻¹) := by
      calc a * x * a⁻¹ = a * ((x * w) * (x * w1) * (x * w2)) * a⁻¹ := by rw [hx_eq]
        _ = _ := by group
    rw [hc0e, hc1e, hc2e, c.prod3 hc0 hc1] at hu_eq
    exact c.xw_notV (mul_mem (mul_mem hc0 hc1) hc2) (by rw [← hu_eq]; exact hu)

theorem struct : ∃ u0 ∈ V, u0 ≠ 1 ∧ a * x * a⁻¹ = x * u0 := by
  have hE : a * x * a⁻¹ ∈ V ⊔ Subgroup.zpowers x := Ctx.conjE c.haN Ctx.x_mem_E
  rcases c.E_cases hE with h | ⟨u0, hu0, h⟩
  · exact absurd h c.notV
  · refine ⟨u0, hu0, ?_, h⟩
    rintro rfl
    exact c.hax (by rw [h, mul_one])

theorem ncx : ∀ w ∈ V, ConjTo x (x * w) := by
  obtain ⟨u0, hu0, hu01, hu⟩ := c.struct
  obtain ⟨u1, u2, T⟩ := c.tri_y_exists hu0 hu01
  have h0 : ConjTo x (x * u0) := ⟨a, hu⟩
  have h1 : ConjTo x (x * u1) := by
    have h := h0.conj f
    have e : f * (x * u0) * f⁻¹ = x * u1 := by
      calc f * (x * u0) * f⁻¹ = (f * x * f⁻¹) * (f * u0 * f⁻¹) := by group
        _ = x * u1 := by rw [c.hfx, T.f0]
    rwa [e] at h
  have h2 : ConjTo x (x * u2) := by
    have h := h1.conj f
    have e : f * (x * u1) * f⁻¹ = x * u2 := by
      calc f * (x * u1) * f⁻¹ = (f * x * f⁻¹) * (f * u1 * f⁻¹) := by group
        _ = x * u2 := by rw [c.hfx, T.f1]
    rwa [e] at h
  intro w hw
  rcases T.allV w hw with h | h | h | h
  · rw [h, mul_one]; exact ConjTo.refl' x
  · rw [h]; exact h0
  · rw [h]; exact h1
  · rw [h]; exact h2

theorem y_mem : y ∈ V := by
  rcases c.E_cases c.hyE with h | ⟨w, hw, h⟩
  · exact h
  · exfalso
    apply c.hyc
    rw [h]
    exact c.ncx w hw

theorem nc_V : ∀ w ∈ V, w ≠ 1 → ¬ ConjTo x w := by
  obtain ⟨y1, y2, T⟩ := c.tri_y_exists c.y_mem c.hy1
  have h1 : ¬ ConjTo x y1 := by
    intro h
    apply c.hyc
    rw [← T.f0] at h
    exact (ConjTo.conj_iff f).1 h
  have h2 : ¬ ConjTo x y2 := by
    intro h
    apply h1
    rw [← T.f1] at h
    exact (ConjTo.conj_iff f).1 h
  intro w hw hw1
  rcases T.allV w hw with h | h | h | h
  · exact absurd h hw1
  · rw [h]; exact c.hyc
  · rw [h]; exact h1
  · rw [h]; exact h2

theorem V_iff {e : G} (he : e ∈ V ⊔ Subgroup.zpowers x) : e ∈ V ↔ ¬ ConjTo x e := by
  constructor
  · intro hV'
    by_cases h1 : e = 1
    · rw [h1]; exact not_conjTo_one c.hx1
    · exact c.nc_V e hV' h1
  · intro hnc
    rcases c.E_cases he with h | ⟨w, hw, h⟩
    · exact h
    · exfalso
      apply hnc
      rw [h]
      exact c.ncx w hw

theorem a_V {w : G} (hw : w ∈ V) : a * w * a⁻¹ ∈ V := by
  by_cases hw1 : w = 1
  · rw [hw1]
    simp
  · have hE : a * w * a⁻¹ ∈ V ⊔ Subgroup.zpowers x := Ctx.conjE c.haN (Ctx.V_le_E hw)
    rw [c.V_iff hE]
    intro hnc
    exact c.nc_V w hw hw1 ((ConjTo.conj_iff a).1 hnc)

theorem conj_step {g0 p : G}
    (hg0N : g0 ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
    (hg0V : ∀ w ∈ V, g0 * w * g0⁻¹ = w) (hg0x : g0 * x * g0⁻¹ = x * p) :
    f * g0 * f⁻¹ ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ∧
      (∀ w ∈ V, (f * g0 * f⁻¹) * w * (f * g0 * f⁻¹)⁻¹ = w) ∧
      (f * g0 * f⁻¹) * x * (f * g0 * f⁻¹)⁻¹ = x * (f * p * f⁻¹) := by
  refine ⟨mul_mem (mul_mem c.hfN hg0N) (inv_mem c.hfN), ?_, ?_⟩
  · intro w hw
    have hw' : f⁻¹ * w * f ∈ V := c.hfinvV hw
    calc (f * g0 * f⁻¹) * w * (f * g0 * f⁻¹)⁻¹
        = f * (g0 * (f⁻¹ * w * f) * g0⁻¹) * f⁻¹ := by group
      _ = f * (f⁻¹ * w * f) * f⁻¹ := by rw [hg0V _ hw']
      _ = w := by group
  · calc (f * g0 * f⁻¹) * x * (f * g0 * f⁻¹)⁻¹
        = f * (g0 * (f⁻¹ * x * f) * g0⁻¹) * f⁻¹ := by group
      _ = f * (g0 * x * g0⁻¹) * f⁻¹ := by rw [c.hfinvx]
      _ = f * (x * p) * f⁻¹ := by rw [hg0x]
      _ = (f * x * f⁻¹) * (f * p * f⁻¹) := by group
      _ = x * (f * p * f⁻¹) := by rw [c.hfx]

theorem shift {g0 p : G}
    (hg0N : g0 ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
    (hg0V : ∀ w ∈ V, g0 * w * g0⁻¹ = w) (hp : p ∈ V) (hp1 : p ≠ 1)
    (hg0x : g0 * x * g0⁻¹ = x * p) :
    ∀ u ∈ V, ∃ g : G,
      g ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ∧
        (∀ w ∈ V, g * w * g⁻¹ = w) ∧ g * x * g⁻¹ = x * u := by
  obtain ⟨p1, p2, T⟩ := c.tri_y_exists hp hp1
  intro u hu
  rcases T.allV u hu with h | h | h | h
  · exact ⟨1, one_mem _, by simp, by rw [h]; simp⟩
  · exact ⟨g0, hg0N, hg0V, by rw [h]; exact hg0x⟩
  · obtain ⟨hN1, hV1, hx1⟩ := c.conj_step hg0N hg0V hg0x
    exact ⟨f * g0 * f⁻¹, hN1, hV1, by rw [h, ← T.f0]; exact hx1⟩
  · obtain ⟨hN1, hV1, hx1⟩ := c.conj_step hg0N hg0V hg0x
    obtain ⟨hN2, hV2, hx2⟩ := c.conj_step hN1 hV1 hx1
    exact ⟨f * (f * g0 * f⁻¹) * f⁻¹, hN2, hV2, by rw [h, ← T.f1, ← T.f0]; exact hx2⟩

theorem words : ∀ u ∈ V, ∃ g : G,
    g ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ∧
      (∀ w ∈ V, g * w * g⁻¹ = w) ∧ g * x * g⁻¹ = x * u := by
  obtain ⟨u0, hu0, hu01, hu⟩ := c.struct
  obtain ⟨y1, y2, T⟩ := c.tri_y_exists c.y_mem c.hy1
  have hyy : y * y = 1 := (c.hV.1 y c.y_mem).1
  have hy1y1 : y1 * y1 = 1 := (c.hV.1 y1 T.m1).1
  have hcomm : y * y1 = y1 * y := (c.hV.1 y c.y_mem).2 y1 T.m1
  have e1 : y * y2 = y1 := by
    rw [← T.m01, ← mul_assoc, hyy, one_mul]
  have e2 : y1 * y2 = y := by
    rw [← T.m01, ← mul_assoc, ← hcomm, mul_assoc, hy1y1, mul_one]
  have hs1V : a * y1 * a⁻¹ ∈ V := c.a_V T.m1
  have hs1_ne1 : a * y1 * a⁻¹ ≠ 1 := by
    intro h
    exact T.n1 (conj_inj a (h.trans (by group)))
  have hs1_ney : a * y1 * a⁻¹ ≠ y := by
    intro h
    exact T.d01 (conj_inj a (h.trans c.hya.symm)).symm
  rcases T.allV _ hs1V with h | h | h | h
  · exact absurd h hs1_ne1
  · exact absurd h hs1_ney
  ·
    have hcent : ∀ w ∈ V, a * w * a⁻¹ = w := by
      intro w hw
      rcases T.allV w hw with h' | h' | h' | h'
      · rw [h']; group
      · rw [h']; exact c.hya
      · rw [h']; exact h
      · rw [h', ← T.m01]
        calc a * (y * y1) * a⁻¹ = (a * y * a⁻¹) * (a * y1 * a⁻¹) := by group
          _ = y * y1 := by rw [c.hya, h]
    exact c.shift c.haN hcent hu0 hu01 hu
  · have hay2 : a * y2 * a⁻¹ = y1 := by
      rw [← T.m01]
      calc a * (y * y1) * a⁻¹ = (a * y * a⁻¹) * (a * y1 * a⁻¹) := by group
        _ = y * y2 := by rw [c.hya, h]
        _ = y1 := e1
    rcases T.allV u0 hu0 with h' | h' | h' | h'
    · exact absurd h' hu01
    ·
      obtain ⟨a1, ha1⟩ : ∃ a1 : G, a1 = f * a * f⁻¹ := ⟨_, rfl⟩
      obtain ⟨a2, ha2⟩ : ∃ a2 : G, a2 = f * a1 * f⁻¹ := ⟨_, rfl⟩
      have ha1N : a1 ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
        rw [ha1]; exact mul_mem (mul_mem c.hfN c.haN) (inv_mem c.hfN)
      have ha2N : a2 ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
        rw [ha2]; exact mul_mem (mul_mem c.hfN ha1N) (inv_mem c.hfN)
      have fy : f⁻¹ * y * f = y2 := by rw [← T.f2]; group
      have fy1 : f⁻¹ * y1 * f = y := by rw [← T.f0]; group
      have fy2 : f⁻¹ * y2 * f = y1 := by rw [← T.f1]; group
      have a1_x : a1 * x * a1⁻¹ = x * y1 := by
        rw [ha1]
        calc f * a * f⁻¹ * x * (f * a * f⁻¹)⁻¹ = f * (a * (f⁻¹ * x * f) * a⁻¹) * f⁻¹ := by group
          _ = f * (a * x * a⁻¹) * f⁻¹ := by rw [c.hfinvx]
          _ = f * (x * y) * f⁻¹ := by rw [hu, h']
          _ = (f * x * f⁻¹) * (f * y * f⁻¹) := by group
          _ = x * y1 := by rw [c.hfx, T.f0]
      have a1_y : a1 * y * a1⁻¹ = y2 := by
        rw [ha1]
        calc f * a * f⁻¹ * y * (f * a * f⁻¹)⁻¹ = f * (a * (f⁻¹ * y * f) * a⁻¹) * f⁻¹ := by group
          _ = f * (a * y2 * a⁻¹) * f⁻¹ := by rw [fy]
          _ = f * y1 * f⁻¹ := by rw [hay2]
          _ = y2 := T.f1
      have a1_y1 : a1 * y1 * a1⁻¹ = y1 := by
        rw [ha1]
        calc f * a * f⁻¹ * y1 * (f * a * f⁻¹)⁻¹ = f * (a * (f⁻¹ * y1 * f) * a⁻¹) * f⁻¹ := by group
          _ = f * (a * y * a⁻¹) * f⁻¹ := by rw [fy1]
          _ = f * y * f⁻¹ := by rw [c.hya]
          _ = y1 := T.f0
      have a1_y2 : a1 * y2 * a1⁻¹ = y := by
        rw [ha1]
        calc f * a * f⁻¹ * y2 * (f * a * f⁻¹)⁻¹ = f * (a * (f⁻¹ * y2 * f) * a⁻¹) * f⁻¹ := by group
          _ = f * (a * y1 * a⁻¹) * f⁻¹ := by rw [fy2]
          _ = f * y2 * f⁻¹ := by rw [h]
          _ = y := T.f2
      have a2_x : a2 * x * a2⁻¹ = x * y2 := by
        rw [ha2]
        calc f * a1 * f⁻¹ * x * (f * a1 * f⁻¹)⁻¹ = f * (a1 * (f⁻¹ * x * f) * a1⁻¹) * f⁻¹ := by group
          _ = f * (a1 * x * a1⁻¹) * f⁻¹ := by rw [c.hfinvx]
          _ = f * (x * y1) * f⁻¹ := by rw [a1_x]
          _ = (f * x * f⁻¹) * (f * y1 * f⁻¹) := by group
          _ = x * y2 := by rw [c.hfx, T.f1]
      have a2_y : a2 * y * a2⁻¹ = y1 := by
        rw [ha2]
        calc f * a1 * f⁻¹ * y * (f * a1 * f⁻¹)⁻¹ = f * (a1 * (f⁻¹ * y * f) * a1⁻¹) * f⁻¹ := by group
          _ = f * (a1 * y2 * a1⁻¹) * f⁻¹ := by rw [fy]
          _ = f * y * f⁻¹ := by rw [a1_y2]
          _ = y1 := T.f0
      have a2_y1 : a2 * y1 * a2⁻¹ = y := by
        rw [ha2]
        calc f * a1 * f⁻¹ * y1 * (f * a1 * f⁻¹)⁻¹ = f * (a1 * (f⁻¹ * y1 * f) * a1⁻¹) * f⁻¹ := by group
          _ = f * (a1 * y * a1⁻¹) * f⁻¹ := by rw [fy1]
          _ = f * y2 * f⁻¹ := by rw [a1_y]
          _ = y := T.f2
      have a2_y2 : a2 * y2 * a2⁻¹ = y2 := by
        rw [ha2]
        calc f * a1 * f⁻¹ * y2 * (f * a1 * f⁻¹)⁻¹ = f * (a1 * (f⁻¹ * y2 * f) * a1⁻¹) * f⁻¹ := by group
          _ = f * (a1 * y1 * a1⁻¹) * f⁻¹ := by rw [fy2]
          _ = f * y1 * f⁻¹ := by rw [a1_y1]
          _ = y2 := T.f1
      have hg0N : a * a1 * a2 * a1 ∈
          Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
        mul_mem (mul_mem (mul_mem c.haN ha1N) ha2N) ha1N
      have hconj : ∀ w : G, (a * a1 * a2 * a1) * w * (a * a1 * a2 * a1)⁻¹ =
          a * (a1 * (a2 * (a1 * w * a1⁻¹) * a2⁻¹) * a1⁻¹) * a⁻¹ := by
        intro w; group
      have hg0V : ∀ w ∈ V, (a * a1 * a2 * a1) * w * (a * a1 * a2 * a1)⁻¹ = w := by
        intro w hw
        rw [hconj]
        rcases T.allV w hw with h'' | h'' | h'' | h''
        · rw [h'']; group
        · rw [h'', a1_y, a2_y2, a1_y2, c.hya]
        · rw [h'', a1_y1, a2_y1, a1_y, hay2]
        · rw [h'', a1_y2, a2_y, a1_y1, h]
      have hg0x : (a * a1 * a2 * a1) * x * (a * a1 * a2 * a1)⁻¹ = x * y := by
        rw [hconj, a1_x]
        have s2 : a2 * (x * y1) * a2⁻¹ = x * y1 := by
          calc a2 * (x * y1) * a2⁻¹ = (a2 * x * a2⁻¹) * (a2 * y1 * a2⁻¹) := by group
            _ = (x * y2) * y := by rw [a2_x, a2_y1]
            _ = x * (y2 * y) := by rw [mul_assoc]
            _ = x * y1 := by rw [(c.hV.1 y2 T.m2).2 y c.y_mem, e1]
        have s3 : a1 * (x * y1) * a1⁻¹ = x := by
          calc a1 * (x * y1) * a1⁻¹ = (a1 * x * a1⁻¹) * (a1 * y1 * a1⁻¹) := by group
            _ = (x * y1) * y1 := by rw [a1_x, a1_y1]
            _ = x := by rw [mul_assoc, hy1y1, mul_one]
        rw [s2, s3, hu, h']
      exact c.shift hg0N hg0V c.y_mem c.hy1 hg0x
    ·
      have hg0N : a * a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
        mul_mem c.haN c.haN
      have hg0V : ∀ w ∈ V, (a * a) * w * (a * a)⁻¹ = w := by
        intro w hw
        rw [show (a * a) * w * (a * a)⁻¹ = a * (a * w * a⁻¹) * a⁻¹ by group]
        rcases T.allV w hw with h'' | h'' | h'' | h''
        · rw [h'']; group
        · rw [h'', c.hya, c.hya]
        · rw [h'', h, hay2]
        · rw [h'', hay2, h]
      have hg0x : (a * a) * x * (a * a)⁻¹ = x * y := by
        rw [show (a * a) * x * (a * a)⁻¹ = a * (a * x * a⁻¹) * a⁻¹ by group, hu, h']
        calc a * (x * y1) * a⁻¹ = (a * x * a⁻¹) * (a * y1 * a⁻¹) := by group
          _ = (x * y1) * y2 := by rw [hu, h', h]
          _ = x * (y1 * y2) := by rw [mul_assoc]
          _ = x * y := by rw [e2]
      exact c.shift hg0N hg0V c.y_mem c.hy1 hg0x
    ·
      have hg0N : a * a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
        mul_mem c.haN c.haN
      have hg0V : ∀ w ∈ V, (a * a) * w * (a * a)⁻¹ = w := by
        intro w hw
        rw [show (a * a) * w * (a * a)⁻¹ = a * (a * w * a⁻¹) * a⁻¹ by group]
        rcases T.allV w hw with h'' | h'' | h'' | h''
        · rw [h'']; group
        · rw [h'', c.hya, c.hya]
        · rw [h'', h, hay2]
        · rw [h'', hay2, h]
      have hg0x : (a * a) * x * (a * a)⁻¹ = x * y := by
        rw [show (a * a) * x * (a * a)⁻¹ = a * (a * x * a⁻¹) * a⁻¹ by group, hu, h']
        calc a * (x * y2) * a⁻¹ = (a * x * a⁻¹) * (a * y2 * a⁻¹) := by group
          _ = (x * y2) * y1 := by rw [hu, h', hay2]
          _ = x * (y2 * y1) := by rw [mul_assoc]
          _ = x * y := by rw [(c.hV.1 y2 T.m2).2 y1 T.m1, e2]
      exact c.shift hg0N hg0V c.y_mem c.hy1 hg0x

end Ctx

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
