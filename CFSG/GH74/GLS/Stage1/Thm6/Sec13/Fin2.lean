module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin1

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

structure Z4Data (H₀ : Subgroup G) (a b : G) : Prop where
  ha : a ^ 4 = 1
  hb : b ^ 4 = 1
  hab : a * b = b * a
  gen : Subgroup.closure ({a, b} : Set G) = H₀
  card : Nat.card H₀ = 16

namespace Z4Data

variable {H₀ : Subgroup G} {a b : G} (d : Z4Data H₀ a b)
include d

theorem a_mem : a ∈ H₀ := d.gen ▸ Subgroup.subset_closure (by simp)
theorem b_mem : b ∈ H₀ := d.gen ▸ Subgroup.subset_closure (by simp)

theorem mem_iff {g : G} : g ∈ H₀ ↔ ∃ i j : ℕ, g = a ^ i * b ^ j := by
  constructor
  · intro hg
    rw [← d.gen] at hg
    exact mem_closure_pair d.ha d.hb d.hab hg
  · rintro ⟨i, j, rfl⟩
    exact H₀.mul_mem (H₀.pow_mem d.a_mem i) (H₀.pow_mem d.b_mem j)

theorem comm {p q : G} (hp : p ∈ H₀) (hq : q ∈ H₀) : p * q = q * p := by
  obtain ⟨i, j, rfl⟩ := d.mem_iff.1 hp
  obtain ⟨k, l, rfl⟩ := d.mem_iff.1 hq
  have hc : ∀ i j : ℕ, Commute (a ^ i) (b ^ j) :=
    fun i j => (Commute.pow_pow (show Commute a b from d.hab) i j)
  have hc2 : Commute (a ^ i * b ^ j) (a ^ k * b ^ l) := by
    apply Commute.mul_left <;> apply Commute.mul_right
    · exact (Commute.pow_pow_self a i k)
    · exact hc i l
    · exact (hc k j).symm
    · exact (Commute.pow_pow_self b j l)
  exact hc2.eq

theorem sq_one [Finite G] {h : G} (hh : h ∈ H₀) (h2 : h * h = 1) :
    h = 1 ∨ h = a ^ 2 ∨ h = b ^ 2 ∨ h = a ^ 2 * b ^ 2 :=
  z4_sq_one d.ha d.hb d.hab (by rw [d.gen]; exact d.card) (d.gen ▸ hh) h2

theorem a2_ne_one [Finite G] : a ^ 2 ≠ 1 := by
  intro h
  have := z4_inj d.ha d.hb d.hab (by rw [d.gen]; exact d.card) 2 0 0 0 (by simpa using h)
  omega

theorem b2_ne_one [Finite G] : b ^ 2 ≠ 1 := by
  intro h
  have := z4_inj d.ha d.hb d.hab (by rw [d.gen]; exact d.card) 0 2 0 0 (by simpa using h)
  omega

theorem a2_ne_b2 [Finite G] : a ^ 2 ≠ b ^ 2 := by
  intro h
  have := z4_inj d.ha d.hb d.hab (by rw [d.gen]; exact d.card) 2 0 0 2 (by simpa using h)
  omega

theorem z_ne_one [Finite G] : a ^ 2 * b ^ 2 ≠ 1 := by
  intro h
  have := z4_inj d.ha d.hb d.hab (by rw [d.gen]; exact d.card) 2 2 0 0 (by simpa using h)
  omega

theorem a2_ne_z [Finite G] : a ^ 2 ≠ a ^ 2 * b ^ 2 := by
  intro h
  have := z4_inj d.ha d.hb d.hab (by rw [d.gen]; exact d.card) 2 0 2 2 (by simpa using h)
  omega

theorem b2_mem : b ^ 2 ∈ H₀ := H₀.pow_mem d.b_mem 2

theorem tab_aa : a ^ 2 * a ^ 2 = 1 := by rw [← pow_add]; exact d.ha
theorem tab_bb : b ^ 2 * b ^ 2 = 1 := by rw [← pow_add]; exact d.hb
theorem tab_ba : b ^ 2 * a ^ 2 = a ^ 2 * b ^ 2 :=
  (Commute.pow_pow (show Commute a b from d.hab) 2 2).symm.eq
theorem tab_za : a ^ 2 * b ^ 2 * a ^ 2 = b ^ 2 := by
  rw [mul_assoc, d.tab_ba, ← mul_assoc, d.tab_aa, one_mul]
theorem tab_zb : a ^ 2 * b ^ 2 * b ^ 2 = a ^ 2 := by
  rw [mul_assoc, d.tab_bb, mul_one]
theorem tab_bz : b ^ 2 * (a ^ 2 * b ^ 2) = a ^ 2 := by
  rw [← mul_assoc, d.tab_ba, d.tab_zb]
theorem tab_zz : a ^ 2 * b ^ 2 * (a ^ 2 * b ^ 2) = 1 := by
  rw [mul_assoc, d.tab_bz, d.tab_aa]

end Z4Data

theorem ncard_le_three {α : Type*} [Finite α] {s : Set α} {p q r : α}
    (h : ∀ v ∈ s, v = p ∨ v = q ∨ v = r) : s.ncard ≤ 3 := by
  classical
  have h1 : s ⊆ ((({p, q, r} : Finset α)) : Set α) := by
    intro v hv; simpa using h v hv
  calc s.ncard ≤ ((({p, q, r} : Finset α)) : Set α).ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
    _ = ({p, q, r} : Finset α).card := Set.ncard_coe_finset _
    _ ≤ 3 := Finset.card_le_three

namespace Z4Data

variable {H₀ : Subgroup G} {a b : G} (d : Z4Data H₀ a b)
include d

theorem V_mem [Finite G] {V : Subgroup G} (hVH : V ≤ H₀) (hV4 : Nat.card V = 4)
    (hVsq : ∀ v ∈ V, v * v = 1) : a ^ 2 ∈ V ∧ b ^ 2 ∈ V ∧ a ^ 2 * b ^ 2 ∈ V := by
  have hsub : ∀ v ∈ V, v = 1 ∨ v = a ^ 2 ∨ v = b ^ 2 ∨ v = a ^ 2 * b ^ 2 :=
    fun v hv => d.sq_one (hVH hv) (hVsq v hv)
  have hcard : ∀ {p q r : G}, (∀ v ∈ V, v = p ∨ v = q ∨ v = r) → False := by
    intro p q r h
    have := ncard_le_three (s := (V : Set G)) h
    have h4 : (V : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hV4
    omega
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    apply hcard (p := 1) (q := b ^ 2) (r := a ^ 2 * b ^ 2)
    intro v hv
    rcases hsub v hv with h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hv) hn
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_contra hn
    apply hcard (p := 1) (q := a ^ 2) (r := a ^ 2 * b ^ 2)
    intro v hv
    rcases hsub v hv with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (h ▸ hv) hn
    · exact Or.inr (Or.inr h)
  · by_contra hn
    apply hcard (p := 1) (q := a ^ 2) (r := b ^ 2)
    intro v hv
    rcases hsub v hv with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd (h ▸ hv) hn

end Z4Data

structure XCtx (H₀ V : Subgroup G) (a b x y f : G) : Prop where
  z4 : Z4Data H₀ a b
  xN : ∀ q ∈ H₀, x * q * x⁻¹ ∈ H₀
  xx : x * x = 1
  xV : ∀ v ∈ V, x * v = v * x
  Cx : ∀ h ∈ H₀, x * h = h * x → h ∈ V
  VH : V ≤ H₀
  Vsq : ∀ v ∈ V, v * v = 1
  yN : ∀ q ∈ H₀, y * q * y⁻¹ ∈ H₀
  ya : y * a * y⁻¹ = b
  yb : y * b * y⁻¹ = a
  xy : x * y * x⁻¹ * y⁻¹ ∈ H₀
  fN : ∀ q ∈ H₀, f * q * f⁻¹ ∈ H₀
  fx : f * x = x * f
  fV : ∀ v ∈ V, f * v * f⁻¹ ∈ V
  ffix : ∀ v ∈ V, f * v * f⁻¹ = v → v = 1
  a2V : a ^ 2 ∈ V
  b2V : b ^ 2 ∈ V
  zV : a ^ 2 * b ^ 2 ∈ V
  Vsub : ∀ v ∈ V, v = 1 ∨ v = a ^ 2 ∨ v = b ^ 2 ∨ v = a ^ 2 * b ^ 2

@[expose] def uu (x : G) (h : G) : G := h * (x * h * x⁻¹)

theorem uu_one (x : G) : uu x (1 : G) = 1 := by simp [uu]

namespace XCtx

variable {H₀ V : Subgroup G} {a b x y f : G} (c : XCtx H₀ V a b x y f)
include c

theorem conjx_conjx (h : G) : x * (x * h * x⁻¹) * x⁻¹ = h := by
  have h1 : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, c.xx, inv_one]
  calc x * (x * h * x⁻¹) * x⁻¹ = (x * x) * h * (x⁻¹ * x⁻¹) := by group
    _ = h := by rw [c.xx, h1]; group

theorem u_mem {h : G} (hh : h ∈ H₀) : uu x h ∈ V := by
  apply c.Cx _ (H₀.mul_mem hh (c.xN h hh))
  have h1 : x * (h * (x * h * x⁻¹)) * x⁻¹ = (x * h * x⁻¹) * (x * (x * h * x⁻¹) * x⁻¹) := by group
  rw [c.conjx_conjx] at h1
  have h2 : x * (h * (x * h * x⁻¹)) * x⁻¹ = h * (x * h * x⁻¹) := by
    rw [h1]; exact (c.z4.comm hh (c.xN h hh)).symm
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem u_mul {h k : G} (hh : h ∈ H₀) (hk : k ∈ H₀) : uu x (h * k) = uu x h * uu x k := by
  unfold uu
  have hc1 := c.z4.comm hk (c.xN h hh)
  calc h * k * (x * (h * k) * x⁻¹) = h * k * ((x * h * x⁻¹) * (x * k * x⁻¹)) := by group
    _ = h * (k * (x * h * x⁻¹)) * (x * k * x⁻¹) := by group
    _ = h * ((x * h * x⁻¹) * k) * (x * k * x⁻¹) := by rw [hc1]
    _ = h * (x * h * x⁻¹) * (k * (x * k * x⁻¹)) := by group

theorem u_V {v : G} (hv : v ∈ V) : uu x v = 1 := by
  unfold uu
  have h1 : x * v * x⁻¹ = v := by
    have := c.xV v hv
    rw [this]; group
  rw [h1]
  exact c.Vsq v hv

theorem u_inv {h : G} (hh : h ∈ H₀) : uu x h⁻¹ = (uu x h)⁻¹ := by
  have := c.u_mul (H₀.inv_mem hh) hh
  rw [inv_mul_cancel, uu_one] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem inv_mem_V [Finite G] {q : G} (hq : q ∈ H₀) (h2 : q * q = 1) : q ∈ V := by
  rcases c.z4.sq_one hq h2 with h | h | h | h <;> rw [h]
  exacts [V.one_mem, c.a2V, c.b2V, c.zV]

theorem u_eq_of_sq [Finite G] {h h' : G} (hh : h ∈ H₀) (hh' : h' ∈ H₀) (e : h * h = h' * h') :
    uu x h = uu x h' := by
  have hc := c.z4.comm hh (H₀.inv_mem hh')
  have hsq : (h * h'⁻¹) * (h * h'⁻¹) = 1 := by
    calc h * h'⁻¹ * (h * h'⁻¹) = h * (h'⁻¹ * h) * h'⁻¹ := by group
      _ = h * (h * h'⁻¹) * h'⁻¹ := by rw [← hc]
      _ = h * h * (h'⁻¹ * h'⁻¹) := by group
      _ = h' * h' * (h'⁻¹ * h'⁻¹) := by rw [e]
      _ = 1 := by group
  have hV : h * h'⁻¹ ∈ V := c.inv_mem_V (H₀.mul_mem hh (H₀.inv_mem hh')) hsq
  have h1 := c.u_V hV
  rw [c.u_mul hh (H₀.inv_mem hh'), c.u_inv hh'] at h1
  exact mul_inv_eq_one.1 h1

theorem u_sigma {h : G} (hh : h ∈ H₀) : uu x (y * h * y⁻¹) = y * uu x h * y⁻¹ := by
  have hκ := c.xy
  have hm : y * (x * h * x⁻¹) * y⁻¹ ∈ H₀ := c.yN _ (c.xN h hh)
  have hcomm := c.z4.comm hκ hm
  have key : x * (y * h * y⁻¹) * x⁻¹ = y * (x * h * x⁻¹) * y⁻¹ := by
    have e : x * (y * h * y⁻¹) * x⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * h * x⁻¹) * y⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
    rw [e, hcomm]; group
  unfold uu
  rw [key]; group

theorem u_f (h : G) : uu x (f * h * f⁻¹) = f * uu x h * f⁻¹ := by
  have hfx : f * x * f⁻¹ = x := mul_inv_eq_iff_eq_mul.2 c.fx
  unfold uu
  calc f * h * f⁻¹ * (x * (f * h * f⁻¹) * x⁻¹)
      = f * h * f⁻¹ * ((f * x * f⁻¹) * (f * h * f⁻¹) * (f * x * f⁻¹)⁻¹) := by rw [hfx]
    _ = f * (h * (x * h * x⁻¹)) * f⁻¹ := by group

theorem u_pow {g : G} (hg : g ∈ H₀) (n : ℕ) : uu x (g ^ n) = (uu x g) ^ n := by
  induction n with
  | zero => simp [uu]
  | succ n ih =>
    rw [pow_succ, c.u_mul (H₀.pow_mem hg n) hg, ih, pow_succ]

theorem f_cases [Finite G] :
    (f * a ^ 2 * f⁻¹ = b ^ 2 ∧ f * b ^ 2 * f⁻¹ = a ^ 2 * b ^ 2 ∧
      f * (a ^ 2 * b ^ 2) * f⁻¹ = a ^ 2) ∨
    (f * a ^ 2 * f⁻¹ = a ^ 2 * b ^ 2 ∧ f * b ^ 2 * f⁻¹ = a ^ 2 ∧
      f * (a ^ 2 * b ^ 2) * f⁻¹ = b ^ 2) := by
  have hinj : ∀ p q : G, f * p * f⁻¹ = f * q * f⁻¹ → p = q := fun p q h =>
    mul_left_cancel (mul_right_cancel h)
  have hp : f * a ^ 2 * f⁻¹ ∈ V := c.fV _ c.a2V
  have hq : f * b ^ 2 * f⁻¹ ∈ V := c.fV _ c.b2V
  have hr : f * (a ^ 2 * b ^ 2) * f⁻¹ = (f * a ^ 2 * f⁻¹) * (f * b ^ 2 * f⁻¹) := by group
  have hpa : f * a ^ 2 * f⁻¹ ≠ a ^ 2 := fun h => c.z4.a2_ne_one (c.ffix _ c.a2V h)
  have hqb : f * b ^ 2 * f⁻¹ ≠ b ^ 2 := fun h => c.z4.b2_ne_one (c.ffix _ c.b2V h)
  have hp1 : f * a ^ 2 * f⁻¹ ≠ 1 := by
    intro h; apply c.z4.a2_ne_one; apply hinj; rw [h]; group
  have hq1 : f * b ^ 2 * f⁻¹ ≠ 1 := by
    intro h; apply c.z4.b2_ne_one; apply hinj; rw [h]; group
  have hpq : f * a ^ 2 * f⁻¹ ≠ f * b ^ 2 * f⁻¹ := fun h => c.z4.a2_ne_b2 (hinj _ _ h)
  have hrz : f * (a ^ 2 * b ^ 2) * f⁻¹ ≠ a ^ 2 * b ^ 2 :=
    fun h => c.z4.z_ne_one (c.ffix _ c.zV h)
  rcases c.Vsub _ hp with h1 | h1 | h1 | h1
  · exact absurd h1 hp1
  · exact absurd h1 hpa
  · left
    rcases c.Vsub _ hq with h2 | h2 | h2 | h2
    · exact absurd h2 hq1
    · exfalso; apply hrz; rw [hr, h1, h2, c.z4.tab_ba]
    · exact absurd h2 hqb
    · exact ⟨h1, h2, by rw [hr, h1, h2, c.z4.tab_bz]⟩
  · right
    rcases c.Vsub _ hq with h2 | h2 | h2 | h2
    · exact absurd h2 hq1
    · exact ⟨h1, h2, by rw [hr, h1, h2, c.z4.tab_za]⟩
    · exact absurd h2 hqb
    · exact absurd (h1.trans h2.symm) hpq

theorem x_inverts [Finite G] : ∀ h ∈ H₀, x * h * x⁻¹ = h⁻¹ := by
  have haH := c.z4.a_mem
  have hbH := c.z4.b_mem
  have hfa : f * a * f⁻¹ ∈ H₀ := c.fN a haH
  have hwV : uu x a ∈ V := c.u_mem haH
  have hub : uu x b = y * uu x a * y⁻¹ := by rw [← c.u_sigma haH, c.ya]
  have hu1 : uu x (f * a * f⁻¹) = f * uu x a * f⁻¹ := c.u_f a
  have hab2 : (a * b) * (a * b) = a ^ 2 * b ^ 2 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← c.z4.hab]
      _ = a ^ 2 * b ^ 2 := by simp only [pow_two]; group
  have hya2 : y * a ^ 2 * y⁻¹ = b ^ 2 := by
    calc y * a ^ 2 * y⁻¹ = (y * a * y⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = b ^ 2 := by rw [c.ya]
  have hyb2 : y * b ^ 2 * y⁻¹ = a ^ 2 := by
    calc y * b ^ 2 * y⁻¹ = (y * b * y⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = a ^ 2 := by rw [c.yb]
  have hyz : y * (a ^ 2 * b ^ 2) * y⁻¹ = a ^ 2 * b ^ 2 := by
    rw [show y * (a ^ 2 * b ^ 2) * y⁻¹ = (y * a ^ 2 * y⁻¹) * (y * b ^ 2 * y⁻¹) by group, hya2,
      hyb2, c.z4.tab_ba]
  have hsqf : (f * a * f⁻¹) * (f * a * f⁻¹) = f * a ^ 2 * f⁻¹ := by
    simp only [pow_two]; group
  have hw : uu x a = 1 ∨ uu x a = a ^ 2 := by
    rcases c.f_cases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have e1 : (f * a * f⁻¹) * (f * a * f⁻¹) = b * b := by
        rw [hsqf, h1]; exact pow_two b
      have := c.u_eq_of_sq hfa hbH e1
      rw [hu1, hub] at this
      rcases c.Vsub _ hwV with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; rw [h, h2, hyb2] at this; exact c.z4.a2_ne_z this.symm
      · exfalso; rw [h, h3, hyz] at this; exact c.z4.a2_ne_z this
    · have e1 : (f * a * f⁻¹) * (f * a * f⁻¹) = (a * b) * (a * b) := by
        rw [hsqf, h1, hab2]
      have := c.u_eq_of_sq hfa (H₀.mul_mem haH hbH) e1
      rw [hu1, c.u_mul haH hbH, hub] at this
      rcases c.Vsub _ hwV with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; rw [h, h2, hyb2, c.z4.tab_ba] at this; exact c.z4.a2_ne_z this
      · exfalso; rw [h, h3, hyz, c.z4.tab_zz] at this; exact c.z4.b2_ne_one this
  rcases hw with hw1 | hw2
  · have hub1 : uu x b = 1 := by rw [hub, hw1]; group
    intro h hh
    obtain ⟨i, j, rfl⟩ := c.z4.mem_iff.1 hh
    have : uu x (a ^ i * b ^ j) = 1 := by
      rw [c.u_mul (H₀.pow_mem haH i) (H₀.pow_mem hbH j), c.u_pow haH, c.u_pow hbH, hw1, hub1]
      simp
    unfold uu at this
    exact eq_inv_of_mul_eq_one_right this
  · exfalso
    have h1 : a * (x * a * x⁻¹) = a * a := by
      have := hw2
      unfold uu at this
      rw [this]; exact pow_two a
    have h2 : x * a * x⁻¹ = a := mul_left_cancel h1
    have h3 : x * a = a * x := mul_inv_eq_iff_eq_mul.1 h2
    have haV : a ∈ V := c.Cx a haH h3
    exact c.z4.a2_ne_one (by rw [pow_two]; exact c.Vsq a haV)

end XCtx

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
