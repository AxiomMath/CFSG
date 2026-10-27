module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Grp

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.L4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local.P27.Psp4

variable {G : Type} [Group G]

structure DataL4 (S P₁ P₂ : Subgroup G) (z t w : G) (a : ℕ) : Prop where
  z_mem : z ∈ S
  z_ord : orderOf z = 2
  z_cent : ∀ s ∈ S, s * z = z * s
  P₁_le : P₁ ≤ S
  P₂_le : P₂ ≤ S
  P₁_quat : IVK.IsQuaternionTwoGroup ↥P₁ a
  P₂_quat : IVK.IsQuaternionTwoGroup ↥P₂ a
  inter : P₁ ⊓ P₂ = zpowers z
  comm : ∀ p ∈ P₁, ∀ q ∈ P₂, p * q = q * p
  t_mem : t ∈ S
  t_inv : t * t = 1
  swap : ∀ p ∈ P₁, t * p * t⁻¹ ∈ P₂
  w_mem : w ∈ S
  w_inv : w * w = 1
  tw_comm : t * w = w * t
  idx : (P₁ ⊔ P₂).relIndex S = 4
  R_inf : (P₁ ⊔ P₂) ⊓ (zpowers t ⊔ zpowers w) = ⊥
  S_eq : S = (P₁ ⊔ P₂) ⊔ (zpowers t ⊔ zpowers w)
  w_norm : ∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁
  w_dih : ∃ (D : Type) (_ : Group D) (f : ↥(P₁ ⊔ zpowers w) →* D),
    Function.Surjective f ∧ f.ker = (zpowers z).subgroupOf (P₁ ⊔ zpowers w) ∧ IVK.IsDihedralTwoGroup D a

@[expose] def ZcL (R : Subgroup G) (z t w : G) : Set G :=
  {z} ∪ {y | ∃ r ∈ R, y = r * t * r⁻¹} ∪ {y | (∃ r ∈ R, y = r * w) ∧ y * y = 1} ∪
    {y | ∃ r ∈ R, y = r * (t * w) * r⁻¹}

@[expose] def XcL (R : Subgroup G) (z t w : G) : Set G :=
  {y | y ∈ R ∧ y * y = 1 ∧ y ≠ 1 ∧ y ≠ z} ∪ {y | ∃ r ∈ R, y = r * (t * z) * r⁻¹} ∪
    {y | ∃ r ∈ R, y = r * (t * w * z) * r⁻¹}

@[expose] def S0 (P₁ P₂ : Subgroup G) (t : G) : Subgroup G := (P₁ ⊔ P₂) ⊔ zpowers t

section Basic

variable {S P₁ P₂ : Subgroup G} {z t w : G} {a : ℕ}

theorem card_of_quat {P : Subgroup G} (h : IVK.IsQuaternionTwoGroup ↥P a) : Nat.card ↥P = 2 ^ a := by
  obtain ⟨h3, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
  simp [pow_succ]; ring

theorem conj_mul' (w p q : G) : w * (p * q) * w⁻¹ = (w * p * w⁻¹) * (w * q * w⁻¹) := by group

theorem conj_inv' (w p : G) : w * p⁻¹ * w⁻¹ = (w * p * w⁻¹)⁻¹ := by group

theorem z_mul_rr_left (z t p q : G) : z * rr t p q = rr t (z * p) q := by
  simp only [rr, mul_assoc]

namespace DataL4

variable (h : DataL4 S P₁ P₂ z t w a)

include h

theorem three_le : 3 ≤ a := h.P₁_quat.1

theorem t_inv' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_inv

theorem w_inv' : w⁻¹ = w := inv_eq_of_mul_eq_one_right h.w_inv

theorem wt_comm : w * t = t * w := h.tw_comm.symm

theorem z_sq : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.z_ord, pow_two] at this

theorem z_ne_one : z ≠ 1 := by
  intro hz
  have := h.z_ord
  rw [hz, orderOf_one] at this
  omega

theorem z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq

theorem z_mem₁ : z ∈ P₁ := by
  have : z ∈ P₁ ⊓ P₂ := by rw [h.inter]; exact mem_zpowers z
  exact this.1

theorem card_P₁ : Nat.card ↥P₁ = 2 ^ a := card_of_quat h.P₁_quat

theorem card_P₂ : Nat.card ↥P₂ = 2 ^ a := card_of_quat h.P₂_quat

theorem R_le_S : P₁ ⊔ P₂ ≤ S := sup_le h.P₁_le h.P₂_le

theorem sg_sg (g : G) : t * (t * g * t⁻¹) * t⁻¹ = g := by
  rw [h.t_inv']
  calc t * (t * g * t) * t = (t * t) * g * (t * t) := by simp only [mul_assoc]
    _ = g := by rw [h.t_inv, one_mul, mul_one]

theorem σ_mem₂ [Finite G] {q : G} (hq : q ∈ P₂) : t * q * t⁻¹ ∈ P₁ := by
  let f : G →* G := (MulAut.conj t).toMonoidHom
  have hle : P₁.map f ≤ P₂ := by
    rintro _ ⟨p, hp, rfl⟩
    exact h.swap p hp
  have hcard : Nat.card ↥P₂ ≤ Nat.card ↥(P₁.map f) := by
    rw [card_map_of_injective (f := f) (MulAut.conj t).injective, h.card_P₁, h.card_P₂]
  have heq : P₁.map f = P₂ := eq_of_le_of_card_ge hle hcard
  have : q ∈ P₁.map f := heq ▸ hq
  obtain ⟨p, hp, hpq⟩ := this
  have hpq' : t * p * t⁻¹ = q := hpq
  rw [← hpq', h.sg_sg]
  exact hp

theorem t_conj_R [Finite G] {r : G} (hr : r ∈ P₁ ⊔ P₂) : t * r * t⁻¹ ∈ P₁ ⊔ P₂ := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_commute h.comm).1 hr
  have e : t * (p * q) * t⁻¹ = (t * p * t⁻¹) * (t * q * t⁻¹) := by group
  rw [e]
  exact mul_mem (mem_sup_right (h.swap p hp)) (mem_sup_left (h.σ_mem₂ hq))

theorem w_conj_P₂ [Finite G] {q : G} (hq : q ∈ P₂) : w * q * w⁻¹ ∈ P₂ := by
  have h1 : t * q * t⁻¹ ∈ P₁ := h.σ_mem₂ hq
  have h2 : w * (t * q * t⁻¹) * w⁻¹ ∈ P₁ := h.w_norm _ h1
  have h3 : t * (w * (t * q * t⁻¹) * w⁻¹) * t⁻¹ ∈ P₂ := h.swap _ h2
  have e : t * (w * (t * q * t⁻¹) * w⁻¹) * t⁻¹ = w * q * w⁻¹ := by
    have hw : t * w = w * t := h.tw_comm
    calc t * (w * (t * q * t⁻¹) * w⁻¹) * t⁻¹ = (t * w) * t * q * ((t * w) * t)⁻¹ := by group
      _ = (w * t) * t * q * ((w * t) * t)⁻¹ := by rw [hw]
      _ = w * (t * t) * q * (w * (t * t))⁻¹ := by simp only [mul_assoc]
      _ = w * q * w⁻¹ := by rw [h.t_inv]; group
  rw [e] at h3
  exact h3

theorem w_conj_R [Finite G] {r : G} (hr : r ∈ P₁ ⊔ P₂) : w * r * w⁻¹ ∈ P₁ ⊔ P₂ := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_commute h.comm).1 hr
  have e : w * (p * q) * w⁻¹ = (w * p * w⁻¹) * (w * q * w⁻¹) := by group
  rw [e]
  exact mul_mem (mem_sup_left (h.w_norm p hp)) (mem_sup_right (h.w_conj_P₂ hq))

theorem t_w_conj : w * t * w⁻¹ = t := by
  rw [h.wt_comm]; group

theorem ω_ω (g : G) : w * (w * g * w⁻¹) * w⁻¹ = g := by
  rw [h.w_inv']
  calc w * (w * g * w) * w = (w * w) * g * (w * w) := by simp only [mul_assoc]
    _ = g := by rw [h.w_inv, one_mul, mul_one]

theorem ω_z : w * z * w⁻¹ = z := by
  rw [h.z_cent w h.w_mem, mul_assoc, mul_inv_cancel, mul_one]

theorem z_comm {g : G} (hg : g ∈ S) : z * g = g * z := (h.z_cent g hg).symm

theorem z_mem_R : z ∈ P₁ ⊔ P₂ := mem_sup_left h.z_mem₁

theorem R_mem_S {r : G} (hr : r ∈ P₁ ⊔ P₂) : r ∈ S := h.R_le_S hr

theorem conj_mul_z {g c : G} (hg : g ∈ S) (hc : c ∈ S) : g * (c * z) * g⁻¹ = z * (g * c * g⁻¹) := by
  calc g * (c * z) * g⁻¹ = g * (z * c) * g⁻¹ := by rw [h.z_cent c hc]
    _ = (g * z) * c * g⁻¹ := by simp only [mul_assoc]
    _ = (z * g) * c * g⁻¹ := by rw [h.z_cent g hg]
    _ = z * (g * c * g⁻¹) := by simp only [mul_assoc]

theorem ω_inv_mem {p : G} (hp : p ∈ P₁) : (w * p * w⁻¹)⁻¹ ∈ P₁ := inv_mem (h.w_norm p hp)

theorem S0_le_S : S0 P₁ P₂ t ≤ S := sup_le h.R_le_S ((zpowers_le).2 h.t_mem)

theorem t_not [Finite G] : t ∉ P₁ ⊔ P₂ := by
  intro ht
  have h1 : t ∈ (P₁ ⊔ P₂) ⊓ (zpowers t ⊔ zpowers w) := ⟨ht, mem_sup_left (mem_zpowers t)⟩
  rw [h.R_inf, mem_bot] at h1
  have hle : P₁ ≤ zpowers z := by
    intro p hp
    have h2 : t * p * t⁻¹ ∈ P₂ := h.swap p hp
    rw [h1] at h2
    simp only [one_mul, inv_one, mul_one] at h2
    rw [← h.inter]
    exact ⟨hp, h2⟩
  have hcard : Nat.card ↥P₁ ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hle
  rw [h.card_P₁, Nat.card_zpowers, h.z_ord] at hcard
  have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h.three_le
  omega

theorem relIndex_S0 [Finite G] : (P₁ ⊔ P₂).relIndex (S0 P₁ P₂ t) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_zpowers t), fun b hb => ?_⟩
  rcases (mem_sup_zpowers_iff (K := P₁ ⊔ P₂) (a := t) (fun k hk => h.t_conj_R hk)
    (by rw [h.t_inv]; exact one_mem _)).1 hb with hbR | ⟨k, hk, rfl⟩
  · refine Or.inr ⟨hbR, fun hbt => h.t_not ?_⟩
    have := mul_mem (inv_mem hbR) hbt
    simpa using this
  · refine Or.inl ⟨?_, fun hkt => h.t_not ?_⟩
    · rw [mul_assoc, h.t_inv, mul_one]; exact hk
    · have := mul_mem (inv_mem hk) hkt
      simpa using this

theorem w_ne_one [Finite G] : w ≠ 1 := by
  intro hw
  have e : S = S0 P₁ P₂ t := by
    rw [h.S_eq, S0, hw, zpowers_one_eq_bot, sup_bot_eq]
  have h4 := h.idx
  rw [e, h.relIndex_S0] at h4
  omega

theorem t_ne_w [Finite G] : t ≠ w := by
  intro htw
  have e : S = S0 P₁ P₂ t := by
    rw [h.S_eq, S0, ← htw, sup_idem]
  have h4 := h.idx
  rw [e, h.relIndex_S0] at h4
  omega

theorem w_not [Finite G] : w ∉ P₁ ⊔ P₂ := by
  intro hw
  have h1 : w ∈ (P₁ ⊔ P₂) ⊓ (zpowers t ⊔ zpowers w) := ⟨hw, mem_sup_right (mem_zpowers w)⟩
  rw [h.R_inf, mem_bot] at h1
  exact h.w_ne_one h1

theorem tw_not [Finite G] : t * w ∉ P₁ ⊔ P₂ := by
  intro htw
  have h1 : t * w ∈ (P₁ ⊔ P₂) ⊓ (zpowers t ⊔ zpowers w) :=
    ⟨htw, mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (mem_zpowers w))⟩
  rw [h.R_inf, mem_bot] at h1
  apply h.t_ne_w
  have : t = w⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this, h.w_inv']

omit h in
theorem t_mem_S0 : t ∈ S0 P₁ P₂ t := mem_sup_right (mem_zpowers t)

theorem toPsp4 [Finite G] : Data (S0 P₁ P₂ t) P₁ P₂ z t a where
  z_mem := mem_sup_left (mem_sup_left h.z_mem₁)
  z_ord := h.z_ord
  z_cent := fun s hs => h.z_cent s (h.S0_le_S hs)
  P₁_le := le_trans le_sup_left le_sup_left
  P₂_le := le_trans le_sup_right le_sup_left
  P₁_quat := h.P₁_quat
  P₂_quat := h.P₂_quat
  inter := h.inter
  comm := h.comm
  t_mem := t_mem_S0
  t_inv := h.t_inv
  t_not := h.t_not
  idx := h.relIndex_S0
  swap := h.swap

theorem unique_invol [Finite G] {x : G} (hx : x ∈ P₁) (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = z := by
  have hd := h.toPsp4
  obtain ⟨a₀, b₀, M, ha, hb, hM, hN, hqg, hspan⟩ := hd.exists_gens
  have hz : z = a₀ ^ (2 * M) := (hd.rel_of_gens ha hb hM hqg hspan).1
  have := hqg.eq_aN_of_involution (P := P₁) (by omega) hspan hx hx2 hx1
  rw [this, hz]

theorem rr_mem_S [Finite G] {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) : rr t p q ∈ S :=
  h.R_le_S (h.toPsp4.rr_mem_R hp hq)

theorem w_rr (p q : G) : w * rr t p q * w⁻¹ = rr t (w * p * w⁻¹) (w * q * w⁻¹) := by
  unfold rr
  have hw : t * w = w * t := h.tw_comm
  have e : w * (t * q * t⁻¹) * w⁻¹ = t * (w * q * w⁻¹) * t⁻¹ := by
    calc w * (t * q * t⁻¹) * w⁻¹ = (w * t) * q * (w * t)⁻¹ := by group
      _ = (t * w) * q * (t * w)⁻¹ := by rw [hw]
      _ = t * (w * q * w⁻¹) * t⁻¹ := by group
  calc w * (p * (t * q * t⁻¹)) * w⁻¹ = (w * p * w⁻¹) * (w * (t * q * t⁻¹) * w⁻¹) := by group
    _ = (w * p * w⁻¹) * (t * (w * q * w⁻¹) * t⁻¹) := by rw [e]

theorem mem_S_iff [Finite G] {s : G} : s ∈ S ↔ ∃ p ∈ P₁, ∃ q ∈ P₁,
    s = rr t p q ∨ s = rr t p q * t ∨ s = rr t p q * w ∨ s = rr t p q * (t * w) := by
  have hS : S = S0 P₁ P₂ t ⊔ zpowers w := by rw [h.S_eq, S0]; exact (sup_assoc _ _ _).symm
  have hconj : ∀ k ∈ S0 P₁ P₂ t, w * k * w⁻¹ ∈ S0 P₁ P₂ t := by
    have : S0 P₁ P₂ t ≤ (S0 P₁ P₂ t).comap (MulAut.conj w).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro r hr
        exact mem_sup_left (h.w_conj_R hr)
      · rw [zpowers_le]
        show w * t * w⁻¹ ∈ S0 P₁ P₂ t
        rw [h.t_w_conj]
        exact t_mem_S0
    exact fun k hk => this hk
  constructor
  · intro hs
    rw [hS] at hs
    rcases (mem_sup_zpowers_iff hconj (by rw [h.w_inv]; exact one_mem _)).1 hs with hs0 | ⟨k, hk, rfl⟩
    · obtain ⟨p, hp, q, hq, he⟩ := h.toPsp4.mem_S_iff.1 hs0
      exact ⟨p, hp, q, hq, he.elim Or.inl (fun e => Or.inr (Or.inl e))⟩
    · obtain ⟨p, hp, q, hq, he⟩ := h.toPsp4.mem_S_iff.1 hk
      refine ⟨p, hp, q, hq, ?_⟩
      rcases he with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (by rw [mul_assoc])))
  · rintro ⟨p, hp, q, hq, rfl | rfl | rfl | rfl⟩
    · exact h.rr_mem_S hp hq
    · exact mul_mem (h.rr_mem_S hp hq) h.t_mem
    · exact mul_mem (h.rr_mem_S hp hq) h.w_mem
    · exact mul_mem (h.rr_mem_S hp hq) (mul_mem h.t_mem h.w_mem)

theorem S_conj_R [Finite G] {s r : G} (hs : s ∈ S) (hr : r ∈ P₁ ⊔ P₂) : s * r * s⁻¹ ∈ P₁ ⊔ P₂ := by
  obtain ⟨p, hp, q, hq, rfl | rfl | rfl | rfl⟩ := h.mem_S_iff.1 hs
  · exact mul_mem (mul_mem (h.toPsp4.rr_mem_R hp hq) hr) (inv_mem (h.toPsp4.rr_mem_R hp hq))
  · have e : rr t p q * t * r * (rr t p q * t)⁻¹ = rr t p q * (t * r * t⁻¹) * (rr t p q)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (h.toPsp4.rr_mem_R hp hq) (h.t_conj_R hr)) (inv_mem (h.toPsp4.rr_mem_R hp hq))
  · have e : rr t p q * w * r * (rr t p q * w)⁻¹ = rr t p q * (w * r * w⁻¹) * (rr t p q)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (h.toPsp4.rr_mem_R hp hq) (h.w_conj_R hr)) (inv_mem (h.toPsp4.rr_mem_R hp hq))
  · have e : rr t p q * (t * w) * r * (rr t p q * (t * w))⁻¹ =
        rr t p q * (t * (w * r * w⁻¹) * t⁻¹) * (rr t p q)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (h.toPsp4.rr_mem_R hp hq) (h.t_conj_R (h.w_conj_R hr)))
      (inv_mem (h.toPsp4.rr_mem_R hp hq))

theorem tw_sq : (t * w) * (t * w) = 1 := by
  calc (t * w) * (t * w) = t * (w * t) * w := by simp only [mul_assoc]
    _ = t * (t * w) * w := by rw [h.wt_comm]
    _ = (t * t) * (w * w) := by simp only [mul_assoc]
    _ = 1 := by rw [h.t_inv, h.w_inv, mul_one]

theorem tw_inv' : (t * w)⁻¹ = t * w := inv_eq_of_mul_eq_one_right h.tw_sq

omit h in
theorem coset_ex {s τ₁ τ₂ : G} (h1 : s * τ₁ ∈ P₁ ⊔ P₂) (h2 : s * τ₂ ∈ P₁ ⊔ P₂) :
    τ₁⁻¹ * τ₂ ∈ P₁ ⊔ P₂ := by
  have := mul_mem (inv_mem h1) h2
  have e : (s * τ₁)⁻¹ * (s * τ₂) = τ₁⁻¹ * τ₂ := by group
  rwa [e] at this

theorem not_R_Rt [Finite G] {s : G} (h1 : s ∈ P₁ ⊔ P₂) (h2 : s * t ∈ P₁ ⊔ P₂) : False := by
  have := coset_ex (s := s) (τ₁ := 1) (τ₂ := t) (by simpa using h1) h2
  exact h.t_not (by simpa using this)

theorem not_R_Rw [Finite G] {s : G} (h1 : s ∈ P₁ ⊔ P₂) (h2 : s * w ∈ P₁ ⊔ P₂) : False := by
  have := coset_ex (s := s) (τ₁ := 1) (τ₂ := w) (by simpa using h1) h2
  exact h.w_not (by simpa using this)

theorem not_R_Rtw [Finite G] {s : G} (h1 : s ∈ P₁ ⊔ P₂) (h2 : s * (t * w) ∈ P₁ ⊔ P₂) : False := by
  have := coset_ex (s := s) (τ₁ := 1) (τ₂ := t * w) (by simpa using h1) h2
  exact h.tw_not (by simpa using this)

theorem not_Rt_Rw [Finite G] {s : G} (h1 : s * t ∈ P₁ ⊔ P₂) (h2 : s * w ∈ P₁ ⊔ P₂) : False := by
  have := coset_ex h1 h2
  rw [h.t_inv'] at this
  exact h.tw_not this

theorem not_Rt_Rtw [Finite G] {s : G} (h1 : s * t ∈ P₁ ⊔ P₂) (h2 : s * (t * w) ∈ P₁ ⊔ P₂) : False := by
  have := coset_ex h1 h2
  have e : t⁻¹ * (t * w) = w := by group
  rw [e] at this
  exact h.w_not this

theorem not_Rw_Rtw [Finite G] {s : G} (h1 : s * w ∈ P₁ ⊔ P₂) (h2 : s * (t * w) ∈ P₁ ⊔ P₂) : False := by
  have := coset_ex h1 h2
  have e : w⁻¹ * (t * w) = t := by rw [h.w_inv']; calc w * (t * w) = (w * t) * w := by rw [mul_assoc]
    _ = (t * w) * w := by rw [h.wt_comm]
    _ = t := by rw [mul_assoc, h.w_inv, mul_one]
  rw [e] at this
  exact h.t_not this

end DataL4

end Basic

end CFSG.GH74.GLS.Stage2.Local.P27.L4
