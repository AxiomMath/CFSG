module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Quat

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

structure Data (S P₁ P₂ : Subgroup G) (z t : G) (a : ℕ) : Prop where
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
  t_not : t ∉ P₁ ⊔ P₂
  idx : (P₁ ⊔ P₂).relIndex S = 2
  swap : ∀ p ∈ P₁, t * p * t⁻¹ ∈ P₂

@[expose] def Zc (R : Subgroup G) (z t : G) : Set G := {z} ∪ {y | ∃ r ∈ R, y = r * t * r⁻¹}

@[expose] def Xc (R : Subgroup G) (z t : G) : Set G :=
  {y | y ∈ R ∧ y * y = 1 ∧ y ≠ 1 ∧ y ≠ z} ∪ {y | ∃ r ∈ R, y = r * (t * z) * r⁻¹}

@[expose] def US (P₁ : Subgroup G) (t : G) : Subgroup G :=
  Subgroup.closure {g | ∃ q ∈ P₁, g = q * (t * q * t⁻¹)}

structure UHyp (S P₁ P₂ : Subgroup G) (z u : G) : Prop where
  mem : u ∈ P₁ ⊔ P₂
  sq : u * u = 1
  ne_one : u ≠ 1
  ne_z : u ≠ z
  norm : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z

@[expose] def Vset (S R : Subgroup G) (z t u : G) : Set G :=
  {w | w ∈ S ⊓ centralizer ({u} : Set G) ∧ w ∈ Zc R z t ∧ w ≠ z ∧ u * w ∈ Zc R z t}

@[expose] def rr (t p q : G) : G := p * (t * q * t⁻¹)

section Coords

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

namespace Data

theorem t_inv' (h : Data S P₁ P₂ z t a) : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_inv

theorem sg_sg (h : Data S P₁ P₂ z t a) (g : G) : t * (t * g * t⁻¹) * t⁻¹ = g := by
  rw [h.t_inv']
  calc t * (t * g * t) * t = (t * t) * g * (t * t) := by simp only [mul_assoc]
    _ = g := by rw [h.t_inv, one_mul, mul_one]

theorem z_sq (h : Data S P₁ P₂ z t a) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.z_ord, pow_two] at this

theorem z_ne_one (h : Data S P₁ P₂ z t a) : z ≠ 1 := by
  intro hz
  have := h.z_ord
  rw [hz, orderOf_one] at this
  omega

theorem z_inv (h : Data S P₁ P₂ z t a) : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq

theorem z_mem₁ (h : Data S P₁ P₂ z t a) : z ∈ P₁ := by
  have : z ∈ P₁ ⊓ P₂ := by rw [h.inter]; exact mem_zpowers z
  exact this.1

theorem σ_z (h : Data S P₁ P₂ z t a) : t * z * t⁻¹ = z := by
  have := h.z_cent t h.t_mem
  rw [this, mul_assoc, mul_inv_cancel, mul_one]

theorem z_cent' (h : Data S P₁ P₂ z t a) {g : G} (hg : g ∈ S) : z * g = g * z := (h.z_cent g hg).symm

theorem mem_inter_iff (h : Data S P₁ P₂ z t a) {g : G} (hg1 : g ∈ P₁) (hg2 : g ∈ P₂) :
    g = 1 ∨ g = z := by
  have : g ∈ P₁ ⊓ P₂ := ⟨hg1, hg2⟩
  rw [h.inter] at this
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 this
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [hm, ← two_mul, zpow_mul, zpow_two]
    simp [h.z_sq]
  · right
    rw [hm, zpow_add, zpow_mul, zpow_one, zpow_two]
    simp [h.z_sq]

theorem σ_mem₁ (h : Data S P₁ P₂ z t a) {p : G} (hp : p ∈ P₁) : t * p * t⁻¹ ∈ P₂ := h.swap p hp

theorem comm_σ (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    p * (t * q * t⁻¹) = (t * q * t⁻¹) * p := h.comm p hp _ (h.swap q hq)

theorem σ_mul (g g' : G) :
    t * (g * g') * t⁻¹ = (t * g * t⁻¹) * (t * g' * t⁻¹) := by
  group

theorem σ_inv (g : G) : t * g⁻¹ * t⁻¹ = (t * g * t⁻¹)⁻¹ := by
  group

theorem card_P₁ (h : Data S P₁ P₂ z t a) : Nat.card ↥P₁ = 2 ^ a := by
  obtain ⟨h3, ⟨e⟩⟩ := h.P₁_quat
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
  simp [pow_succ]; ring

theorem card_P₂ (h : Data S P₁ P₂ z t a) : Nat.card ↥P₂ = 2 ^ a := by
  obtain ⟨h3, ⟨e⟩⟩ := h.P₂_quat
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
  simp [pow_succ]; ring

theorem mem_sup_iff (h : Data S P₁ P₂ z t a) {g : G} :
    g ∈ P₁ ⊔ P₂ ↔ ∃ p ∈ P₁, ∃ q ∈ P₂, g = p * q := by
  constructor
  · intro hg
    let K : Subgroup G :=
      { carrier := {g | ∃ p ∈ P₁, ∃ q ∈ P₂, g = p * q}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
        mul_mem' := by
          rintro _ _ ⟨p, hp, q, hq, rfl⟩ ⟨p', hp', q', hq', rfl⟩
          refine ⟨p * p', mul_mem hp hp', q * q', mul_mem hq hq', ?_⟩
          have h1 : p' * q = q * p' := h.comm p' hp' q hq
          calc p * q * (p' * q') = p * (q * p') * q' := by simp only [mul_assoc]
            _ = p * (p' * q) * q' := by rw [h1]
            _ = p * p' * (q * q') := by simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨p, hp, q, hq, rfl⟩
          refine ⟨p⁻¹, inv_mem hp, q⁻¹, inv_mem hq, ?_⟩
          have h1 : p⁻¹ * q⁻¹ = q⁻¹ * p⁻¹ := h.comm p⁻¹ (inv_mem hp) q⁻¹ (inv_mem hq)
          rw [mul_inv_rev, h1] }
    have : P₁ ⊔ P₂ ≤ K := sup_le (fun p hp => ⟨p, hp, 1, one_mem _, (mul_one p).symm⟩)
      (fun q hq => ⟨1, one_mem _, q, hq, (one_mul q).symm⟩)
    exact this hg
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact mul_mem (mem_sup_left hp) (mem_sup_right hq)

theorem rr_mul (h : Data S P₁ P₂ z t a) {p q p' q' : G} (hq : q ∈ P₁) (hp' : p' ∈ P₁) :
    rr t p q * rr t p' q' = rr t (p * p') (q * q') := by
  unfold rr
  have h1 : (t * q * t⁻¹) * p' = p' * (t * q * t⁻¹) := (h.comm_σ hp' hq).symm
  calc p * (t * q * t⁻¹) * (p' * (t * q' * t⁻¹))
      = p * ((t * q * t⁻¹) * p') * (t * q' * t⁻¹) := by simp only [mul_assoc]
    _ = p * (p' * (t * q * t⁻¹)) * (t * q' * t⁻¹) := by rw [h1]
    _ = (p * p') * ((t * q * t⁻¹) * (t * q' * t⁻¹)) := by simp only [mul_assoc]
    _ = (p * p') * (t * (q * q') * t⁻¹) := by rw [Data.σ_mul]

theorem rr_one (t : G) : rr t 1 1 = 1 := by simp [rr]

theorem rr_inv (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    (rr t p q)⁻¹ = rr t p⁻¹ q⁻¹ := by
  unfold rr
  have hc : (t * q * t⁻¹)⁻¹ * p⁻¹ = p⁻¹ * (t * q * t⁻¹)⁻¹ := by
    have e := h.comm_σ hp hq
    generalize t * q * t⁻¹ = w at e ⊢
    rw [← mul_inv_rev, ← mul_inv_rev, e]
  rw [mul_inv_rev, hc, Data.σ_inv]

theorem σ_rr (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    t * rr t p q * t⁻¹ = rr t q p := by
  unfold rr
  rw [Data.σ_mul, h.sg_sg, h.comm_σ hq hp]

theorem rr_mul_t (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    t * rr t p q = rr t q p * t := by
  have := h.σ_rr hp hq
  calc t * rr t p q = (t * rr t p q * t⁻¹) * t := by rw [inv_mul_cancel_right]
    _ = rr t q p * t := by rw [this]

theorem rr_eq_iff (h : Data S P₁ P₂ z t a) {p q p' q' : G} (hp : p ∈ P₁) (hq : q ∈ P₁)
    (hp' : p' ∈ P₁) (hq' : q' ∈ P₁) :
    rr t p q = rr t p' q' ↔ (p' = p ∧ q' = q) ∨ (p' = z * p ∧ q' = z * q) := by
  have hσz : t⁻¹ * z * t = z := by
    have := h.σ_z
    rw [h.t_inv'] at this ⊢
    exact this
  constructor
  · intro he
    unfold rr at he
    have h1 : p'⁻¹ * p = t * (q' * q⁻¹) * t⁻¹ := by
      calc p'⁻¹ * p = p'⁻¹ * (p * (t * q * t⁻¹)) * (t * q * t⁻¹)⁻¹ := by group
        _ = p'⁻¹ * (p' * (t * q' * t⁻¹)) * (t * q * t⁻¹)⁻¹ := by rw [he]
        _ = (t * q' * t⁻¹) * (t * q * t⁻¹)⁻¹ := by group
        _ = t * (q' * q⁻¹) * t⁻¹ := by group
    have h2 : p'⁻¹ * p ∈ P₁ := mul_mem (inv_mem hp') hp
    have h3 : p'⁻¹ * p ∈ P₂ := by
      rw [h1]; exact h.swap _ (mul_mem hq' (inv_mem hq))
    have hq'q : q' * q⁻¹ = t⁻¹ * (p'⁻¹ * p) * t := by
      rw [h1]; group
    rcases h.mem_inter_iff h2 h3 with h4 | h4
    · left
      refine ⟨inv_mul_eq_one.1 h4, ?_⟩
      rw [h4] at hq'q
      have : q' * q⁻¹ = 1 := by rw [hq'q]; group
      exact mul_inv_eq_one.1 this
    · right
      have hp'z : p = p' * z := by rw [← h4]; group
      have hzp : z * p = p * z := h.z_cent' (h.P₁_le hp)
      refine ⟨?_, ?_⟩
      · calc p' = (p' * z) * z := by rw [mul_assoc, h.z_sq, mul_one]
          _ = p * z := by rw [← hp'z]
          _ = z * p := hzp.symm
      · rw [h4] at hq'q
        have h6 : q' * q⁻¹ = z := by rw [hq'q, hσz]
        calc q' = (q' * q⁻¹) * q := by group
          _ = z * q := by rw [h6]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · unfold rr
      have hz1 : t * (z * q) * t⁻¹ = z * (t * q * t⁻¹) := by
        rw [Data.σ_mul, h.σ_z]
      have hzp : z * p = p * z := h.z_cent' (h.P₁_le hp)
      calc p * (t * q * t⁻¹) = (z * z) * p * (t * q * t⁻¹) := by rw [h.z_sq, one_mul]
        _ = z * (z * p) * (t * q * t⁻¹) := by simp only [mul_assoc]
        _ = z * (p * z) * (t * q * t⁻¹) := by rw [hzp]
        _ = z * p * (z * (t * q * t⁻¹)) := by simp only [mul_assoc]
        _ = z * p * (t * (z * q) * t⁻¹) := by rw [hz1]

theorem R_le_S (h : Data S P₁ P₂ z t a) : P₁ ⊔ P₂ ≤ S := sup_le h.P₁_le h.P₂_le

end Data

end Coords

section CoordsFin

variable [Finite G] {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

namespace Data

theorem σ_mem₂ (h : Data S P₁ P₂ z t a) {q : G} (hq : q ∈ P₂) : t * q * t⁻¹ ∈ P₁ := by
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

theorem mem_R_iff (h : Data S P₁ P₂ z t a) {ρ : G} :
    ρ ∈ P₁ ⊔ P₂ ↔ ∃ p ∈ P₁, ∃ q ∈ P₁, ρ = rr t p q := by
  rw [h.mem_sup_iff]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    refine ⟨p, hp, t * q * t⁻¹, h.σ_mem₂ hq, ?_⟩
    unfold rr
    rw [h.sg_sg]
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, _, h.σ_mem₁ hq, rfl⟩

theorem rr_mem_R (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q ∈ P₁ ⊔ P₂ := h.mem_R_iff.2 ⟨p, hp, q, hq, rfl⟩

theorem mem_S_iff (h : Data S P₁ P₂ z t a) {s : G} :
    s ∈ S ↔ ∃ p ∈ P₁, ∃ q ∈ P₁, s = rr t p q ∨ s = rr t p q * t := by
  constructor
  · intro hs
    obtain ⟨g₀, hg₀, hX⟩ := Subgroup.relIndex_eq_two_iff.1 h.idx
    by_cases hsR : s ∈ P₁ ⊔ P₂
    · obtain ⟨p, hp, q, hq, rfl⟩ := h.mem_R_iff.1 hsR
      exact ⟨p, hp, q, hq, Or.inl rfl⟩
    · have h1 : s * g₀ ∈ P₁ ⊔ P₂ := by
        rcases hX s hs with ⟨h1, -⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd h1 hsR
      have h2 : t * g₀ ∈ P₁ ⊔ P₂ := by
        rcases hX t h.t_mem with ⟨h1, -⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd h1 h.t_not
      have h3 : s * t ∈ P₁ ⊔ P₂ := by
        have e : s * t = (s * g₀) * (t * g₀)⁻¹ := by
          calc s * t = s * t⁻¹ := by rw [h.t_inv']
            _ = (s * g₀) * (t * g₀)⁻¹ := by group
        rw [e]
        exact mul_mem h1 (inv_mem h2)
      obtain ⟨p, hp, q, hq, hpq⟩ := h.mem_R_iff.1 h3
      refine ⟨p, hp, q, hq, Or.inr ?_⟩
      rw [← hpq, mul_assoc, h.t_inv, mul_one]
  · rintro ⟨p, hp, q, hq, rfl | rfl⟩
    · exact h.R_le_S (h.rr_mem_R hp hq)
    · exact mul_mem (h.R_le_S (h.rr_mem_R hp hq)) h.t_mem

omit [Finite G] in
theorem exists_gens (h : Data S P₁ P₂ z t a) :
    ∃ (a₀ b₀ : G) (M : ℕ), a₀ ∈ P₁ ∧ b₀ ∈ P₁ ∧ 1 ≤ M ∧ 2 * M = 2 ^ (a - 2) ∧ QG a₀ b₀ (2 * M) ∧
      ∀ x ∈ P₁, ∃ k : ℕ, x = a₀ ^ k ∨ x = a₀ ^ k * b₀ := by
  obtain ⟨h3, ⟨e⟩⟩ := h.P₁_quat
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 3 := ⟨a - 3, by omega⟩
  have hN : 2 ^ (k + 3 - 2) = 2 * 2 ^ k := by
    rw [show k + 3 - 2 = k + 1 by omega, pow_succ]; ring
  have : NeZero (2 ^ (k + 3 - 2)) := ⟨by positivity⟩
  obtain ⟨a₀, b₀, ha, hb, hqg, hspan⟩ := quat_gens e
  refine ⟨a₀, b₀, 2 ^ k, ha, hb, Nat.one_le_two_pow, hN.symm, ?_, hspan⟩
  rw [← hN]
  exact hqg

end Data

end CoordsFin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
