module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup

theorem quaternion_inverter {n : ℕ} (hn : 2 ∣ n) (g : QuaternionGroup n) :
    ∃ p : QuaternionGroup n, p ^ 2 = QuaternionGroup.a (n : ZMod (2 * n)) ∧ p * g * p⁻¹ = g⁻¹ := by
  obtain ⟨m, hm⟩ := hn
  have h2n : (n : ZMod (2 * n)) + n = 0 := by
    rw [← Nat.cast_add, ← two_mul]
    exact ZMod.natCast_self (2 * n)
  have hmm : (m : ZMod (2 * n)) + m = n := by
    rw [← Nat.cast_add, ← two_mul, ← hm]
  cases g with
  | a i =>
    refine ⟨QuaternionGroup.xa 0, QuaternionGroup.xa_sq 0, ?_⟩
    have hinv : (QuaternionGroup.a i)⁻¹ = QuaternionGroup.a (-i) :=
      inv_eq_of_mul_eq_one_right (by
        rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
        congr 1
        ring)
    rw [hinv, mul_inv_eq_iff_eq_mul, QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
    congr 1
    ring
  | xa j =>
    refine ⟨QuaternionGroup.a (m : ZMod (2 * n)), ?_, ?_⟩
    · rw [sq, QuaternionGroup.a_mul_a, hmm]
    · have hinv : (QuaternionGroup.xa j)⁻¹ = QuaternionGroup.xa ((n : ZMod (2 * n)) + j) :=
        inv_eq_of_mul_eq_one_right (by
          rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.one_def]
          congr 1
          linear_combination h2n)
      rw [hinv, mul_inv_eq_iff_eq_mul, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
      congr 1
      linear_combination -hmm - h2n

theorem q8_zsq : (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) : QuaternionGroup 2) *
    QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) = 1 := by decide

theorem q8_inv : ∀ x : QuaternionGroup 2, x * x = 1 →
    x = 1 ∨ x = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by
  decide

theorem q8_sq : ∀ x : QuaternionGroup 2, x ^ 2 = 1 ∨
    x ^ 2 = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by
  decide

theorem q8_cen : ∀ x y : QuaternionGroup 2,
    x ^ 2 = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) → y * x = x * y →
    y = 1 ∨ y = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) ∨ y = x ∨
      y = x * QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by
  decide

structure IsQ8Like {T : Type} [Group T] (R : Subgroup T) (z : T) : Prop where
  z_mem : z ∈ R
  z_sq : z * z = 1
  inv : ∀ r ∈ R, r * r = 1 → r = 1 ∨ r = z
  sq : ∀ r ∈ R, r ^ 2 = 1 ∨ r ^ 2 = z
  inverter : ∀ r ∈ R, r ^ 2 = z → ∃ s ∈ R, s ^ 2 = z ∧ s * r * s⁻¹ = r⁻¹
  cen : ∀ r₁ ∈ R, r₁ ^ 2 = z → ∀ r ∈ R, r * r₁ = r₁ * r → r = 1 ∨ r = z ∨ r = r₁ ∨ r = r₁ * z

theorem IsQ8Like.of_injective {T : Type} [Group T] (ι : QuaternionGroup 2 →* T)
    (hι : Function.Injective ι) :
    IsQ8Like ι.range (ι (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)))) := by
  have hmem : ∀ r ∈ ι.range, ∃ x, ι x = r := fun r hr => MonoidHom.mem_range.mp hr
  refine ⟨MonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, q8_zsq, map_one]
  · intro r hr hrr
    obtain ⟨x, rfl⟩ := hmem r hr
    rw [← map_mul, ← map_one ι] at hrr
    rcases q8_inv x (hι hrr) with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
  · intro r hr
    obtain ⟨x, rfl⟩ := hmem r hr
    rcases q8_sq x with h | h
    · left
      rw [← map_pow, h, map_one]
    · right
      rw [← map_pow, h]
  · intro r hr hr2
    obtain ⟨x, rfl⟩ := hmem r hr
    obtain ⟨p, hp2, hp⟩ := quaternion_inverter (n := 2) (dvd_refl 2) x
    refine ⟨ι p, MonoidHom.mem_range.mpr ⟨p, rfl⟩, ?_, ?_⟩
    · rw [← map_pow, hp2]
    · have := congrArg ι hp
      simpa [map_mul, map_inv] using this
  · intro r₁ hr₁ hr₁2 r hr hcomm
    obtain ⟨x, rfl⟩ := hmem r₁ hr₁
    obtain ⟨y, rfl⟩ := hmem r hr
    have hx2 : x ^ 2 = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) :=
      hι (by rw [map_pow]; exact hr₁2)
    have hcy : y * x = x * y := hι (by rw [map_mul, map_mul]; exact hcomm)
    rcases q8_cen x y hx2 hcy with h | h | h | h
    · left
      rw [h, map_one]
    · right
      left
      rw [h]
    · right
      right
      left
      rw [h]
    · right
      right
      right
      rw [h, map_mul]

structure QPair {T : Type} [Group T] (R Q : Subgroup T) (z : T) : Prop where
  q8 : IsQ8Like R z
  z_Q : z ∈ Q
  comm : ∀ r ∈ R, ∀ q ∈ Q, r * q = q * r
  Q_inv : ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z

section Pair

variable {T : Type} [Group T] {R Q : Subgroup T} {z : T}

theorem mul_self_mul_of_comm {a b : T} (hab : a * b = b * a) :
    (a * b) * (a * b) = (a * a) * (b * b) := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by group

theorem QPair.mul_sq_mem (h : QPair R Q z) {r₁ r₂ q₁ q₂ : T} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R)
    (hq₁ : q₁ ∈ Q) (hq₂ : q₂ ∈ Q) :
    ((r₁ * q₁) * (r₂ * q₂)) * ((r₁ * q₁) * (r₂ * q₂)) ∈ Q := by
  have h1 : (r₁ * q₁) * (r₂ * q₂) = (r₁ * r₂) * (q₁ * q₂) := by
    calc (r₁ * q₁) * (r₂ * q₂) = r₁ * (q₁ * r₂) * q₂ := by group
      _ = r₁ * (r₂ * q₁) * q₂ := by rw [← h.comm r₂ hr₂ q₁ hq₁]
      _ = (r₁ * r₂) * (q₁ * q₂) := by group
  have hrR : r₁ * r₂ ∈ R := R.mul_mem hr₁ hr₂
  have hqQ : q₁ * q₂ ∈ Q := Q.mul_mem hq₁ hq₂
  rw [h1, mul_self_mul_of_comm (h.comm _ hrR _ hqQ)]
  have hsq : (r₁ * r₂) * (r₁ * r₂) ∈ Q := by
    rw [← sq]
    rcases h.q8.sq _ hrR with h0 | h0
    · rw [h0]
      exact Q.one_mem
    · rw [h0]
      exact h.z_Q
  exact Q.mul_mem hsq (Q.mul_mem hqQ hqQ)

theorem QPair.sq_eq_of_involution (h : QPair R Q z) {r q : T} (hr : r ∈ R) (hq : q ∈ Q)
    (hx : (r * q) * (r * q) = 1) (hx1 : r * q ≠ 1) (hxz : r * q ≠ z) :
    r ^ 2 = z ∧ q ^ 2 = z := by
  have hrq : r * q = q * r := h.comm r hr q hq
  have hrr : (r * r) * (q * q) = 1 := by
    rw [← mul_self_mul_of_comm hrq]
    exact hx
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.q8.z_sq
  rcases h.q8.sq r hr with h0 | h0
  · exfalso
    have hrr1 : r * r = 1 := by rw [← sq]; exact h0
    have hqq1 : q * q = 1 := by
      rw [hrr1, one_mul] at hrr
      exact hrr
    rcases h.q8.inv r hr hrr1 with h1 | h1 <;> rcases h.Q_inv q hq hqq1 with h2 | h2
    · exact hx1 (by rw [h1, h2, one_mul])
    · exact hxz (by rw [h1, h2, one_mul])
    · exact hxz (by rw [h1, h2, mul_one])
    · exact hx1 (by rw [h1, h2]; exact h.q8.z_sq)
  · refine ⟨h0, ?_⟩
    have hrrz : r * r = z := by rw [← sq]; exact h0
    rw [hrrz] at hrr
    have hqq : q * q = z⁻¹ := eq_inv_of_mul_eq_one_right hrr
    rw [sq, hqq, hzi]

theorem QPair.exists_noncommuting (h : QPair R Q z)
    (hQinv : ∀ q ∈ Q, q ^ 2 = z → ∃ p ∈ Q, p ^ 2 = z ∧ p * q * p⁻¹ = q⁻¹)
    {r q : T} (hr : r ∈ R) (hq : q ∈ Q) (hx : (r * q) * (r * q) = 1) (hx1 : r * q ≠ 1)
    (hxz : r * q ≠ z) :
    ∃ s ∈ R, ∃ p ∈ Q, (s * p) * (s * p) = 1 ∧ (r * (s * p)) * (r * (s * p)) = 1 ∧
      (s * p) * (r * q) = (r * q) * (s * p) ∧ (r * (s * p)) * (r * q) = (r * q) * (r * (s * p)) ∧
      ((s * p) * (r * (s * p))) * ((s * p) * (r * (s * p))) = z := by
  obtain ⟨hr2, hq2⟩ := h.sq_eq_of_involution hr hq hx hx1 hxz
  obtain ⟨s, hs, hs2, hsr⟩ := h.q8.inverter r hr hr2
  obtain ⟨p, hp, hp2, hpq⟩ := hQinv q hq hq2
  refine ⟨s, hs, p, hp, ?_⟩
  have hrq : r * q = q * r := h.comm r hr q hq
  have hrp : r * p = p * r := h.comm r hr p hp
  have hsp : s * p = p * s := h.comm s hs p hp
  have hsq : s * q = q * s := h.comm s hs q hq
  have hzz : z * z = 1 := h.q8.z_sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hprp : p * r * p⁻¹ = r := by
    rw [← hrp]
    group
  have hsqs : s * q * s⁻¹ = q := by
    rw [hsq]
    group
  have hu_r : (s * p) * r * (s * p)⁻¹ = r⁻¹ := by
    calc (s * p) * r * (s * p)⁻¹ = s * (p * r * p⁻¹) * s⁻¹ := by group
      _ = s * r * s⁻¹ := by rw [hprp]
      _ = r⁻¹ := hsr
  have hu_q : (s * p) * q * (s * p)⁻¹ = q⁻¹ := by
    calc (s * p) * q * (s * p)⁻¹ = s * (p * q * p⁻¹) * s⁻¹ := by group
      _ = s * q⁻¹ * s⁻¹ := by rw [hpq]
      _ = (s * q * s⁻¹)⁻¹ := by group
      _ = q⁻¹ := by rw [hsqs]
  have hxinv : (r * q)⁻¹ = r * q := inv_eq_of_mul_eq_one_right hx
  have hu_x : (s * p) * (r * q) * (s * p)⁻¹ = r * q := by
    calc (s * p) * (r * q) * (s * p)⁻¹
        = ((s * p) * r * (s * p)⁻¹) * ((s * p) * q * (s * p)⁻¹) := by group
      _ = r⁻¹ * q⁻¹ := by rw [hu_r, hu_q]
      _ = (q * r)⁻¹ := by group
      _ = (r * q)⁻¹ := by rw [← hrq]
      _ = r * q := hxinv
  have hu_x' : (s * p) * (r * q) = (r * q) * (s * p) := by
    calc (s * p) * (r * q) = (s * p) * (r * q) * (s * p)⁻¹ * (s * p) := by group
      _ = (r * q) * (s * p) := by rw [hu_x]
  have huu : (s * p) * (s * p) = 1 := by
    calc (s * p) * (s * p) = s * (p * s) * p := by group
      _ = s * (s * p) * p := by rw [← hsp]
      _ = (s * s) * (p * p) := by group
      _ = z * z := by rw [← sq, ← sq, hs2, hp2]
      _ = 1 := hzz
  have hrx : Commute r (r * q) := (Commute.refl r).mul_right (show Commute r q from hrq)
  refine ⟨?_, ?_, hu_x', ?_, ?_⟩
  · exact huu
  · calc (r * (s * p)) * (r * (s * p))
        = r * ((s * p) * r * (s * p)⁻¹) * ((s * p) * (s * p)) := by group
      _ = r * r⁻¹ * 1 := by rw [hu_r, huu]
      _ = 1 := by group
  · calc (r * (s * p)) * (r * q) = r * ((s * p) * (r * q)) := by group
      _ = r * ((r * q) * (s * p)) := by rw [hu_x']
      _ = (r * (r * q)) * (s * p) := by group
      _ = ((r * q) * r) * (s * p) := by rw [hrx.eq]
      _ = (r * q) * (r * (s * p)) := by group
  · have huv : (s * p) * (r * (s * p)) = r⁻¹ := by
      calc (s * p) * (r * (s * p)) = ((s * p) * r * (s * p)⁻¹) * ((s * p) * (s * p)) := by group
        _ = r⁻¹ * 1 := by rw [hu_r, huu]
        _ = r⁻¹ := mul_one _
    rw [huv]
    calc r⁻¹ * r⁻¹ = (r * r)⁻¹ := by group
      _ = z⁻¹ := by rw [← sq, hr2]
      _ = z := hzi

theorem QPair.exists_noncomm_of_rank (h : QPair R Q z) {T₀ E : Subgroup T}
    (hdecomp : ∀ t ∈ T₀, t * t = 1 → ∃ r ∈ R, ∃ q ∈ Q, r * q = t) (hET : E ≤ T₀)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 2 ^ 3) :
    ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hEcomm := (SU1.isElemAbelian_iff.mp hE).1
  have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    have := (SU1.isElemAbelian_iff.mp hE).2 e he
    rwa [sq] at this
  have hzz : z * z = 1 := h.q8.z_sq
  have hzE : (E : Set T).ncard = 8 := by
    have := (Nat.card_coe_set_eq (E : Set T)).symm
    rw [this]
    exact hcard
  obtain ⟨e₁, he₁E, he₁1, he₁z⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ z := by
    by_contra hno
    push Not at hno
    have hsub : (E : Set T) ⊆ {1, z} := fun e he => by
      by_cases h1 : e = 1
      · exact Or.inl h1
      · exact Or.inr (hno e he h1)
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({1, z} : Set T).ncard ≤ 2 := by
      calc ({1, z} : Set T).ncard ≤ ({z} : Set T).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  obtain ⟨r₁, hr₁, q₁, hq₁, hrq₁⟩ := hdecomp e₁ (hET he₁E) (hEsq e₁ he₁E)
  have he₁x : (r₁ * q₁) * (r₁ * q₁) = 1 := by rw [hrq₁]; exact hEsq e₁ he₁E
  obtain ⟨hr₁2, hq₁2⟩ := h.sq_eq_of_involution hr₁ hq₁ he₁x (by rw [hrq₁]; exact he₁1)
    (by rw [hrq₁]; exact he₁z)
  have hsub : (E : Set T) ⊆ {1, z, e₁, e₁ * z} := by
    intro e he
    obtain ⟨r, hr, q, hq, hrq⟩ := hdecomp e (hET he) (hEsq e he)
    have hee₁ : e * e₁ = e₁ * e := hEcomm e he e₁ he₁E
    have hrr₁ : r * r₁ = r₁ * r := by
      have h1 : e * e₁ = (r * r₁) * (q * q₁) := by
        rw [← hrq, ← hrq₁]
        calc r * q * (r₁ * q₁) = r * (q * r₁) * q₁ := by group
          _ = r * (r₁ * q) * q₁ := by rw [← h.comm r₁ hr₁ q hq]
          _ = (r * r₁) * (q * q₁) := by group
      have h2 : e₁ * e = (r₁ * r) * (q₁ * q) := by
        rw [← hrq, ← hrq₁]
        calc r₁ * q₁ * (r * q) = r₁ * (q₁ * r) * q := by group
          _ = r₁ * (r * q₁) * q := by rw [← h.comm r hr q₁ hq₁]
          _ = (r₁ * r) * (q₁ * q) := by group
      rw [h1, h2, hab q hq q₁ hq₁] at hee₁
      exact mul_right_cancel hee₁
    rcases h.q8.cen r₁ hr₁ hr₁2 r hr hrr₁ with h0 | h0 | h0 | h0
    ·
      have heQ : e ∈ Q := by rw [← hrq, h0, one_mul]; exact hq
      rcases h.Q_inv e heQ (hEsq e he) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    · have heQ : e ∈ Q := by rw [← hrq, h0]; exact Q.mul_mem h.z_Q hq
      rcases h.Q_inv e heQ (hEsq e he) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    ·
      have he₁e : e₁ * e ∈ Q := by
        have : e₁ * e = (r₁ * r₁) * (q₁ * q) := by
          rw [← hrq, ← hrq₁, h0]
          calc r₁ * q₁ * (r₁ * q) = r₁ * (q₁ * r₁) * q := by group
            _ = r₁ * (r₁ * q₁) * q := by rw [← h.comm r₁ hr₁ q₁ hq₁]
            _ = (r₁ * r₁) * (q₁ * q) := by group
        rw [this, ← sq, hr₁2]
        exact Q.mul_mem h.z_Q (Q.mul_mem hq₁ hq)
      have he₁e2 : (e₁ * e) * (e₁ * e) = 1 := by
        calc (e₁ * e) * (e₁ * e) = e₁ * (e * e₁) * e := by group
          _ = e₁ * (e₁ * e) * e := by rw [hee₁]
          _ = (e₁ * e₁) * (e * e) := by group
          _ = 1 := by rw [hEsq e₁ he₁E, hEsq e he, one_mul]
      have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right (hEsq e₁ he₁E)
      have hee : e = e₁ * (e₁ * e) := by
        calc e = e₁⁻¹ * (e₁ * e) := by group
          _ = e₁ * (e₁ * e) := by rw [he₁inv]
      rcases h.Q_inv _ he₁e he₁e2 with h3 | h3
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [hee, h3, mul_one]
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hee, h3]
        exact Set.mem_singleton _
    ·
      have he₁e : e₁ * e ∈ Q := by
        have : e₁ * e = (r₁ * (r₁ * z)) * (q₁ * q) := by
          rw [← hrq, ← hrq₁, h0]
          calc r₁ * q₁ * (r₁ * z * q) = r₁ * (q₁ * (r₁ * z)) * q := by group
            _ = r₁ * ((r₁ * z) * q₁) * q := by rw [← h.comm (r₁ * z) (R.mul_mem hr₁ h.q8.z_mem) q₁ hq₁]
            _ = (r₁ * (r₁ * z)) * (q₁ * q) := by group
        rw [this]
        have hr₁z : r₁ * (r₁ * z) = z * z := by
          calc r₁ * (r₁ * z) = (r₁ * r₁) * z := by group
            _ = z * z := by rw [← sq, hr₁2]
        rw [hr₁z, hzz, one_mul]
        exact Q.mul_mem hq₁ hq
      have he₁e2 : (e₁ * e) * (e₁ * e) = 1 := by
        calc (e₁ * e) * (e₁ * e) = e₁ * (e * e₁) * e := by group
          _ = e₁ * (e₁ * e) * e := by rw [hee₁]
          _ = (e₁ * e₁) * (e * e) := by group
          _ = 1 := by rw [hEsq e₁ he₁E, hEsq e he, one_mul]
      have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right (hEsq e₁ he₁E)
      have hee : e = e₁ * (e₁ * e) := by
        calc e = e₁⁻¹ * (e₁ * e) := by group
          _ = e₁ * (e₁ * e) := by rw [he₁inv]
      rcases h.Q_inv _ he₁e he₁e2 with h3 | h3
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [hee, h3, mul_one]
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hee, h3]
        exact Set.mem_singleton _
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, z, e₁, e₁ * z} : Set T).ncard ≤ 4 := by
    calc ({1, z, e₁, e₁ * z} : Set T).ncard ≤ ({z, e₁, e₁ * z} : Set T).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ ≤ (({e₁, e₁ * z} : Set T).ncard + 1) + 1 := by
          have := Set.ncard_insert_le z ({e₁, e₁ * z} : Set T)
          omega
      _ ≤ ((({e₁ * z} : Set T).ncard + 1) + 1) + 1 := by
          have := Set.ncard_insert_le e₁ ({e₁ * z} : Set T)
          omega
      _ = 4 := by rw [Set.ncard_singleton]
  omega

theorem QPair.inverter_of_noncomm [Finite T] (h : QPair R Q z) (hQ2 : IsPGroup 2 Q)
    (hnc : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) :
    ∀ q ∈ Q, q ^ 2 = z → ∃ p ∈ Q, p ^ 2 = z ∧ p * q * p⁻¹ = q⁻¹ := by
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥Q := by
    intro a b _
    apply Subtype.ext
    apply Subtype.ext
    have key : ∀ t : CFSG.DisconnectedInvolutionGraph.Helpers.Involution ↥Q,
        (((t : ↥Q)) : T) = z := by
      intro t
      have ht2 : orderOf ((t : ↥Q) : T) = 2 :=
        (Subgroup.orderOf_coe (t : ↥Q)).trans t.2
      have htt : ((t : ↥Q) : T) * ((t : ↥Q) : T) = 1 := by
        have := pow_orderOf_eq_one ((t : ↥Q) : T)
        rwa [ht2, sq] at this
      have ht1 : ((t : ↥Q) : T) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at ht2
        exact absurd ht2 (by norm_num)
      exact (h.Q_inv _ (t : ↥Q).2 htt).resolve_left ht1
    rw [key a, key b]
  obtain ⟨f, hf, s, hs, hfs⟩ := hnc
  obtain ⟨e, he1, ⟨φ⟩⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_nonabelian_quaternion
    hQ2 hrank ⟨⟨f, hf⟩, ⟨s, hs⟩, fun hh => hfs (congrArg Subtype.val hh)⟩
  let ι : QuaternionGroup (2 ^ e) →* T := Q.subtype.comp φ.toMonoidHom
  have hιinj : Function.Injective ι := Q.subtype_injective.comp φ.injective
  have hrange : ι.range = Q := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (φ y).2
    · intro hx
      obtain ⟨y, hy⟩ := φ.surjective ⟨x, hx⟩
      exact ⟨y, by simp [ι, hy]⟩
  have hn2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have hn0 : (2 ^ e : ℕ) ≠ 0 := by positivity
  have hzn : ι (QuaternionGroup.a ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e))) = z := by
    have hmem : ι (QuaternionGroup.a ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e))) ∈ Q := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h2n : ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e)) + ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e)) = 0 := by
      rw [← Nat.cast_add, ← two_mul]
      exact ZMod.natCast_self (2 * 2 ^ e)
    have hsq1 : ι (QuaternionGroup.a ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e))) *
        ι (QuaternionGroup.a ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e))) = 1 := by
      rw [← map_mul, QuaternionGroup.a_mul_a, h2n, QuaternionGroup.a_zero, map_one]
    have hne1 : ι (QuaternionGroup.a ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e))) ≠ 1 := by
      intro h1
      rw [← map_one ι] at h1
      have h2 := hιinj h1
      rw [← QuaternionGroup.a_zero, QuaternionGroup.a.injEq] at h2
      have h3 := (ZMod.natCast_eq_zero_iff _ _).mp h2
      have h4 : 2 * 2 ^ e ≤ 2 ^ e := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h3
      omega
    exact (h.Q_inv _ hmem hsq1).resolve_left hne1
  intro q hq _
  rw [← hrange] at hq
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hq
  obtain ⟨p, hp2, hp⟩ := quaternion_inverter hn2 x
  refine ⟨ι p, by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨p, rfl⟩, ?_, ?_⟩
  · rw [← map_pow, hp2, hzn]
  · have := congrArg ι hp
    simpa [map_mul, map_inv] using this

end Pair

end CFSG.GH74.Uniqueness.SU.SU10
