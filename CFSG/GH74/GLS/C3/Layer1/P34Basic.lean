module

public import CFSG.GH74.GLS.C3.Layer1.P34Cfg

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin

variable {X : Type} [Group X] {T P Q : Subgroup X} {x z f h : X}

theorem mem_normalizer_of_conj_le [Finite X] {A : Subgroup X} {g : X}
    (h : ∀ a ∈ A, g⁻¹ * a * g ∈ A) : g ∈ normalizer (A : Set X) := by
  have hmap : A.map (MulAut.conj g⁻¹).toMonoidHom = A := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨a, ha, rfl⟩
      simpa using h a ha
    · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have : a ∈ A.map (MulAut.conj g⁻¹).toMonoidHom := by rw [hmap]; exact ha
    obtain ⟨b, hb, rfl⟩ := this
    have e : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    simpa [e] using hb
  · intro ha
    have := h _ ha
    simpa [mul_assoc] using this

theorem exists_sylow_ge [Finite X] {N K : Subgroup X} (hKN : K ≤ N) (hK : IsPGroup 2 ↥K) :
    ∃ S : Subgroup X, K ≤ S ∧ S ≤ N ∧ IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.relIndex N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU0 : IsPGroup 2 ↥(K.subgroupOf N) :=
    IsPGroup.of_equiv hK (Subgroup.subgroupOfEquivOfLe hKN).symm
  obtain ⟨S, hS⟩ := hU0.exists_le_sylow
  refine ⟨(S : Subgroup ↥N).map N.subtype, ?_, Subgroup.map_subtype_le _,
    S.isPGroup'.map N.subtype, ?_⟩
  · intro k hk
    exact ⟨⟨k, hKN hk⟩, hS (by simpa [Subgroup.mem_subgroupOf] using hk), rfl⟩
  · have hS' : ((S : Subgroup ↥N).map N.subtype).subgroupOf N = (S : Subgroup ↥N) := by
      ext z
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨w, hw, hwz⟩
        have : w = z := Subtype.ext hwz
        rwa [this] at hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    have : ((S : Subgroup ↥N).map N.subtype).relIndex N = (S : Subgroup ↥N).index := by
      unfold Subgroup.relIndex
      rw [hS']
    rw [this]
    exact Sylow.not_dvd_index S

theorem le_of_sylow_le [Finite X] {N U S : Subgroup X} (hUS : U ≤ S) (hSN : S ≤ N)
    (hS : IsPGroup 2 ↥S) (hU : ¬ 2 ∣ U.relIndex N) : S ≤ U := by
  have h1 := Subgroup.relIndex_mul_relIndex U S N hUS hSN
  have hdvd : U.relIndex S ∣ U.relIndex N := ⟨S.relIndex N, h1.symm⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hS)
  have h2 : U.relIndex S ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card U S
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have : i = 0 := by
    by_contra hne
    apply hU
    refine dvd_trans ?_ hdvd
    rw [hi']
    exact dvd_pow_self 2 hne
  rw [this, pow_zero] at hi'
  exact Subgroup.relIndex_eq_one.1 hi'

namespace Cfg34

variable (c : Cfg34 X T P Q x z f h)
include c

theorem z_mem_T : z ∈ T := c.P_le c.z_mem

theorem z_sq : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [c.z_order, sq] at this

theorem x_sq : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [c.x_order, sq] at this

theorem f_sq : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [c.f_order, sq] at this

theorem z_ne_one : z ≠ 1 := by
  intro h1
  have := c.z_order
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem x_ne_one : x ≠ 1 := by
  intro h1
  have := c.x_order
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem PQ_comm : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a := by
  intro a ha b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ Q := by
    have := Q.mul_mem (c.Q_norm a (c.P_le ha) b hb) (Q.inv_mem hb)
    simpa [mul_assoc] using this
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ P := by
    have := P.mul_mem ha (c.P_norm b (c.Q_le hb) a⁻¹ (P.inv_mem ha))
    simpa [mul_assoc] using this
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ P ⊓ Q := ⟨h2, h1⟩
  rw [c.PQ_inf, Subgroup.mem_bot] at h3
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem z_cent_of_norm (s : X) (hs : ∀ a ∈ P, s * a * s⁻¹ ∈ P) (hs' : ∀ a ∈ P, s⁻¹ * a * s ∈ P) :
    s * z = z * s := by
  have h1 : s * z * s⁻¹ ∈ P := hs z c.z_mem
  have h2 : ∀ a ∈ P, a * (s * z * s⁻¹) = (s * z * s⁻¹) * a := by
    intro a ha
    have ha' : s⁻¹ * a * s ∈ P := hs' a ha
    have hc := c.z_central _ ha'
    have : s⁻¹ * a * s * z = z * (s⁻¹ * a * s) := hc
    calc a * (s * z * s⁻¹) = s * ((s⁻¹ * a * s) * z) * s⁻¹ := by group
      _ = s * (z * (s⁻¹ * a * s)) * s⁻¹ := by rw [this]
      _ = (s * z * s⁻¹) * a := by group
  rcases c.z_unique _ h1 h2 with h3 | h3
  · exfalso
    apply c.z_ne_one
    have : s * z * s⁻¹ = 1 := h3
    calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
      _ = 1 := by rw [this]; group
  · calc s * z = (s * z * s⁻¹) * s := by group
      _ = z * s := by rw [h3]

theorem z_cent_T : ∀ t ∈ T, t * z = z * t := fun t ht =>
  c.z_cent_of_norm t (fun a ha => c.P_norm t ht a ha)
    (fun a ha => by simpa using c.P_norm t⁻¹ (T.inv_mem ht) a ha)

theorem x_ne_z : x ≠ z := by
  intro hxz
  have h1 : x ∈ P ⊓ Q := ⟨hxz ▸ c.z_mem, c.x_mem_Q⟩
  rw [c.PQ_inf, Subgroup.mem_bot] at h1
  exact c.x_ne_one h1

theorem mem_PQ {y : X} : y ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, y = p * q := by
  have hQP : Q ≤ normalizer (P : Set X) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have := c.P_norm q (c.Q_le hq) a ha
      simpa [mul_assoc] using this
    · intro ha
      have := c.P_norm q⁻¹ (T.inv_mem (c.Q_le hq)) _ ha
      simpa [mul_assoc] using this
  have := Subgroup.coe_mul_of_right_le_normalizer_left P Q hQP
  constructor
  · intro hy
    have hy' : y ∈ ((P ⊔ Q : Subgroup X) : Set X) := hy
    rw [this] at hy'
    obtain ⟨p, hp, q, hq, rfl⟩ := hy'
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact (P ⊔ Q).mul_mem (mem_sup_left hp) (mem_sup_right hq)

theorem R_le : P ⊔ Q ≤ T := sup_le c.P_le c.Q_le

theorem R_norm : ∀ t ∈ T, ∀ r ∈ P ⊔ Q, t * r * t⁻¹ ∈ P ⊔ Q := by
  intro t ht r hr
  obtain ⟨p, hp, q, hq, rfl⟩ := c.mem_PQ.1 hr
  have : t * (p * q) * t⁻¹ = (t * p * t⁻¹) * (t * q * t⁻¹) := by group
  rw [this]
  exact c.mem_PQ.2 ⟨_, c.P_norm t ht p hp, _, c.Q_norm t ht q hq, rfl⟩

end Cfg34

end CFSG.GH74.GLS.C3.Layer1.P34
