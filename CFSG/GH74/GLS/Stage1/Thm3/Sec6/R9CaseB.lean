module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9CaseA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Abs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

theorem conj_of_odd_mul {G : Type*} [Group G] {e t : G} (he : e * e = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (e * t))) : ∃ m : G, m * e * m⁻¹ = t := by
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set a := e * t with ha
  have hainv : a⁻¹ = t * e := by rw [ha, mul_inv_rev, he', ht']
  obtain ⟨j, hj⟩ := hodd
  have hea : e * a⁻¹ * e = a := by
    rw [hainv, ha]
    calc e * (t * e) * e = (e * t) * (e * e) := by group
      _ = e * t := by rw [he, mul_one]
  have hpow : ∀ k : ℕ, e * (a⁻¹ ^ k) * e = a ^ k := by
    intro k
    have : e * (a⁻¹ ^ k) * e⁻¹ = (e * a⁻¹ * e⁻¹) ^ k := by
      rw [← conj_pow]
    rw [he'] at this
    rw [this, hea]
  have hn : a ^ (2 * j + 1) = 1 := by
    rw [← hj]; exact pow_orderOf_eq_one a
  have hn' : a⁻¹ ^ (2 * j + 1) = 1 := by rw [inv_pow, hn, inv_one]
  set m := a⁻¹ ^ (j + 1) with hm
  refine ⟨m, ?_⟩
  have h2 : e * m⁻¹ * e = m := by
    have := hpow (j + 1)
    calc e * m⁻¹ * e = e⁻¹ * m⁻¹ * e⁻¹ := by rw [he']
      _ = (e * m * e)⁻¹ := by group
      _ = (a ^ (j + 1))⁻¹ := by rw [hm, this]
      _ = m := by rw [hm, inv_pow]
  have h1 : m * e * m⁻¹ = m * (e * m⁻¹ * e) * e⁻¹ := by group
  rw [h1, h2, he']
  have h3 : m * m = a⁻¹ := by
    rw [hm, ← pow_add]
    calc a⁻¹ ^ (j + 1 + (j + 1)) = a⁻¹ ^ (2 * j + 1) * a⁻¹ := by
          rw [← pow_succ]; congr 1; omega
      _ = a⁻¹ := by rw [hn', one_mul]
  rw [h3, hainv]
  calc t * e * e = t * (e * e) := by group
    _ = t := by rw [he, mul_one]

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

namespace Cfg1

theorem conj_comp (h : Cfg1 G z S P Q F FA) {U : Subgroup G} (hUR : U ≤ P ⊔ Q) (hU4 : Four U)
    (hUn : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) {u u₁ u₂ : G} (huU : u ∈ U) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hu₁P : u₁ ∈ P) (hu₂Q : u₂ ∈ Q) (hu : u = u₁ * u₂) {s : G} (hs : s ∈ S) :
    (s * u₁ * s⁻¹ = u₁ ∨ s * u₁ * s⁻¹ = u₁ * z) ∧ (s * u₂ * s⁻¹ = u₂ ∨ s * u₂ * s⁻¹ = u₂ * z) := by
  have hUS : U ≤ S := hUR.trans (sup_le h.P_le h.Q_le)
  have hzU : z ∈ U := h.z_mem_four hU4 hUS hUn
  have hz1 := h.z_ne
  have hz2 := h.z_sq
  have hsuU : s * u * s⁻¹ ∈ U := hUn s hs u huU
  have hsu1 : s * u * s⁻¹ ≠ 1 := by
    intro e
    apply hu1
    calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
      _ = 1 := by rw [e]; group
  have hsuz : s * u * s⁻¹ ≠ z := by
    intro e
    apply huz
    have hzc : s * z = z * s := (h.z_cent s hs).symm
    calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
      _ = s⁻¹ * z * s := by rw [e]
      _ = z := by
        calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
          _ = s⁻¹ * (s * z) := by rw [hzc]
          _ = z := by group
  have hab : s * u * s⁻¹ = u ∨ s * u * s⁻¹ = z * u := by
    rcases Four.mem_cases hU4 hzU huU hz1 hu1 huz hsuU with e | e | e | e
    · exact absurd e hsu1
    · exact absurd e hsuz
    · exact Or.inl e
    · exact Or.inr e
  set a := u₁⁻¹ * (s * u₁ * s⁻¹) with ha
  set b := u₂⁻¹ * (s * u₂ * s⁻¹) with hb
  have haP : a ∈ P := mul_mem (inv_mem hu₁P) (h.P_norm s hs u₁ hu₁P)
  have hbQ : b ∈ Q := mul_mem (inv_mem hu₂Q) (h.Q_norm s hs u₂ hu₂Q)
  have huS : u ∈ S := hUS huU
  have hsu_eq : s * u * s⁻¹ = u * (a * b) := by
    have e1 : s * u * s⁻¹ = (s * u₁ * s⁻¹) * (s * u₂ * s⁻¹) := by rw [hu]; group
    have e2 : s * u₁ * s⁻¹ = u₁ * a := by rw [ha]; group
    have e3 : s * u₂ * s⁻¹ = u₂ * b := by rw [hb]; group
    rw [e1, e2, e3, hu]
    calc u₁ * a * (u₂ * b) = u₁ * (a * u₂) * b := by group
      _ = u₁ * (u₂ * a) * b := by rw [(h.PQ_comm a haP u₂ hu₂Q).symm]
      _ = u₁ * u₂ * (a * b) := by group
  have hab' : a * b = 1 ∨ a * b = z := by
    rcases hab with e | e
    · left
      have : u * (a * b) = u * 1 := by rw [← hsu_eq, e]; group
      exact mul_left_cancel this
    · right
      have : u * (a * b) = u * z := by rw [← hsu_eq, e, h.z_cent u huS]
      exact mul_left_cancel this
  have haz : (a = 1 ∨ a = z) ∧ (b = 1 ∨ b = z) := by
    have hzQ := h.z_Q
    have hzP := h.z_P
    rcases hab' with e | e
    · have haQ : a ∈ Q := by
        rw [eq_inv_of_mul_eq_one_left e]; exact inv_mem hbQ
      have hbP : b ∈ P := by
        rw [eq_inv_of_mul_eq_one_right e]; exact inv_mem haP
      exact ⟨h.PQ_inf a haP haQ, h.PQ_inf b hbP hbQ⟩
    · have haQ : a ∈ Q := by
        have e' : a = z * b⁻¹ := by
          calc a = (a * b) * b⁻¹ := by group
            _ = z * b⁻¹ := by rw [e]
        rw [e']
        exact mul_mem hzQ (inv_mem hbQ)
      have hbP : b ∈ P := by
        have e' : b = a⁻¹ * z := by
          calc b = a⁻¹ * (a * b) := by group
            _ = a⁻¹ * z := by rw [e]
        rw [e']
        exact mul_mem (inv_mem haP) hzP
      exact ⟨h.PQ_inf a haP haQ, h.PQ_inf b hbP hbQ⟩
  have hya : s * u₁ * s⁻¹ = u₁ * a := by rw [ha]; group
  have hyb : s * u₂ * s⁻¹ = u₂ * b := by rw [hb]; group
  refine ⟨?_, ?_⟩
  · rcases haz.1 with e | e
    · left; rw [hya, e, mul_one]
    · right; rw [hya, e]
  · rcases haz.2 with e | e
    · left; rw [hyb, e, mul_one]
    · right; rw [hyb, e]

theorem sq_of_pq (h : Cfg1 G z S P Q F FA) (hQinv : ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z) {p q : G}
    (hp : p ∈ P) (hq : q ∈ Q) (ht2 : (p * q) * (p * q) = 1) (ht1 : p * q ≠ 1) (htz : p * q ≠ z) :
    p * p = z ∧ q * q = z := by
  have hcomm : q * p = p * q := (h.PQ_comm p hp q hq).symm
  have hpq : (p * p) * (q * q) = 1 := by
    calc (p * p) * (q * q) = p * (p * q) * q := by group
      _ = p * (q * p) * q := by rw [← hcomm]
      _ = (p * q) * (p * q) := by group
      _ = 1 := ht2
  have hqq : q * q = (p * p)⁻¹ := eq_inv_of_mul_eq_one_right hpq
  have hppP : p * p ∈ P := mul_mem hp hp
  have hppQ : p * p ∈ Q := by
    have : (q * q)⁻¹ ∈ Q := inv_mem (mul_mem hq hq)
    have e : p * p = (q * q)⁻¹ := by rw [hqq, inv_inv]
    rw [e]; exact this
  rcases h.PQ_inf _ hppP hppQ with e | e
  · exfalso
    have hq2 : q * q = 1 := by rw [hqq, e]; group
    rcases h.P_inv p hp e with h1 | h1 <;> rcases hQinv q hq hq2 with h2 | h2
    · exact ht1 (by rw [h1, h2]; group)
    · exact htz (by rw [h1, h2]; group)
    · exact htz (by rw [h1, h2]; group)
    · exact ht1 (by rw [h1, h2]; exact h.z_sq)
  · refine ⟨e, ?_⟩
    rw [hqq, e]
    exact inv_eq_of_mul_eq_one_right h.z_sq

end Cfg1

namespace Cfg1K

theorem step1b (h : Cfg1K G z S P Q Q FA) (hQinv : ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z)
    {u₂ : G} (hu₂Q : u₂ ∈ Q)
    (hnorm₂ : ∀ s ∈ S, s * u₂ * s⁻¹ = u₂ ∨ s * u₂ * s⁻¹ = u₂ * z)
    (hCase : ∃ t ∈ P ⊔ Q, t ≠ z ∧ IsConj z t)
    (hX : ∀ t : G, IsConj z t → t ∈ P ⊔ (Q ⊓ centralizer ({u₂} : Set G)) → t = z) : False := by
  have hz1 := h.z_ne
  have hz2 := h.z_sq
  have hsqconj : ∀ {w : G}, IsConj z w → w * w = 1 ∧ w ≠ 1 := by
    intro w hzw
    obtain ⟨c, hc⟩ := isConj_iff.1 hzw
    refine ⟨?_, ?_⟩
    · rw [← hc]
      calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    · intro e
      apply hz1
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = 1 := by rw [hc, e]; group
  obtain ⟨t, htR, htz, hzt⟩ := hCase
  obtain ⟨ht2, ht1⟩ := hsqconj hzt
  obtain ⟨p, hp, q, hq, htpq, hpsq, hqsq⟩ := h.toCfg1.decomp_four' hQinv htR ht2 ht1 htz
  have hpS : p ∈ S := h.P_le hp
  have hBS : zpowers p ≤ S := zpowers_le.2 hpS
  have hBt : ∀ b ∈ zpowers p, b * t = t * b := by
    have hle : zpowers p ≤ centralizer ({t} : Set G) := by
      refine zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
      have hc : p * q = q * p := h.PQ_comm p hp q hq
      calc p * t = p * (p * q) := by rw [htpq]
        _ = p * (q * p) := by rw [hc]
        _ = p * q * p := by rw [mul_assoc]
        _ = t * p := by rw [htpq]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
  obtain ⟨g, hg, hgB⟩ := h.toCfg1.exists_g_into_S hzt hBS hBt
  have hs₀S : g * p * g⁻¹ ∈ S := hgB p (mem_zpowers p)
  set s₀ := g * p * g⁻¹ with hs₀
  set w := g * z * g⁻¹ with hw
  have hws : s₀ * s₀ = w := by
    rw [hs₀, hw, ← hpsq]; group
  have hwR : w ∈ P ⊔ Q := by
    rw [← hws]; exact B.sq_mem_of_relIndex_le_two h.idx hs₀S
  have hzw : IsConj z w := isConj_iff.2 ⟨g, rfl⟩
  obtain ⟨hw2, hw1⟩ := hsqconj hzw
  have hwz : w ≠ z := by
    intro e
    apply htz
    have hgz : g * z * g⁻¹ = z := hw.symm.trans e
    have : g⁻¹ * z * g = z := by
      calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hgz]
        _ = z := by group
    rw [← hg, this]
  have hwX : ¬ (w ∈ P ⊔ (Q ⊓ centralizer ({u₂} : Set G))) := fun hm => hwz (hX w hzw hm)
  obtain ⟨p', hp', q', hq', hwe, hp'sq, hq'sq⟩ := h.toCfg1.decomp_four' hQinv hwR hw2 hw1 hwz
  have hq'X : ¬ (q' * u₂ = u₂ * q') := by
    intro hc
    apply hwX
    rw [hwe]
    exact mul_mem (mem_sup_left hp') (mem_sup_right ⟨hq', Subgroup.mem_centralizer_singleton_iff.2 hc⟩)
  have hq'u : q' * u₂ * q'⁻¹ = u₂ * z := by
    rcases hnorm₂ q' (h.Q_le hq') with e | e
    · exfalso
      apply hq'X
      calc q' * u₂ = (q' * u₂ * q'⁻¹) * q' := by group
        _ = u₂ * q' := by rw [e]
    · exact e
  have hwu1 : w * u₂ * w⁻¹ = u₂ * z := by
    have hpc : ∀ x ∈ Q, p' * x = x * p' := fun x hx => h.PQ_comm p' hp' x hx
    have hzQ := h.z_Q
    calc w * u₂ * w⁻¹ = p' * (q' * u₂ * q'⁻¹) * p'⁻¹ := by rw [hwe]; group
      _ = p' * (u₂ * z) * p'⁻¹ := by rw [hq'u]
      _ = (u₂ * z) * (p' * p'⁻¹) := by
          calc p' * (u₂ * z) * p'⁻¹ = (p' * (u₂ * z)) * p'⁻¹ := by group
            _ = ((u₂ * z) * p') * p'⁻¹ := by rw [hpc (u₂ * z) (mul_mem hu₂Q hzQ)]
            _ = (u₂ * z) * (p' * p'⁻¹) := by group
      _ = u₂ * z := by rw [mul_inv_cancel, mul_one]
  have hwu2 : w * u₂ * w⁻¹ = u₂ := by
    have hzc : z * s₀ = s₀ * z := h.z_cent s₀ hs₀S
    have e : w * u₂ * w⁻¹ = s₀ * (s₀ * u₂ * s₀⁻¹) * s₀⁻¹ := by
      rw [← hws]; group
    rw [e]
    rcases hnorm₂ s₀ hs₀S with e1 | e1
    · rw [e1, e1]
    · rw [e1]
      calc s₀ * (u₂ * z) * s₀⁻¹ = (s₀ * u₂ * s₀⁻¹) * (s₀ * z * s₀⁻¹) := by group
        _ = (u₂ * z) * z := by
            rw [e1]
            congr 1
            calc s₀ * z * s₀⁻¹ = (s₀ * z) * s₀⁻¹ := by group
              _ = (z * s₀) * s₀⁻¹ := by rw [hzc]
              _ = z := by group
        _ = u₂ := by rw [mul_assoc, hz2, mul_one]
  have : u₂ * z = u₂ := hwu1.symm.trans hwu2
  apply hz1
  calc z = u₂⁻¹ * (u₂ * z) := by group
    _ = 1 := by rw [this]; group

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
