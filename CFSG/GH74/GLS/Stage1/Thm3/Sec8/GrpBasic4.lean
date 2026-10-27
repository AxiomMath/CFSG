module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section Quat

variable {G : Type*} [Group G] [Finite G]

theorem GQ.sq_mem_of_card_eight {Q : Subgroup G} {z : G} (hQ : GQ Q z) (h8 : Nat.card ↥Q = 8) {q : G}
    (hq : q ∈ Q) : q * q = 1 ∨ q * q = z := by
  obtain ⟨M, hMQ, -, -, h4, hMi, hout⟩ := hQ.ex
  have hMc : Nat.card ↥M = 4 := by
    have h1 := card_mul_relIndex_of_le hMQ
    rw [hMi, h8] at h1
    omega
  by_cases hqM : q ∈ M
  · have h1 : q ^ 4 = 1 := by
      have := pow_card_of_mem hqM
      rwa [hMc] at this
    have h2 : (q * q) * (q * q) = 1 := by rw [← pow_four_eq]; exact h1
    exact hQ.uniq _ (mul_mem hq hq) h2
  · right
    exact (hout q hq hqM).1

end Quat

section Decomp

theorem decomp_of_involution_mem_sup {G : Type*} [Group G] [Finite G] {z u : G}
    {W₁ W₂ V₁ V₂ : Subgroup G} (hz2 : z * z = 1)
    (hW₁c : IsCyclic ↥W₁) (hW₂c : IsCyclic ↥W₂)
    (hV₁W₂ : V₁ ≤ W₂) (hV₂W₁ : V₂ ≤ W₁) (hV₁p : IsPGroup 2 ↥V₁) (hV₂p : IsPGroup 2 ↥V₂)
    (hV₁4 : 4 ≤ Nat.card ↥V₁) (hV₂4 : 4 ≤ Nat.card ↥V₂)
    (hn₁ : ∀ b ∈ W₂, ∀ a ∈ W₁, b * a * b⁻¹ ∈ W₁) (hn₂ : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b * a⁻¹ ∈ W₂)
    (hinter : ∀ x ∈ W₁, x ∈ W₂ → x = 1 ∨ x = z)
    (hu : u ∈ W₁ ⊔ W₂) (hu2 : u * u = 1) :
    ∃ w₁ ∈ V₂, ∃ w₂ ∈ V₁, u = w₁ * w₂ := by
  have hnorm : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha; exact hn₁ b hb a ha
    · intro ha
      have h1 := hn₁ b⁻¹ (inv_mem hb) _ ha
      have e : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
      rwa [e] at h1
  obtain ⟨b, hb, a, ha, hba⟩ := mem_sup_of_le_normalizer' hnorm (sup_comm W₁ W₂ ▸ hu)
  set w₁ := b * a * b⁻¹ with hw₁
  have hw₁W : w₁ ∈ W₁ := hn₁ b hb a ha
  have huw : u = w₁ * b := by rw [hba, hw₁]; group
  set w₂ := b with hw₂
  have hw₂W : w₂ ∈ W₂ := hb
  set ε := w₂ * w₁ * w₂⁻¹ * w₁⁻¹ with hε
  have hεW₁ : ε ∈ W₁ := mul_mem (hn₁ w₂ hw₂W w₁ hw₁W) (inv_mem hw₁W)
  have hεW₂ : ε ∈ W₂ := by
    have : ε = w₂ * (w₁ * w₂⁻¹ * w₁⁻¹) := by rw [hε]; group
    rw [this]
    exact mul_mem hw₂W (hn₂ w₁ hw₁W w₂⁻¹ (inv_mem hw₂W))
  have hεc : ε * w₁ = w₁ * ε := cyclic_comm hW₁c ε hεW₁ w₁ hw₁W
  have hu2' : ε * (w₁ * w₁) * (w₂ * w₂) = 1 := by
    have e1 : w₂ * w₁ = ε * w₁ * w₂ := by rw [hε]; group
    calc ε * (w₁ * w₁) * (w₂ * w₂) = ε * w₁ * (w₁ * w₂ * w₂) := by group
      _ = w₁ * ε * (w₁ * w₂ * w₂) := by rw [hεc]
      _ = w₁ * (ε * w₁ * w₂) * w₂ := by group
      _ = w₁ * (w₂ * w₁) * w₂ := by rw [← e1]
      _ = u * u := by rw [huw]; group
      _ = 1 := hu2
  have h1 : (w₁ * w₁) * (w₂ * w₂) = ε⁻¹ := by
    calc (w₁ * w₁) * (w₂ * w₂) = ε⁻¹ * (ε * (w₁ * w₁) * (w₂ * w₂)) := by group
      _ = ε⁻¹ := by rw [hu2']; group
  have hw₁sq : w₁ * w₁ ∈ W₂ := by
    have : w₁ * w₁ = ε⁻¹ * (w₂ * w₂)⁻¹ := by
      calc w₁ * w₁ = ((w₁ * w₁) * (w₂ * w₂)) * (w₂ * w₂)⁻¹ := by group
        _ = ε⁻¹ * (w₂ * w₂)⁻¹ := by rw [h1]
    rw [this]
    exact mul_mem (inv_mem hεW₂) (inv_mem (mul_mem hw₂W hw₂W))
  have hw₂sq : w₂ * w₂ ∈ W₁ := by
    have : w₂ * w₂ = (w₁ * w₁)⁻¹ * ε⁻¹ := by
      calc w₂ * w₂ = (w₁ * w₁)⁻¹ * ((w₁ * w₁) * (w₂ * w₂)) := by group
        _ = (w₁ * w₁)⁻¹ * ε⁻¹ := by rw [h1]
    rw [this]
    exact mul_mem (inv_mem (mul_mem hw₁W hw₁W)) (inv_mem hεW₁)
  have hw₁4 : w₁ ^ 4 = 1 := by
    rw [pow_four_eq]
    rcases hinter _ (mul_mem hw₁W hw₁W) hw₁sq with h | h
    · rw [h]; simp
    · rw [h]; exact hz2
  have hw₂4 : w₂ ^ 4 = 1 := by
    rw [pow_four_eq]
    rcases hinter _ hw₂sq (mul_mem hw₂W hw₂W) with h | h
    · rw [h]; simp
    · rw [h]; exact hz2
  exact ⟨w₁, mem_of_pow_four_eq_one hW₁c hV₂W₁ hV₂p hV₂4 hw₁W hw₁4, w₂,
    mem_of_pow_four_eq_one hW₂c hV₁W₂ hV₁p hV₁4 hw₂W hw₂4, huw⟩

end Decomp

section Swap

variable {G : Type*} [Group G]

theorem sq_one_sup {X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hX : ∀ x ∈ X, x * x = 1) (hY : ∀ y ∈ Y, y * y = 1) : ∀ e ∈ X ⊔ Y, e * e = 1 := by
  intro e he
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute' hXY he
  have h1 := hXY x hx y hy
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [h1]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hX x hx, hY y hy, one_mul]

@[expose] def swapHom (P₁ P₂ : Subgroup G) (d : G) (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂) : ↥P₁ →* G :=
  MonoidHom.mk' (fun q => (q : G) * (d * (q : G) * d⁻¹)) (by
    intro a b
    have h1 := hc (b : G) b.2 _ (hdP (a : G) a.2)
    calc ((a * b : ↥P₁) : G) * (d * ((a * b : ↥P₁) : G) * d⁻¹)
        = (a : G) * ((b : G) * (d * (a : G) * d⁻¹)) * (d * (b : G) * d⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : G) * ((d * (a : G) * d⁻¹) * (b : G)) * (d * (b : G) * d⁻¹) := by rw [h1]
      _ = ((a : G) * (d * (a : G) * d⁻¹)) * ((b : G) * (d * (b : G) * d⁻¹)) := by group)

theorem swapHom_apply {P₁ P₂ : Subgroup G} {d : G} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂) (q : ↥P₁) :
    swapHom P₁ P₂ d hc hdP q = (q : G) * (d * (q : G) * d⁻¹) := rfl

theorem swapHom_eq_one_iff {P₁ P₂ : Subgroup G} {z d : G} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hinf : P₁ ⊓ P₂ = zpowers z) (hz2 : z * z = 1) (hdz : d * z * d⁻¹ = z)
    (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂) (q : ↥P₁) :
    swapHom P₁ P₂ d hc hdP q = 1 ↔ (q : G) ∈ zpowers z := by
  rw [swapHom_apply]
  constructor
  · intro h
    have hr : d * (q : G) * d⁻¹ ∈ P₂ := hdP q q.2
    have hq : (q : G) = (d * (q : G) * d⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hq2 : (q : G) ∈ P₂ := by rw [hq]; exact inv_mem hr
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨q.2, hq2⟩
  · intro h
    rcases (mem_zpowers_of_sq' hz2).1 h with h1 | h1
    · rw [h1]; group
    · rw [h1, hdz, hz2]

theorem swapHom_mul_self {P₁ P₂ : Subgroup G} {z d : G} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hz2 : z * z = 1) (hdz : d * z * d⁻¹ = z) (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂)
    (hsq : ∀ q ∈ P₁, q * q = 1 ∨ q * q = z) (q : ↥P₁) :
    swapHom P₁ P₂ d hc hdP q * swapHom P₁ P₂ d hc hdP q = 1 := by
  rw [swapHom_apply]
  have h1 := hc (q : G) q.2 _ (hdP q q.2)
  have hrr : (d * (q : G) * d⁻¹) * (d * (q : G) * d⁻¹) = d * ((q : G) * q) * d⁻¹ := by group
  calc ((q : G) * (d * (q : G) * d⁻¹)) * ((q : G) * (d * (q : G) * d⁻¹))
      = (q : G) * ((d * (q : G) * d⁻¹) * (q : G)) * (d * (q : G) * d⁻¹) := by group
    _ = (q : G) * ((q : G) * (d * (q : G) * d⁻¹)) * (d * (q : G) * d⁻¹) := by rw [h1]
    _ = ((q : G) * q) * ((d * (q : G) * d⁻¹) * (d * (q : G) * d⁻¹)) := by group
    _ = 1 := by
      rw [hrr]
      rcases hsq q q.2 with h | h
      · rw [h]; group
      · rw [h, hdz, hz2]

theorem swapHom_comm_d {P₁ P₂ : Subgroup G} {d : G} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hd2 : d * d = 1) (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂) (q : ↥P₁) :
    d * swapHom P₁ P₂ d hc hdP q = swapHom P₁ P₂ d hc hdP q * d := by
  rw [swapHom_apply]
  have h1 := hc (q : G) q.2 _ (hdP q q.2)
  have hr : d * (d * (q : G) * d⁻¹) * d⁻¹ = (q : G) := by
    calc d * (d * (q : G) * d⁻¹) * d⁻¹ = (d * d) * (q : G) * (d * d)⁻¹ := by group
      _ = q := by rw [hd2]; group
  calc d * ((q : G) * (d * (q : G) * d⁻¹))
      = ((d * (q : G) * d⁻¹) * (d * (d * (q : G) * d⁻¹) * d⁻¹)) * d := by group
    _ = ((d * (q : G) * d⁻¹) * (q : G)) * d := by rw [hr]
    _ = ((q : G) * (d * (q : G) * d⁻¹)) * d := by rw [h1]

theorem swapHom_comm_z {P₁ P₂ : Subgroup G} {z d : G} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hzP₁ : z ∈ P₁) (hzP₂ : z ∈ P₂) (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂) (q : ↥P₁) :
    z * swapHom P₁ P₂ d hc hdP q = swapHom P₁ P₂ d hc hdP q * z := by
  rw [swapHom_apply]
  have h1 := hc z hzP₁ _ (hdP q q.2)
  have h2 := hc (q : G) q.2 z hzP₂
  calc z * ((q : G) * (d * (q : G) * d⁻¹)) = (z * (q : G)) * (d * (q : G) * d⁻¹) := by group
    _ = ((q : G) * z) * (d * (q : G) * d⁻¹) := by rw [← h2]
    _ = (q : G) * (z * (d * (q : G) * d⁻¹)) := by group
    _ = (q : G) * ((d * (q : G) * d⁻¹) * z) := by rw [h1]
    _ = ((q : G) * (d * (q : G) * d⁻¹)) * z := by group

theorem z_not_mem_swapRange {P₁ P₂ : Subgroup G} {z d : G} (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a)
    (hinf : P₁ ⊓ P₂ = zpowers z) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hdz : d * z * d⁻¹ = z)
    (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂) : z ∉ (swapHom P₁ P₂ d hc hdP).range := by
  rintro ⟨q, hq⟩
  have hqz : (q : G) ∈ zpowers z := by
    have hzP₂ : z ∈ P₂ := (Subgroup.mem_inf.1 (hinf ▸ Subgroup.mem_zpowers z : z ∈ P₁ ⊓ P₂)).2
    have hr : d * (q : G) * d⁻¹ ∈ P₂ := hdP q q.2
    rw [swapHom_apply hc hdP q] at hq
    have hq' : (q : G) = z * (d * (q : G) * d⁻¹)⁻¹ := by
      calc (q : G) = ((q : G) * (d * (q : G) * d⁻¹)) * (d * (q : G) * d⁻¹)⁻¹ := by group
        _ = z * (d * (q : G) * d⁻¹)⁻¹ := by rw [hq]
    have hqP₂ : (q : G) ∈ P₂ := by rw [hq']; exact mul_mem hzP₂ (inv_mem hr)
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨q.2, hqP₂⟩
  have h1 := (swapHom_eq_one_iff hc hinf hz2 hdz hdP q).2 hqz
  rw [hq] at h1
  exact hz1 h1

theorem card_swapRange [Finite G] {P₁ P₂ : Subgroup G} {z d : G}
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : P₁ ⊓ P₂ = zpowers z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hdz : d * z * d⁻¹ = z) (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂)
    (h8 : Nat.card ↥P₁ = 8) : Nat.card (swapHom P₁ P₂ d hc hdP).range = 4 := by
  have hker : (swapHom P₁ P₂ d hc hdP).ker.map P₁.subtype = zpowers z := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (swapHom_eq_one_iff hc hinf hz2 hdz hdP q).1 (MonoidHom.mem_ker.1 hq)
    · intro hx
      have hxP : x ∈ P₁ := (Subgroup.mem_inf.1 (hinf ▸ hx : x ∈ P₁ ⊓ P₂)).1
      exact ⟨⟨x, hxP⟩, MonoidHom.mem_ker.2 ((swapHom_eq_one_iff hc hinf hz2 hdz hdP ⟨x, hxP⟩).2 hx),
        rfl⟩
  have hk : Nat.card (swapHom P₁ P₂ d hc hdP).ker = 2 := by
    have h1 := Subgroup.card_map_of_injective (K := (swapHom P₁ P₂ d hc hdP).ker) P₁.subtype_injective
    rw [hker] at h1
    rw [← h1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1]
  have h2 := Subgroup.card_mul_index (swapHom P₁ P₂ d hc hdP).ker
  rw [Subgroup.index_ker, hk, h8] at h2
  omega

theorem exists_swap_elemAb [Finite G] {P₁ P₂ X : Subgroup G} {z d : G}
    (hc : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hinf : P₁ ⊓ P₂ = zpowers z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hd2 : d * d = 1) (hdz : d * z * d⁻¹ = z) (hdP : ∀ q ∈ P₁, d * q * d⁻¹ ∈ P₂)
    (hsq : ∀ q ∈ P₁, q * q = 1 ∨ q * q = z) (h8 : Nat.card ↥P₁ = 8) (hP₁X : P₁ ≤ X)
    (hP₂X : P₂ ≤ X) (hdX : d ∉ X) :
    ∃ E : Subgroup G, (∀ e ∈ E, e * e = 1) ∧ Nat.card ↥E = 16 := by
  have hzmem : z ∈ P₁ ⊓ P₂ := hinf ▸ Subgroup.mem_zpowers z
  have hzP₁ : z ∈ P₁ := hzmem.1
  have hzP₂ : z ∈ P₂ := hzmem.2
  have hdz' : d * z = z * d := by
    calc d * z = (d * z * d⁻¹) * d := by group
      _ = z * d := by rw [hdz]
  have hHc : Nat.card (swapHom P₁ P₂ d hc hdP).range = 4 := card_swapRange hc hinf hz2 hz1 hdz hdP h8
  have hHsq : ∀ e ∈ (swapHom P₁ P₂ d hc hdP).range, e * e = 1 := by
    rintro e ⟨q, rfl⟩
    exact swapHom_mul_self hc hz2 hdz hdP hsq q
  have hHz : ∀ e ∈ (swapHom P₁ P₂ d hc hdP).range, z * e = e * z := by
    rintro e ⟨q, rfl⟩
    exact swapHom_comm_z hc hzP₁ hzP₂ hdP q
  have hHd : ∀ e ∈ (swapHom P₁ P₂ d hc hdP).range, d * e = e * d := by
    rintro e ⟨q, rfl⟩
    exact swapHom_comm_d hc hd2 hdP q
  have hHX : (swapHom P₁ P₂ d hc hdP).range ≤ X := by
    rintro e ⟨q, rfl⟩
    rw [swapHom_apply hc hdP q]
    exact mul_mem (hP₁X q.2) (hP₂X (hdP q q.2))
  have hzsq : ∀ e ∈ zpowers z, e * e = 1 := by
    intro e he
    rcases (mem_zpowers_of_sq' hz2).1 he with h | h
    · rw [h]; group
    · rw [h, hz2]
  have hzH : ∀ a ∈ zpowers z, ∀ b ∈ (swapHom P₁ P₂ d hc hdP).range, a * b = b * a := by
    intro a ha b hb
    rcases (mem_zpowers_of_sq' hz2).1 ha with h | h
    · rw [h]; group
    · rw [h]; exact hHz b hb
  have hzHbot : zpowers z ⊓ (swapHom P₁ P₂ d hc hdP).range = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases (mem_zpowers_of_sq' hz2).1 hg.1 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      apply z_not_mem_swapRange hc hinf hz2 hz1 hdz hdP
      rw [← h]
      exact hg.2
  have hYc : Nat.card ↥(zpowers z ⊔ (swapHom P₁ P₂ d hc hdP).range) = 8 := by
    have h1 := card_sup_mul_card_inf' (A := zpowers z) (B := (swapHom P₁ P₂ d hc hdP).range)
      (le_normalizer_of_commute' hzH)
    rw [hzHbot, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1, hHc] at h1
    omega
  have hYsq := sq_one_sup hzH hzsq hHsq
  have hdY : ∀ a ∈ zpowers d, ∀ b ∈ zpowers z ⊔ (swapHom P₁ P₂ d hc hdP).range,
      a * b = b * a := by
    intro a ha b hb
    rcases (mem_zpowers_of_sq' hd2).1 ha with h | h
    · rw [h]; group
    · rw [h]
      obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute' hzH hb
      have h1 : d * a' = a' * d := by
        rcases (mem_zpowers_of_sq' hz2).1 ha' with h' | h'
        · rw [h']; group
        · rw [h']; exact hdz'
      calc d * (a' * b') = (d * a') * b' := by group
        _ = (a' * d) * b' := by rw [h1]
        _ = a' * (d * b') := by group
        _ = a' * (b' * d) := by rw [hHd b' hb']
        _ = (a' * b') * d := by group
  have hdsq : ∀ e ∈ zpowers d, e * e = 1 := by
    intro e he
    rcases (mem_zpowers_of_sq' hd2).1 he with h | h
    · rw [h]; group
    · rw [h, hd2]
  refine ⟨zpowers d ⊔ (zpowers z ⊔ (swapHom P₁ P₂ d hc hdP).range), sq_one_sup hdY hdsq hYsq, ?_⟩
  have hd1 : d ≠ 1 := fun h => hdX (h ▸ X.one_mem)
  have hdYbot : zpowers d ⊓ (zpowers z ⊔ (swapHom P₁ P₂ d hc hdP).range) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases (mem_zpowers_of_sq' hd2).1 hg.1 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      apply hdX
      have hY : zpowers z ⊔ (swapHom P₁ P₂ d hc hdP).range ≤ X :=
        sup_le (zpowers_le.2 (hP₁X hzP₁)) hHX
      have hgY := hg.2
      rw [h] at hgY
      exact hY hgY
  have h1 := card_sup_mul_card_inf' (A := zpowers d)
    (B := zpowers z ⊔ (swapHom P₁ P₂ d hc hdP).range) (le_normalizer_of_commute' hdY)
  rw [hdYbot, Subgroup.card_bot, mul_one, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1, hYc] at h1
  omega

end Swap

section Gen

variable {G : Type*} [Group G] [Finite G]

theorem sup_eq_of_card_le {A W₀ : Subgroup G} {y g : G} (hAW : A ≤ W₀) (hy : y ∈ W₀) (hg : g ∈ W₀)
    (hy2 : y * y = 1) (hg2 : g * g = 1) (hyA : y ∉ A) (hgA : g ∉ A) (hygA : y⁻¹ * g ∉ A)
    (hnA : ∀ w ∈ W₀, ∀ a ∈ A, w * a * w⁻¹ ∈ A)
    (hcomm : ∀ w ∈ W₀, ∀ w' ∈ W₀, w * w' * w⁻¹ * w'⁻¹ ∈ A)
    (hcard : Nat.card ↥W₀ ≤ 4 * Nat.card ↥A) :
    A ⊔ zpowers y ⊔ zpowers g = W₀ := by
  have hy1 : y ≠ 1 := fun h => hyA (h ▸ A.one_mem)
  have hg1 : g ≠ 1 := fun h => hgA (h ▸ A.one_mem)
  have hyN : y ∈ normalizer (A : Set G) := mem_normalizer_of_invol hy2 (fun p hp => hnA y hy p hp)
  have hyz : zpowers y ≤ normalizer (A : Set G) := zpowers_le.2 hyN
  have hAy : A ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases (mem_zpowers_of_sq' hy2).1 hx.2 with h | h
    · rw [h]; exact one_mem _
    · have : y ∈ A := by rw [← h]; exact hx.1
      exact absurd this hyA
  have hBc : Nat.card ↥(A ⊔ zpowers y) = 2 * Nat.card ↥A := by
    have h1 := card_sup_mul_card_inf' (A := A) (B := zpowers y) hyz
    rw [hAy, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1] at h1
    omega
  have hgB : g ∈ normalizer ((A ⊔ zpowers y : Subgroup G) : Set G) := by
    apply mem_normalizer_of_invol hg2
    intro p hp
    have hle : A ⊔ zpowers y ≤ (A ⊔ zpowers y).comap (MulAut.conj g).toMonoidHom := by
      apply sup_le
      · intro a ha
        exact Subgroup.mem_sup_left (hnA g hg a ha)
      · rw [zpowers_le]
        show g * y * g⁻¹ ∈ A ⊔ zpowers y
        have e : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_left (hcomm g hg y hy))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    exact hle hp
  have hgB' : g ∉ A ⊔ zpowers y := by
    intro hgB'
    obtain ⟨b, hb, a, ha, hba⟩ := mem_sup_of_le_normalizer' hyz (sup_comm A (zpowers y) ▸ hgB')
    rcases (mem_zpowers_of_sq' hy2).1 hb with h | h
    · rw [h, one_mul] at hba
      apply hgA
      rw [hba]
      exact ha
    · rw [h] at hba
      apply hygA
      have : y⁻¹ * g = a := by rw [hba]; group
      rw [this]
      exact ha
  have hgz : zpowers g ≤ normalizer ((A ⊔ zpowers y : Subgroup G) : Set G) := zpowers_le.2 hgB
  have hBg : (A ⊔ zpowers y) ⊓ zpowers g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases (mem_zpowers_of_sq' hg2).1 hx.2 with h | h
    · rw [h]; exact one_mem _
    · have : g ∈ A ⊔ zpowers y := by rw [← h]; exact hx.1
      exact absurd this hgB'
  have hTc : Nat.card ↥(A ⊔ zpowers y ⊔ zpowers g) = 2 * Nat.card ↥(A ⊔ zpowers y) := by
    have h1 := card_sup_mul_card_inf' (A := A ⊔ zpowers y) (B := zpowers g) hgz
    rw [hBg, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1] at h1
    omega
  have hTle : A ⊔ zpowers y ⊔ zpowers g ≤ W₀ :=
    sup_le (sup_le hAW (zpowers_le.2 hy)) (zpowers_le.2 hg)
  exact Subgroup.eq_of_le_of_card_ge hTle (by omega)

end Gen

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
