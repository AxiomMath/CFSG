module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise commutatorElement

theorem comm_of_mem_normalizer_zpowers {G : Type*} [Group G] {b y : G} (hb : orderOf b = 2)
    (hy : y ∈ normalizer ((zpowers b : Subgroup G) : Set G)) : y * b = b * y := by
  have h1 : y * b * y⁻¹ ∈ zpowers b := (mem_normalizer_iff.mp hy b).mp (mem_zpowers b)
  have hne : y * b * y⁻¹ ≠ 1 := by
    intro he
    have : b = 1 := by
      calc b = y⁻¹ * (y * b * y⁻¹) * y := by group
        _ = 1 := by rw [he]; group
    rw [this, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have h2 := eq_of_mem_zpowers_of_orderOf_eq_two hb h1 hne
  calc y * b = (y * b * y⁻¹) * y := by group
    _ = b * y := by rw [h2]

theorem mem_normalizer_zpowers_of_comm {G : Type*} [Group G] {b y : G} (hy : y * b = b * y) :
    y ∈ normalizer ((zpowers b : Subgroup G) : Set G) := by
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro z hz
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  exact (Commute.zpow_left (show Commute b y from hy.symm) k).eq

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem conj_mem_D {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.D) : s * y * s⁻¹ ∈ h.D :=
  mem_inf.mpr ⟨mul_mem (mul_mem hs (h.D_le_S hy)) (inv_mem hs),
    (mem_normalizer_iff.mp (h.S_le_normalizer hs) y).mp (h.D_le_J hy)⟩

theorem D_le_normalizer_P : h.D ≤ normalizer (h.P : Set H) := by
  intro d hd
  apply mem_normalizer_of_conj_mem
  · intro y hy
    exact h.conj_mem_P (h.D_le_S hd) hy
  · intro y hy
    have := h.conj_mem_P (inv_mem (h.D_le_S hd)) hy
    rwa [inv_inv] at this

theorem exists_mul_of_mem_D_sup_P {y : H} (hy : y ∈ h.D ⊔ h.P) :
    ∃ d ∈ h.D, ∃ t ∈ h.P, d * t = y := by
  have hm : y ∈ (h.D : Set H) * (h.P : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ h.D_le_normalizer_P]
    exact hy
  exact Set.mem_mul.mp hm

theorem zpowers_a_le_normalizer_D : zpowers h.a ≤ normalizer (h.D : Set H) := by
  rw [zpowers_le]
  apply mem_normalizer_of_conj_mem
  · intro d hd
    exact h.conj_mem_D h.a_mem_S hd
  · intro d hd
    have := h.conj_mem_D (inv_mem h.a_mem_S) hd
    rwa [inv_inv] at this

theorem conj_mem_D_sup_a {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.D ⊔ zpowers h.a) :
    s * y * s⁻¹ ∈ h.D ⊔ zpowers h.a := by
  have hm : y ∈ (h.D : Set H) * (zpowers h.a : Set H) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ h.zpowers_a_le_normalizer_D]
    exact hy
  obtain ⟨d, hd, ε, hε, rfl⟩ := Set.mem_mul.mp hm
  have hsε : s * ε * s⁻¹ = ε := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hε
    rw [(Commute.zpow_right (show Commute s h.a from h.comm_a hs) k).eq, mul_inv_cancel_right]
  have : s * (d * ε) * s⁻¹ = (s * d * s⁻¹) * (s * ε * s⁻¹) := by group
  rw [this, hsε]
  exact mul_mem (mem_sup_left (h.conj_mem_D hs hd)) (mem_sup_right hε)

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem conj_x_b_of_P_eq_T {b : H} (hBb : h.B = zpowers b) (hb : orderOf b = 2)
    (hTab : h.T = zpowers h.a ⊔ zpowers b) (hPT : h.P = h.T) : h.x⁻¹ * b * h.x = h.a * b := by
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbP : b ∈ h.P := h.toHyp52.B_le_P hbB
  have hbS : b ∈ h.S := h.toHyp52.P_le_S hbP
  have hab : h.a * b = b * h.a := (h.toHyp52.comm_a hbS).symm
  have hb1 : b ≠ 1 := fun he => by rw [he, orderOf_one] at hb; exact absurd hb (by norm_num)
  have hxb : h.x⁻¹ * b * h.x ∈ h.T := by
    rw [← hPT]
    have := h.toHyp52.conj_mem_P (inv_mem h.x_mem) hbP
    rwa [inv_inv] at this
  rcases h.mem_T_cases hb hTab hab hxb with h1 | h1 | h1 | h1
  · exfalso; apply hb1
    calc b = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · exfalso; apply h.toHyp52.a_not_mem_B
    have : b = h.a := by
      calc b = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
        _ = h.x * h.a * h.x⁻¹ := by rw [h1]
        _ = h.a := by rw [h.toHyp52.x_comm_a, mul_inv_cancel_right]
    rw [← this]; exact hbB
  · exfalso; apply hb1
    have hbx : b ∈ conjugate h.B h.x := by
      rw [mem_conjugate_iff]
      have : h.x * b * h.x⁻¹ = b := by
        calc h.x * b * h.x⁻¹ = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by rw [h1]
          _ = b := by group
      rw [this]; exact hbB
    exact mem_bot.mp (h.inf_conjugate_x ▸ mem_inf.mpr ⟨hbB, hbx⟩)
  · exact h1

theorem commutator_le_of_P_eq_T (hB7 : EmbedsTQuotStatement)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) (hPT : h.P = h.T) (hDP : h.D ⊓ h.P = ⊥)
    (hSS : ⁅h.S, h.S⁆ ≤ h.D ⊔ h.P) {m : ℕ}
    (f : ↥h.S →* Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ m)))
    (hf : f.ker = (h.D ⊔ h.P).subgroupOf h.S) : ⁅h.S, h.S⁆ ≤ h.D ⊔ zpowers h.a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hBb, hb, -, hTab, -⟩ := h.index_two_structure hB7 hT
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbP : b ∈ h.P := h.toHyp52.B_le_P hbB
  have hbS : b ∈ h.S := h.toHyp52.P_le_S hbP
  have hab : h.a * b = b * h.a := (h.toHyp52.comm_a hbS).symm
  have hb1 : b ≠ 1 := fun he => by rw [he, orderOf_one] at hb; exact absurd hb (by norm_num)
  have ha1 : h.a ≠ 1 := fun he => by
    have := h.orderOf_a
    rw [he, orderOf_one] at this
    exact absurd this (by norm_num)
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hxb := h.conj_x_b_of_P_eq_T hBb hb hTab hPT
  have hxa : h.x⁻¹ * h.a * h.x = h.a := by
    rw [mul_assoc, ← h.toHyp52.x_comm_a, ← mul_assoc, inv_mul_cancel, one_mul]
  have hPcases : ∀ {t : H}, t ∈ h.P → t = 1 ∨ t = h.a ∨ t = b ∨ t = h.a * b := fun ht =>
    h.mem_T_cases hb hTab hab (hPT ▸ ht)
  have hQb : ∀ {q : H}, q ∈ h.Q → q * b = b * q := fun hq =>
    comm_of_mem_normalizer_zpowers hb (hBb ▸ (mem_inf.mp hq).2)
  have hQP : ∀ {q t : H}, q ∈ h.Q → t ∈ h.P → q * t = t * q := by
    intro q t hq ht
    have hqa : q * h.a = h.a * q := h.toHyp52.comm_a (mem_inf.mp hq).1
    rcases hPcases ht with rfl | rfl | rfl | rfl
    · rw [mul_one, one_mul]
    · exact hqa
    · exact hQb hq
    · calc q * (h.a * b) = h.a * (q * b) := by rw [← mul_assoc, hqa, mul_assoc]
        _ = h.a * b * q := by rw [hQb hq, mul_assoc]
  have hQ : ∀ {s : H}, s ∈ h.S → s * b = b * s → s ∈ h.Q := fun hs hsb =>
    mem_inf.mpr ⟨hs, hBb ▸ mem_normalizer_zpowers_of_comm hsb⟩
  have hPQ : h.P ≤ h.Q := by rw [hPT]; exact inf_le_left
  have hDPQ : h.D ⊔ h.P ≤ h.Q :=
    sup_le (fun d hd => hQ (h.toHyp52.D_le_S hd) (h.toHyp52.D_comm_P hd hbP)) hPQ
  have hxQ : h.x ∉ h.Q := by
    intro hxQ
    apply hb1
    have hbx : b ∈ conjugate h.B h.x := by
      rw [mem_conjugate_iff]
      exact (mem_normalizer_iff.mp (mem_inf.mp hxQ).2 b).mp hbB
    exact mem_bot.mp (h.inf_conjugate_x ▸ mem_inf.mpr ⟨hbB, hbx⟩)
  have hx2 : h.x ^ 2 ∈ h.P := (mem_inf.mp h.x_sq_mem).1
  have hQx : ∀ {q : H}, q ∈ h.Q → ⁅q, h.x⁆ ∈ h.D ⊔ zpowers h.a := by
    intro q hq
    have hqS : q ∈ h.S := (mem_inf.mp hq).1
    obtain ⟨d₁, hd₁, t₁, ht₁, hdt⟩ :=
      h.toHyp52.exists_mul_of_mem_D_sup_P (hSS (commutator_mem_commutator hqS h.x_mem))
    have hqx2 : q * h.x ^ 2 = h.x ^ 2 * q := hQP hq hx2
    have hxq : h.x * q * h.x⁻¹ = h.x⁻¹ * q * h.x := by
      calc h.x * q * h.x⁻¹ = h.x⁻¹ * (h.x ^ 2 * q) * h.x⁻¹ := by group
        _ = h.x⁻¹ * (q * h.x ^ 2) * h.x⁻¹ := by rw [hqx2]
        _ = h.x⁻¹ * q * h.x := by group
    have hconj : h.x⁻¹ * ⁅q, h.x⁆ * h.x = ⁅q, h.x⁆⁻¹ := by
      rw [commutatorElement_def]
      calc h.x⁻¹ * (q * h.x * q⁻¹ * h.x⁻¹) * h.x = h.x⁻¹ * q * h.x * q⁻¹ := by group
        _ = h.x * q * h.x⁻¹ * q⁻¹ := by rw [hxq]
        _ = (q * h.x * q⁻¹ * h.x⁻¹)⁻¹ := by group
    have hAD : h.x⁻¹ * d₁ * h.x ∈ h.D := by
      have := h.toHyp52.conj_mem_D (inv_mem h.x_mem) hd₁
      rwa [inv_inv] at this
    have hBP : h.x⁻¹ * t₁ * h.x ∈ h.P := by
      have := h.toHyp52.conj_mem_P (inv_mem h.x_mem) ht₁
      rwa [inv_inv] at this
    have hdt' : d₁ * t₁ = t₁ * d₁ := h.toHyp52.D_comm_P hd₁ ht₁
    have heq : (h.x⁻¹ * d₁ * h.x) * (h.x⁻¹ * t₁ * h.x) = d₁⁻¹ * t₁⁻¹ := by
      calc (h.x⁻¹ * d₁ * h.x) * (h.x⁻¹ * t₁ * h.x) = h.x⁻¹ * (d₁ * t₁) * h.x := by group
        _ = (d₁ * t₁)⁻¹ := by rw [hdt, hconj]
        _ = d₁⁻¹ * t₁⁻¹ := by rw [hdt', mul_inv_rev]
    have hmem : d₁ * (h.x⁻¹ * d₁ * h.x) ∈ h.D ⊓ h.P := by
      refine mem_inf.mpr ⟨mul_mem hd₁ hAD, ?_⟩
      have : d₁ * (h.x⁻¹ * d₁ * h.x) = t₁⁻¹ * (h.x⁻¹ * t₁ * h.x)⁻¹ := by
        rw [eq_mul_inv_of_mul_eq heq]
        group
      rw [this]
      exact mul_mem (inv_mem ht₁) (inv_mem hBP)
    rw [hDP, mem_bot] at hmem
    have hA : h.x⁻¹ * d₁ * h.x = d₁⁻¹ := eq_inv_of_mul_eq_one_right hmem
    have hB : h.x⁻¹ * t₁ * h.x = t₁⁻¹ := by
      rw [hA] at heq
      exact mul_left_cancel heq
    rw [← hdt]
    refine mul_mem (mem_sup_left hd₁) (mem_sup_right ?_)
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    rcases hPcases ht₁ with h0 | h0 | h0 | h0
    · rw [h0]; exact one_mem _
    · rw [h0]; exact mem_zpowers _
    · exfalso
      rw [h0, hxb, hbinv] at hB
      apply ha1
      calc h.a = h.a * b * b⁻¹ := by group
        _ = 1 := by rw [hB]; group
    · exfalso
      have h1 : h.x⁻¹ * (h.a * b) * h.x = b := by
        calc h.x⁻¹ * (h.a * b) * h.x = (h.x⁻¹ * h.a * h.x) * (h.x⁻¹ * b * h.x) := by group
          _ = b := by rw [hxa, hxb, ← mul_assoc, ha2, one_mul]
      have h2 : (h.a * b)⁻¹ = h.a * b := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, hbinv, hab]
      rw [h0, h1, h2] at hB
      apply ha1
      calc h.a = h.a * b * b⁻¹ := by group
        _ = 1 := by rw [← hB]; group
  obtain ⟨N, hN⟩ : ∃ N : Subgroup ↥h.S, N = (h.D ⊔ zpowers h.a).subgroupOf h.S := ⟨_, rfl⟩
  have hNn : N.Normal := by
    rw [hN]
    constructor
    intro n hn s
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact h.toHyp52.conj_mem_D_sup_a s.2 hn
  obtain ⟨φ, hφker⟩ : ∃ φ : ↥h.S →* ↥h.S ⧸ N, φ.ker = N :=
    ⟨QuotientGroup.mk' N, QuotientGroup.ker_mk' N⟩
  have hφ1 : ∀ y : ↥h.S, φ y = 1 ↔ (y : H) ∈ h.D ⊔ zpowers h.a := by
    intro y
    rw [← MonoidHom.mem_ker, hφker, hN, mem_subgroupOf]
  have hφc : ∀ y z : ↥h.S, Commute (φ y) (φ z) ↔ ⁅(y : H), (z : H)⁆ ∈ h.D ⊔ zpowers h.a := by
    intro y z
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hφ1]
    rfl
  have hφD : ∀ {d : H} (hd : d ∈ h.D), φ ⟨d, h.toHyp52.D_le_S hd⟩ = 1 := fun hd =>
    (hφ1 _).mpr (mem_sup_left hd)
  obtain ⟨x', hx'⟩ : ∃ x' : ↥h.S, (x' : H) = h.x := ⟨⟨h.x, h.x_mem⟩, rfl⟩
  have hkerQ : ∀ y : ↥h.S, y ∈ f.ker → (y : H) ∈ h.Q := by
    intro y hy
    rw [hf, mem_subgroupOf] at hy
    exact hDPQ hy
  have hu2 : orderOf (f x') = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← MonoidHom.mem_ker, hf, mem_subgroupOf]
      have : ((x' ^ 2 : ↥h.S) : H) = h.x ^ 2 := by rw [← hx']; rfl
      rw [this]
      exact mem_sup_right hx2
    · intro h1
      apply hxQ
      rw [← hx']
      exact hkerQ x' (MonoidHom.mem_ker.mpr h1)
  have huY : f x' ∉ (h.Q.subgroupOf h.S).map f := by
    intro hmem
    obtain ⟨q, hq, hqx⟩ := mem_map.mp hmem
    apply hxQ
    have h1 : q⁻¹ * x' ∈ f.ker := (f.eq_iff).mp hqx.symm
    have h2 := mul_mem (mem_subgroupOf.mp hq) (hkerQ _ h1)
    simpa [hx'] using h2
  have hYc : IsCyclic ↥((h.Q.subgroupOf h.S).map f) := isCyclic_of_not_mem_involution hu2 huY
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥((h.Q.subgroupOf h.S).map f))
  obtain ⟨q₀, hq₀, hq₀g⟩ := mem_map.mp g.2
  have hq₀Q : (q₀ : H) ∈ h.Q := mem_subgroupOf.mp hq₀
  have hφQ : ∀ q : ↥h.S, (q : H) ∈ h.Q →
      ∃ k : ℤ, ∃ t : ↥h.S, (t : H) ∈ h.P ∧ φ q = φ q₀ ^ k * φ t := by
    intro q hq
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨f q, mem_map_of_mem f (mem_subgroupOf.mpr hq)⟩)
    have hfk : f (q₀ ^ k) = f q := by
      have := congrArg Subtype.val hk
      rw [SubgroupClass.coe_zpow, ← hq₀g] at this
      rw [map_zpow]
      exact this
    have hr : (q₀ ^ k)⁻¹ * q ∈ f.ker := (f.eq_iff).mp hfk.symm
    rw [hf, mem_subgroupOf] at hr
    obtain ⟨d, hd, t, ht, hdt⟩ := h.toHyp52.exists_mul_of_mem_D_sup_P hr
    refine ⟨k, ⟨t, h.toHyp52.P_le_S ht⟩, ht, ?_⟩
    have hr' : (q₀ ^ k)⁻¹ * q = ⟨d, h.toHyp52.D_le_S hd⟩ * ⟨t, h.toHyp52.P_le_S ht⟩ :=
      Subtype.ext hdt.symm
    calc φ q = φ (q₀ ^ k * ((q₀ ^ k)⁻¹ * q)) := by rw [mul_inv_cancel_left]
      _ = φ q₀ ^ k * φ ⟨t, h.toHyp52.P_le_S ht⟩ := by
        rw [hr', map_mul, map_mul, map_zpow, hφD hd, one_mul]
  have hcP : ∀ t q : ↥h.S, (t : H) ∈ h.P → (q : H) ∈ h.Q → Commute (φ t) (φ q) := by
    intro t q ht hq
    have : t * q = q * t := Subtype.ext (hQP hq ht).symm
    show φ t * φ q = φ q * φ t
    rw [← map_mul, ← map_mul, this]
  have hφQQ : ∀ q₁ q₂ : ↥h.S, (q₁ : H) ∈ h.Q → (q₂ : H) ∈ h.Q → Commute (φ q₁) (φ q₂) := by
    intro q₁ q₂ h1 h2
    obtain ⟨i, t₁, ht₁, e1⟩ := hφQ q₁ h1
    obtain ⟨j, t₂, ht₂, e2⟩ := hφQ q₂ h2
    rw [e1, e2]
    exact Commute.mul_left
      (Commute.mul_right (Commute.zpow_zpow_self _ i j) ((hcP t₂ q₀ ht₂ hq₀Q).symm.zpow_left i))
      (Commute.mul_right ((hcP t₁ q₀ ht₁ hq₀Q).zpow_right j) (hcP t₁ t₂ ht₁ (hPQ ht₂)))
  have hφQx : ∀ q : ↥h.S, (q : H) ∈ h.Q → Commute (φ q) (φ x') := by
    intro q hq
    rw [hφc, hx']
    exact hQx hq
  have hdecS : ∀ s : ↥h.S, (s : H) ∈ h.Q ∨ ((x'⁻¹ * s : ↥h.S) : H) ∈ h.Q := by
    intro s
    have hsb : (s : H) * b * (s : H)⁻¹ ∈ h.P := h.toHyp52.conj_mem_P s.2 hbP
    rcases hPcases hsb with h1 | h1 | h1 | h1
    · exfalso; apply hb1
      calc b = (s : H)⁻¹ * ((s : H) * b * (s : H)⁻¹) * s := by group
        _ = 1 := by rw [h1]; group
    · exfalso; apply h.toHyp52.a_not_mem_B
      have : b = h.a := by
        calc b = (s : H)⁻¹ * ((s : H) * b * (s : H)⁻¹) * s := by group
          _ = (s : H)⁻¹ * h.a * s := by rw [h1]
          _ = h.a := by
            rw [mul_assoc, ← h.toHyp52.comm_a s.2, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [← this]; exact hbB
    · left
      apply hQ s.2
      calc (s : H) * b = ((s : H) * b * (s : H)⁻¹) * s := by group
        _ = b * s := by rw [h1]
    · right
      simp only [coe_mul, coe_inv, hx']
      apply hQ (mul_mem (inv_mem h.x_mem) s.2)
      have h2 : h.x⁻¹ * ((s : H) * b * (s : H)⁻¹) * h.x = b := by
        rw [h1]
        calc h.x⁻¹ * (h.a * b) * h.x = (h.x⁻¹ * h.a * h.x) * (h.x⁻¹ * b * h.x) := by group
          _ = b := by rw [hxa, hxb, ← mul_assoc, ha2, one_mul]
      calc h.x⁻¹ * (s : H) * b
          = (h.x⁻¹ * ((s : H) * b * (s : H)⁻¹) * h.x) * (h.x⁻¹ * s) := by group
        _ = b * (h.x⁻¹ * s) := by rw [h2]
  have hA : ∀ s : ↥h.S, (∀ q : ↥h.S, (q : H) ∈ h.Q → Commute (φ s) (φ q)) ∧
      Commute (φ s) (φ x') := by
    intro s
    rcases hdecS s with hs | hs
    · exact ⟨fun q hq => hφQQ s q hs hq, hφQx s hs⟩
    · have he : φ s = φ x' * φ (x'⁻¹ * s) := by rw [← map_mul, mul_inv_cancel_left]
      rw [he]
      exact ⟨fun q hq => Commute.mul_left (hφQx q hq).symm (hφQQ _ q hs hq),
        Commute.mul_left (Commute.refl _) (hφQx _ hs)⟩
  have hall : ∀ s t : ↥h.S, Commute (φ s) (φ t) := by
    intro s t
    rcases hdecS t with ht | ht
    · exact (hA s).1 t ht
    · have he : φ t = φ x' * φ (x'⁻¹ * t) := by rw [← map_mul, mul_inv_cancel_left]
      rw [he]
      exact Commute.mul_right (hA s).2 ((hA s).1 _ ht)
  rw [commutator_le]
  intro s hs t ht
  exact (hφc ⟨s, hs⟩ ⟨t, ht⟩).mp (hall _ _)

theorem commutator_le_zpowers_of_P_eq_T {d : H} (hd : d ∈ h.D) (hDP : h.D ⊓ h.P = ⊥)
    (h1 : ⁅h.S, h.S⁆ ≤ zpowers d ⊔ h.P) (h2 : ⁅h.S, h.S⁆ ≤ h.D ⊔ zpowers h.a) :
    ⁅h.S, h.S⁆ ≤ zpowers d ⊔ zpowers h.a := by
  intro u hu
  have hdN : zpowers d ≤ normalizer (h.P : Set H) :=
    zpowers_le.mpr (h.toHyp52.D_le_normalizer_P hd)
  have hm1 : u ∈ (zpowers d : Set H) * (h.P : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hdN]
    exact h1 hu
  have hm2 : u ∈ (h.D : Set H) * (zpowers h.a : Set H) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ h.toHyp52.zpowers_a_le_normalizer_D]
    exact h2 hu
  obtain ⟨u₁, hu₁, t, ht, rfl⟩ := Set.mem_mul.mp hm1
  obtain ⟨d', hd', ε, hε, he⟩ := Set.mem_mul.mp hm2
  have hu₁D : u₁ ∈ h.D := zpowers_le.mpr hd hu₁
  have hεP : ε ∈ h.P := zpowers_le.mpr h.toHyp52.a_mem_P hε
  have hm : d'⁻¹ * u₁ ∈ h.D ⊓ h.P := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hd') hu₁D, ?_⟩
    have : d'⁻¹ * u₁ = ε * t⁻¹ := by
      calc d'⁻¹ * u₁ = d'⁻¹ * (u₁ * t) * t⁻¹ := by group
        _ = d'⁻¹ * (d' * ε) * t⁻¹ := by rw [he]
        _ = ε * t⁻¹ := by group
    rw [this]
    exact mul_mem hεP (inv_mem ht)
  rw [hDP, mem_bot] at hm
  have hu₁d : u₁ = d' := by
    calc u₁ = d' * (d'⁻¹ * u₁) := (mul_inv_cancel_left d' u₁).symm
      _ = d' := by rw [hm, mul_one]
  have htε : t = ε := by
    rw [hu₁d] at he
    exact (mul_left_cancel he).symm
  rw [htε]
  exact mul_mem (mem_sup_left hu₁) (mem_sup_right hε)

theorem commutator_structure (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hAC : CFAutSmallCommutator) (hAQ : CFAutSmallQuotient) (hST : SuzukiTausskyInput)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) :
    (∃ d ∈ h.D, ∃ c ∈ h.P, ⁅h.S, h.S⁆ ≤ zpowers d ⊔ zpowers c) ∧
      (∀ u ∈ ⁅h.S, h.S⁆, ∀ v ∈ ⁅h.S, h.S⁆, u * v = v * u) ∧ ⁅h.S, h.S⁆ ≤ h.D ⊔ h.P ∧
      ∃ z : H, orderOf z = 2 ∧ z ∈ h.D ∧ z ∈ centralizer (h.S : Set H) ∧
        ∀ u ∈ ⁅h.S, h.S⁆, orderOf u = 2 → u ∈ closure {z, h.a} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := h.toHyp52.center_eq_bot hB1 hB6 hCF23 hCF24
  have hSmall := h.toHyp52.isSmallAltOrL2_J hB1 hB6 hCF23 hCF24
  have hDP := h.toHyp52.D_inf_P_eq_bot hZ
  obtain ⟨d, hd, hdn, hdle⟩ := hAC H h.toHyp52 hSmall hZ
  rcases Nat.lt_or_ge (Nat.card h.P) 8 with h8 | h8
  ·
    have hPT := h.P_eq_T_of_card_lt hB7 hT h8
    obtain ⟨m, f, hf⟩ := hAQ H h.toHyp52 hSmall hZ
    have hSS : ⁅h.S, h.S⁆ ≤ h.D ⊔ h.P :=
      hdle.trans (sup_le (zpowers_le.mpr (mem_sup_left hd)) le_sup_right)
    have hle := h.commutator_le_zpowers_of_P_eq_T hd hDP hdle
      (h.commutator_le_of_P_eq_T hB7 hT hPT hDP hSS f hf)
    have ha2 : 2 ∣ orderOf h.a := by simp [h.orderOf_a]
    have haa : h.a ^ (orderOf h.a / 2) = h.a := by rw [h.orderOf_a, Nat.div_self two_pos, pow_one]
    exact ⟨⟨d, hd, h.a, h.toHyp52.a_mem_P, hle⟩,
      h.commutator_conclusions hd hdn h.toHyp52.a_mem_P ha2 haa hDP hle⟩
  ·
    obtain ⟨p, -, hp, -, -, hc, -, -, hpn, hpc, hpa⟩ :=
      h.presentation_of_index_two hB7 hST hT h8
    have hle := h.commutator_le_of_card_ge hd hdle hp hpn hpc
    have hp2 : 2 ∣ orderOf p := by
      have hP2 : IsPGroup 2 ↥h.P := h.toHyp52.isPGroup_S.to_le h.toHyp52.P_le_S
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨p, hp⟩
      rw [Subgroup.orderOf_mk] at hn
      rw [hn]
      refine dvd_pow_self 2 ?_
      rintro rfl
      rw [pow_zero] at hn
      omega
    exact ⟨⟨d, hd, p, hp, hle⟩, h.commutator_conclusions hd hdn hp hp2 hpa hDP hle⟩

end Hyp59

end CFSG.ComponentClassification.GSThmB
