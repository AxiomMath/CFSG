module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainAct

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn

variable {G : Type} [Group G]

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {k : ℕ} {A : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) k A)

include hS hC

theorem conj_not_mem_AX (g : G) : g * t * g⁻¹ ∉ A := by
  intro huA
  have hu2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.shape.mul_self]
    group
  exact (hS.shape.conj_not_mem hS.rad.odd g) (hS.rad.Q_le_L (hC.level.mem_Q _ huA hu2))

variable (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
include hinv

theorem conj_mem_AX [Finite G] {g : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) {x : G} (hx : x ∈ A) :
    g * x * g⁻¹ ∈ A := by
  have hAt : ∀ y ∈ A, g * y * g⁻¹ ∈ A ⊔ zpowers t := fun y hy =>
    (mem_normalizer_iff.1 hg y).1 (mem_sup_left hy)
  have key : ∀ y ∈ A, y * y ≠ 1 → g * y * g⁻¹ ∈ A := by
    intro y hy hy1
    obtain ⟨b, hb, hb' | hb'⟩ := hC.mem_AtX hS (hAt y hy)
    · exact hb' ▸ hb
    · exfalso
      apply hy1
      have h2 := mul_t_sq hinv hb hS.shape.mul_self
      rw [← hb'] at h2
      have : g * (y * y) * g⁻¹ = 1 := by
        rw [show g * (y * y) * g⁻¹ = g * y * g⁻¹ * (g * y * g⁻¹) by group, h2]
      calc y * y = g⁻¹ * (g * (y * y) * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
  by_cases hx1 : x * x = 1
  ·
    have hQ := hS.rad.card_Q
    obtain ⟨b, hb, hbQ⟩ : ∃ b ∈ A, b ∉ Q := by
      by_contra hcon
      push Not at hcon
      have := card_le_of_le (show A ≤ Q from hcon)
      rw [hC.level.card_eq, hQ] at this
      have h12 : 2 ^ 12 ≤ 2 ^ (6 * k) := Nat.pow_le_pow_right (by norm_num) (by
        have := hC.two_le; omega)
      omega
    have hb1 : b * b ≠ 1 := fun h => hbQ (hC.level.mem_Q b hb h)
    have hxb1 : x * b * (x * b) ≠ 1 := by
      intro h
      apply hb1
      have hc := hC.level.comm x hx b hb
      calc b * b = x * x * (b * b) := by rw [hx1, one_mul]
        _ = x * (x * b) * b := by group
        _ = x * (b * x) * b := by rw [hc]
        _ = x * b * (x * b) := by group
        _ = 1 := h
    have h1 := key _ (mul_mem hx hb) hxb1
    have h2 := key b hb hb1
    have := mul_mem h1 (inv_mem h2)
    rwa [show g * (x * b) * g⁻¹ * (g * b * g⁻¹)⁻¹ = g * x * g⁻¹ by group] at this
  · exact key x hx hx1

omit hinv in
theorem wOf_memX [Finite G] {g : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) : wOf t g ∈ A := by
  have hgt : g * t * g⁻¹ ∈ A ⊔ zpowers t := (mem_normalizer_iff.1 hg t).1 (mem_sup_right
    (mem_zpowers t))
  obtain ⟨b, hb, hb' | hb'⟩ := hC.mem_AtX hS hgt
  · exact absurd (hb' ▸ hb) (hC.conj_not_mem_AX hS g)
  · have : wOf t g = t⁻¹ * b * t := by rw [wOf, hb']; group
    rw [this]
    have := (mem_normalizer_iff.1 (inv_mem hC.t_mem_normalizer) b).1 hb
    rwa [inv_inv] at this

theorem normalizes_QX [Finite G] {g : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) :
    g ∈ normalizer (Q : Set G) := by
  refine mem_normalizer_of_conj_mem fun q hq => ?_
  refine hC.level.mem_Q _ (hC.conj_mem_AX hS hinv hg (hC.level.Q_le hq)) ?_
  rw [show g * q * g⁻¹ * (g * q * g⁻¹) = g * (q * q) * g⁻¹ by group, hS.rad.Q_mul_self hq]
  group

omit hinv in
theorem pow_wOf_mem_QX [Finite G] {g : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) :
    wOf t g ^ 2 ^ (k - 1) ∈ Q :=
  hC.level.pow_mem_Q hC.k_pos (hC.wOf_memX hS hg)

theorem cOf_mulX [Finite G] {g h : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G))
    (hh : h ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) :
    cOf ψ t k (g * h) = cOf ψ t k g + lin ψ g (cOf ψ t k h) := by
  have hwg := hC.wOf_memX hS hg
  have hwh := hC.wOf_memX hS hh
  have hconj := hC.conj_mem_AX hS hinv hg hwh
  have hgQ := hC.normalizes_QX hS hinv hg
  apply hS.rad.ψ_inj
  rw [hS.rad.ψ_add, cOf, cOf, cOf, hS.rad.ψ_coord (hC.pow_wOf_mem_QX hS (mul_mem hg hh)),
    hS.rad.ψ_coord (hC.pow_wOf_mem_QX hS hg), hS.rad.ψ_lin hgQ,
    hS.rad.ψ_coord (hC.pow_wOf_mem_QX hS hh), wOf_mul,
    Commute.mul_pow (hC.level.comm _ hwg _ hconj), conj_pow]

omit hinv in
theorem K_le_N1X [Finite G] :
    P ⊔ zpowers x₀ ≤ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) := fun y hy =>
  mem_normalizer_sup (mem_normalizer_of_conj_mem (hC.P_norm y hy))
    (mem_normalizer_zpowers (hS.commute_of_mem_K hy))

omit hinv in
theorem P_le_N1X [Finite G] : P ≤ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) :=
  le_sup_left.trans (hC.K_le_N1X hS)

omit hC hinv in
theorem cOf_eq_zero_of_commuteX {g : G} (hg : g * t = t * g) : cOf ψ t k g = 0 := by
  have hw : wOf t g = 1 := by simp only [wOf]; rw [hg, mul_inv_cancel_right, inv_mul_cancel]
  rw [cOf, hw, one_pow, ← hS.rad.ψ_zero, hS.rad.coord_ψ]

theorem mem_NA_of_cOf_eq_zeroX [Finite G] {g : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) (h : cOf ψ t k g = 0) :
    g ∈ A ⊔ (P ⊔ zpowers x₀ ⊔ zpowers t) := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  have hw := hC.wOf_memX hS hg
  have h1 : wOf t g ^ 2 ^ (k - 1) = 1 := by
    have := hS.rad.ψ_coord (hC.pow_wOf_mem_QX hS hg)
    rw [← this]
    change ψ (cOf ψ t k g) = 1
    rw [h, hS.rad.ψ_zero]
  obtain ⟨a', ha', hsq⟩ :=
    (mem_pw hC.level.comm).1 ((hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos hw).1 h1)
  set b := a'⁻¹
  have hb : b ∈ A := inv_mem ha'
  have htb : t⁻¹ * b * t = b⁻¹ := by
    rw [hS.shape.inv_eq]
    have := hinv b hb
    rwa [hS.shape.inv_eq] at this
  have hbt : b * t * b⁻¹ = g * t * g⁻¹ := by
    conv_rhs => rw [conj_t_eq_wOf, ← hsq]
    calc b * t * b⁻¹ = t * (t⁻¹ * b * t) * b⁻¹ := by group
      _ = t * (b⁻¹ * b⁻¹) := by rw [htb, mul_assoc]
      _ = t * a' ^ 2 := by simp only [b, inv_inv, sq]
  set x := b⁻¹ * g
  have hxt : x * t = t * x := by
    have : x * t * x⁻¹ = t := by
      calc x * t * x⁻¹ = b⁻¹ * (g * t * g⁻¹) * b := by simp only [x]; group
        _ = t := by rw [← hbt]; group
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [this]
  have hxN : x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) :=
    mul_mem (inv_mem (A_le_N1 hb)) hg
  have hxE : x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_sup (hC.normalizes_QX hS hinv hxN) (mem_normalizer_zpowers hxt)
  have hxPt : x ∈ P ⊔ zpowers x₀ ⊔ zpowers t := by
    rw [← hS.shape.normalizer_eq]
    exact ⟨mem_centralizer_singleton_iff.2 hxt, hxE⟩
  have : g = b * x := by simp only [x]; group
  rw [this]
  exact mul_mem (mem_sup_left hb) (mem_sup_right hxPt)

omit hC hinv in
theorem cOf_oneX : cOf ψ t k 1 = 0 := cOf_eq_zero_of_commuteX hS (by group)

theorem affN_mulX [Finite G] {g h : G}
    (hg : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G))
    (hh : h ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    cOf ψ t k (g * h) + lin ψ (g * h) v =
      cOf ψ t k g + lin ψ g (cOf ψ t k h + lin ψ h v) := by
  have hgQ := hC.normalizes_QX hS hinv hg
  have hhQ := hC.normalizes_QX hS hinv hh
  rw [hC.cOf_mulX hS hinv hg hh, hS.rad.lin_mul hgQ hhQ, hS.rad.lin_add hgQ, add_assoc]

@[expose] noncomputable def affHomNX [Finite G] :
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) →* Equiv.Perm V6 where
  toFun g :=
    { toFun := fun v => cOf ψ t k g + lin ψ g v
      invFun := fun v => cOf ψ t k (g : G)⁻¹ + lin ψ (g : G)⁻¹ v
      left_inv := fun v => by
        simp only
        rw [← hC.affN_mulX hS hinv (inv_mem g.2) g.2, inv_mul_cancel, hS.rad.lin_one,
          cOf_oneX hS, zero_add]
      right_inv := fun v => by
        simp only
        rw [← hC.affN_mulX hS hinv g.2 (inv_mem g.2), mul_inv_cancel, hS.rad.lin_one,
          cOf_oneX hS, zero_add] }
  map_one' := Equiv.ext fun v => by
    simp only [Equiv.coe_fn_mk, Subgroup.coe_one, Equiv.Perm.one_apply]
    rw [cOf_oneX hS, hS.rad.lin_one, zero_add]
  map_mul' g h := Equiv.ext fun v => by
    simp only [Equiv.coe_fn_mk, Subgroup.coe_mul, Equiv.Perm.mul_apply]
    exact hC.affN_mulX hS hinv g.2 h.2 v

theorem affHomN_applyX [Finite G] (g : normalizer ((A ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : hC.affHomNX hS hinv g v = cOf ψ t k g + lin ψ g v := rfl

omit hinv in
theorem lin_of_mem_AX [Finite G] {b : G} (hb : b ∈ A) (v : V6) : lin ψ b v = v := by
  rw [hS.rad.lin_eq_iff (hC.mem_normalizer_Q_of_mem_A hb), hC.level.comm b hb _
    (hC.level.Q_le (hS.rad.ψ_mem v)), mul_inv_cancel_right]

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
