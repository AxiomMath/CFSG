module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLayer

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1

variable {G : Type*} [Group G]

namespace Config

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  {k : ℕ} {A : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hC : Config t Q P k A)
  (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
include hS hC hinv

@[expose] def Csub (t : G) (Q A : Subgroup G) : Subgroup G :=
  Rsub t Q A ⊓ centralizer (A : Set G)

omit hS hC hinv in
theorem mem_Csub {x : G} : x ∈ Csub t Q A ↔ x ∈ Rsub t Q A ∧ ∀ y ∈ A, x * y = y * x := by
  rw [Csub, mem_inf, mem_centralizer_iff]
  exact and_congr_right fun _ => ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩

omit hinv in
theorem A_le_C [Finite G] : A ≤ Csub t Q A := fun b hb =>
  mem_Csub.2 ⟨hC.At_le_R hS (mem_sup_left hb), fun y hy => hC.level.comm b hb y hy⟩

theorem t_not_mem_C [Finite G] : t ∉ Csub t Q A := by
  have hQ := hS.rad.card_Q
  intro ht
  have h := (mem_Csub.1 ht).2
  have hle : A ≤ Q := fun x hx => by
    refine hC.level.mem_Q x hx ?_
    have h1 := hinv x hx
    rw [h x hx, mul_inv_cancel_right] at h1
    calc x * x = x⁻¹ * x := by rw [← h1]
      _ = 1 := inv_mul_cancel x
  have := card_le_of_le hle
  rw [hC.level.card_eq, hQ] at this
  have h12 : 2 ^ 12 ≤ 2 ^ (6 * k) := Nat.pow_le_pow_right (by norm_num) (by
    have := hC.two_le; omega)
  omega

theorem exists_C_cOf [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) (v : V6) :
    ∃ x ∈ Csub t Q A, cOf ψ t k x = v := by
  obtain ⟨r, hr, hrv⟩ := htr v
  rcases hC.R_centralizes hS hinv hM3 hM4 htr hr with h | h
  · exact ⟨r, mem_Csub.2 ⟨hr, h⟩, hrv⟩
  · refine ⟨r * t, mem_Csub.2 ⟨mul_mem hr (t_mem_R hS), h⟩, ?_⟩
    rw [hC.cOf_mul_R hS hinv hr (t_mem_R hS), cOf_eq_zero_of_commute hS rfl, add_zero, hrv]

theorem mem_A_of_cOf_C [Finite G] {x : G} (hx : x ∈ Csub t Q A) (h : cOf ψ t k x = 0) :
    x ∈ A := by
  obtain ⟨b, hb, hxb | hxb⟩ := hC.mem_At hS (hC.mem_At_of_cOf hS hinv (mem_Csub.1 hx).1 h)
  · exact hxb ▸ hb
  · exfalso
    apply hC.t_not_mem_C hS hinv
    have := mul_mem (inv_mem (hC.A_le_C hS hb)) hx
    rwa [hxb, ← mul_assoc, inv_mul_cancel, one_mul] at this

omit hS hC hinv in
theorem C_le_R : Csub t Q A ≤ Rsub t Q A := inf_le_left

theorem cm_eq_wOf_inv [Finite G] {x : G}
    (hx : x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G)) :
    cm t x = (wOf t x)⁻¹ := by
  have h := hinv _ (hC.wOf_mem hS hx)
  rw [cm, conj_t_eq_wOf, show t * wOf t x * t⁻¹ = t * wOf t x * t⁻¹ from rfl]
  calc t * wOf t x * t⁻¹ = (wOf t x)⁻¹ := h
    _ = (wOf t x)⁻¹ := rfl

theorem decomp_C [Finite G] {x s : G} (hx : x ∈ Csub t Q A) (hs : s ∈ Csub t Q A)
    (h : cOf ψ t k x = cOf ψ t k s) : ∃ b ∈ A, x = s * b := by
  refine ⟨s⁻¹ * x, hC.mem_A_of_cOf_C hS hinv (mul_mem (inv_mem hs) hx) ?_, by group⟩
  rw [hC.cOf_mul_R hS hinv (inv_mem (C_le_R hs)) (C_le_R hx), hC.cOf_inv_R hS hinv (C_le_R hs),
    h, v6_add_self]

theorem cm_mem_A_C [Finite G] {x : G} (hx : x ∈ Csub t Q A) : cm t x ∈ A := by
  rw [hC.cm_eq_wOf_inv hS hinv (mem_Rsub.1 (C_le_R hx)).1]
  exact inv_mem (hC.wOf_mem hS (mem_Rsub.1 (C_le_R hx)).1)

theorem cm_mul_C [Finite G] {x y : G} (hx : x ∈ Csub t Q A) (hy : y ∈ Csub t Q A) :
    cm t (x * y) = cm t x * cm t y := by
  have h1 : cm t (x * y) = x * cm t y * x⁻¹ * cm t x := by simp only [cm]; group
  rw [h1, (mem_Csub.1 hx).2 _ (hC.cm_mem_A_C hS hinv hy), mul_inv_cancel_right,
    hC.level.comm _ (hC.cm_mem_A_C hS hinv hy) _ (hC.cm_mem_A_C hS hinv hx)]

@[expose] def phiHom [Finite G] : Csub t Q A →* G where
  toFun x := cm t x
  map_one' := by simp [cm]
  map_mul' x y := hC.cm_mul_C hS hinv x.2 y.2

@[expose] noncomputable def cHomC [Finite G] : Csub t Q A →* Multiplicative V6 where
  toFun x := Multiplicative.ofAdd (cOf ψ t k x)
  map_one' := by
    change Multiplicative.ofAdd (cOf ψ t k 1) = 1
    rw [cOf_one hS]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (cOf ψ t k (x * y)) = _
    rw [hC.cOf_mul_R hS hinv (C_le_R x.2) (C_le_R y.2)]
    rfl

theorem cOf_eq_zero_of_mem_A {b : G} (hb : b ∈ A) : cOf ψ t k b = 0 := by
  have h := hinv b hb
  have hw : wOf t b = b⁻¹ * b⁻¹ := by
    rw [wOf, show t⁻¹ * (b * t * b⁻¹) = (t⁻¹ * b * t) * b⁻¹ by group]
    rw [hS.shape.inv_eq]
    rw [hS.shape.inv_eq] at h
    rw [h]
  have hk := hC.k_pos
  rw [cOf, hw, show b⁻¹ * b⁻¹ = (b ^ 2)⁻¹ by rw [sq, _root_.mul_inv_rev], inv_pow, ← pow_mul,
    ← pow_succ', Nat.sub_add_cancel hk, hC.level.pow_eq_one b hb, inv_one, ← hS.rad.ψ_zero,
    hS.rad.coord_ψ]

theorem card_C [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) :
    Nat.card (Csub t Q A) = 2 ^ (6 * (k + 1)) := by
  have hker : (hC.cHomC hS hinv).ker = A.subgroupOf (Csub t Q A) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact hC.mem_A_of_cOf_C hS hinv x.2 (congrArg Multiplicative.toAdd h)
    · intro h
      change Multiplicative.ofAdd (cOf ψ t k x) = 1
      rw [hC.cOf_eq_zero_of_mem_A hS hinv h]
      rfl
  have hrange : (hC.cHomC hS hinv).range = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, hx, hxv⟩ := hC.exists_C_cOf hS hinv hM3 hM4 htr (Multiplicative.toAdd v)
    exact ⟨⟨x, hx⟩, by change Multiplicative.ofAdd (cOf ψ t k x) = v; rw [hxv]; rfl⟩
  have h := card_mul_index (hC.cHomC hS hinv).ker
  rw [index_ker, hker, hrange, card_top,
    Nat.card_congr (subgroupOfEquivOfLe (hC.A_le_C hS)).toEquiv, hC.level.card_eq] at h
  have h64 : Nat.card (Multiplicative V6) = 64 := by
    rw [Nat.card_eq_fintype_card]; simp
  rw [h64] at h
  rw [← h, mul_add, mul_one, pow_add]
  norm_num

theorem cm_eq_one_iff_C [Finite G] {x : G} (hx : x ∈ Csub t Q A) : cm t x = 1 ↔ x ∈ Q := by
  rw [cm_eq_one_iff_commute]
  constructor
  · intro hxt
    have h : x ∈ centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) :=
      ⟨mem_centralizer_singleton_iff.2 hxt, mem_centralizer_iff.2 fun q hq =>
        ((mem_Rsub.1 (C_le_R hx)).2 q hq).symm⟩
    rw [hS.shape.centralizer_eq] at h
    obtain ⟨q, hq, hxq | hxq⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 h
    · exact hxq ▸ hq
    · exfalso
      apply hC.t_not_mem_C hS hinv
      have := mul_mem (inv_mem (hC.A_le_C hS (hC.level.Q_le hq))) hx
      rwa [hxq, ← mul_assoc, inv_mul_cancel, one_mul] at this
  · intro hq
    exact hS.shape.commute_of_mem (hS.rad.Q_le_L hq)

omit hinv in
theorem conj_mem_C [Finite G] {x : G} (hx : x ∈ P) {y : G} (hy : y ∈ Csub t Q A) :
    x * y * x⁻¹ ∈ Csub t Q A := by
  refine mem_Csub.2 ⟨hC.conj_mem_R hS hx (C_le_R hy), fun b hb => ?_⟩
  have hb' : x⁻¹ * b * x ∈ A := by
    have := hC.P_norm _ (inv_mem hx) b hb
    rwa [inv_inv] at this
  have h1 := (mem_Csub.1 hy).2 _ hb'
  calc x * y * x⁻¹ * b = x * (y * (x⁻¹ * b * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * b * x) * y) * x⁻¹ := by rw [h1]
    _ = b * (x * y * x⁻¹) := by group

theorem C_comm [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) :
    ∀ x ∈ Csub t Q A, ∀ y ∈ Csub t Q A, x * y = y * x := by
  have hκQ : ∀ x ∈ Csub t Q A, ∀ y ∈ Csub t Q A, x * y * x⁻¹ * y⁻¹ ∈ Q := by
    intro x hx y hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ Csub t Q A :=
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    refine (hC.cm_eq_one_iff_C hS hinv hmem).1 ?_
    have e := (hC.phiHom hS hinv).map_mul ⟨x * y, mul_mem hx hy⟩ ⟨x⁻¹ * y⁻¹,
      mul_mem (inv_mem hx) (inv_mem hy)⟩
    have hphi : ∀ z : Csub t Q A, hC.phiHom hS hinv z = cm t z := fun _ => rfl
    have h1 : cm t (x * y * x⁻¹ * y⁻¹) = cm t (x * y) * cm t (x⁻¹ * y⁻¹) := by
      have := hC.cm_mul_C hS hinv (mul_mem hx hy) (mul_mem (inv_mem hx) (inv_mem hy))
      rwa [show x * y * (x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ by group] at this
    rw [h1, hC.cm_mul_C hS hinv hx hy, hC.cm_mul_C hS hinv (inv_mem hx) (inv_mem hy)]
    have hi : ∀ z ∈ Csub t Q A, cm t z⁻¹ = (cm t z)⁻¹ := by
      intro z hz
      have := hC.cm_mul_C hS hinv hz (inv_mem hz)
      rw [mul_inv_cancel, show cm t 1 = 1 by simp [cm]] at this
      exact eq_inv_of_mul_eq_one_right this.symm
    rw [hi x hx, hi y hy]
    have hc := hC.level.comm _ (hC.cm_mem_A_C hS hinv hx) _ (hC.cm_mem_A_C hS hinv hy)
    calc cm t x * cm t y * ((cm t x)⁻¹ * (cm t y)⁻¹)
        = cm t y * cm t x * ((cm t x)⁻¹ * (cm t y)⁻¹) := by rw [hc]
      _ = 1 := by group
  choose sC hsC hsCc using hC.exists_C_cOf hS hinv hM3 hM4 htr
  have hcent : ∀ x ∈ Csub t Q A, ∀ b ∈ A, x * b = b * x := fun x hx b hb =>
    (mem_Csub.1 hx).2 b hb
  have hκb : ∀ x y b : G, y * b = b * y → (x * b) * y * (x * b)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    intro x y b h
    calc (x * b) * y * (x * b)⁻¹ * y⁻¹ = x * (b * y) * b⁻¹ * x⁻¹ * y⁻¹ := by group
      _ = x * (y * b) * b⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  have hκb' : ∀ x y b : G, x * b = b * x → x * (y * b) * x⁻¹ * (y * b)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    intro x y b h
    have h' : b * x⁻¹ = x⁻¹ * b := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, inv_mul_cancel_left]
    calc x * (y * b) * x⁻¹ * (y * b)⁻¹ = x * y * (b * x⁻¹) * b⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * b) * b⁻¹ * y⁻¹ := by rw [h']
      _ = x * y * x⁻¹ * y⁻¹ := by group
  set β : V6 → V6 → V6 := fun u v => coord ψ (sC u * sC v * (sC u)⁻¹ * (sC v)⁻¹)
  have hβψ : ∀ u v, ψ (β u v) = sC u * sC v * (sC u)⁻¹ * (sC v)⁻¹ := fun u v =>
    hS.rad.ψ_coord (hκQ _ (hsC u) _ (hsC v))
  have hQcent : ∀ x ∈ Csub t Q A, ∀ q ∈ Q, x * q = q * x := fun x hx q hq =>
    hcent x hx q (hC.level.Q_le hq)
  have hβ1 : ∀ u u' v, β (u + u') v = β u v + β u' v := by
    intro u u' v
    obtain ⟨b, hb, hbeq⟩ := hC.decomp_C hS hinv (hsC (u + u')) (mul_mem (hsC u) (hsC u')) (by
      rw [hsCc, hC.cOf_mul_R hS hinv (C_le_R (hsC u)) (C_le_R (hsC u')), hsCc, hsCc])
    apply hS.rad.ψ_inj
    rw [hβψ, hS.rad.ψ_add, hβψ, hβψ, hbeq, hκb _ _ _ (hcent _ (hsC v) b hb)]
    have hq' := hκQ _ (hsC u') _ (hsC v)
    have hq0 := hκQ _ (hsC u) _ (hsC v)
    have hc := hQcent _ (hsC u) _ hq'
    calc sC u * sC u' * sC v * (sC u * sC u')⁻¹ * (sC v)⁻¹
        = sC u * (sC u' * sC v * (sC u')⁻¹ * (sC v)⁻¹) * sC v * (sC u)⁻¹ * (sC v)⁻¹ := by
          group
      _ = (sC u' * sC v * (sC u')⁻¹ * (sC v)⁻¹) * sC u * sC v * (sC u)⁻¹ * (sC v)⁻¹ := by
          rw [hc]
      _ = (sC u' * sC v * (sC u')⁻¹ * (sC v)⁻¹) * (sC u * sC v * (sC u)⁻¹ * (sC v)⁻¹) := by
          group
      _ = _ := hS.rad.Q_comm hq' hq0
  have hκmul : ∀ x y y' : G, x * (y * y') * x⁻¹ * (y * y')⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by
    intro x y y'; group
  have hβ2 : ∀ u v v', β u (v + v') = β u v + β u v' := by
    intro u v v'
    obtain ⟨b, hb, hbeq⟩ := hC.decomp_C hS hinv (hsC (v + v')) (mul_mem (hsC v) (hsC v')) (by
      rw [hsCc, hC.cOf_mul_R hS hinv (C_le_R (hsC v)) (C_le_R (hsC v')), hsCc, hsCc])
    apply hS.rad.ψ_inj
    rw [hβψ, hS.rad.ψ_add, hβψ, hβψ, hbeq, hκb' _ _ _ (hcent _ (hsC u) b hb), hκmul]
    have hq' := hκQ _ (hsC u) _ (hsC v')
    have hc := hQcent _ (hsC v) _ hq'
    rw [hc, mul_inv_cancel_right]
  have hβ3 : ∀ i : Fin 6, ∀ u v, β (genMat ε i *ᵥ u) (genMat ε i *ᵥ v) = genMat ε i *ᵥ β u v := by
    intro i u v
    have hp := hS.rad.p_mem i
    have hxu := hC.conj_mem_C hS hp (hsC u)
    have hxv := hC.conj_mem_C hS hp (hsC v)
    obtain ⟨b, hb, hbeq⟩ := hC.decomp_C hS hinv (hsC (genMat ε i *ᵥ u)) hxu (by
      rw [hsCc, hC.cOf_conj_P hS hinv hp (C_le_R (hsC u)), hsCc, hS.rad.lin_p])
    obtain ⟨b', hb', hbeq'⟩ := hC.decomp_C hS hinv (hsC (genMat ε i *ᵥ v)) hxv (by
      rw [hsCc, hC.cOf_conj_P hS hinv hp (C_le_R (hsC v)), hsCc, hS.rad.lin_p])
    apply hS.rad.ψ_inj
    rw [hβψ, ← hS.rad.p_act, hβψ, hbeq, hbeq',
      hκb _ _ _ (hcent _ (mul_mem hxv (hC.A_le_C hS hb')) b hb),
      hκb' _ _ _ (hcent _ hxu b' hb')]
    group
  have hF := hM3 β hβ1 hβ2 hβ3
  intro x hx y hy
  obtain ⟨b, hb, hbx⟩ := hC.decomp_C hS hinv hx (hsC (cOf ψ t k x)) (hsCc _).symm
  obtain ⟨b', hb', hby⟩ := hC.decomp_C hS hinv hy (hsC (cOf ψ t k y)) (hsCc _).symm
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [hbx, hby, hκb _ _ _ (hcent _ (mul_mem (hsC _) (hC.A_le_C hS hb')) b hb),
      hκb' _ _ _ (hcent _ (hsC _) b' hb'), ← hβψ, hF, hS.rad.ψ_zero]
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem level_C [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) :
    Level Q (k + 1) (Csub t Q A) := by
  have hk := hC.two_le
  have hcomm := hC.C_comm hS hinv hM3 hM4 htr
  have hsqA : ∀ x ∈ Csub t Q A, x * x ∈ A := fun x hx => by
    refine hC.mem_A_of_cOf_C hS hinv (mul_mem hx hx) ?_
    rw [hC.cOf_mul_R hS hinv (C_le_R hx) (C_le_R hx), v6_add_self]
  refine ⟨hcomm, hC.card_C hS hinv hM3 hM4 htr, (hC.level.Q_le).trans (hC.A_le_C hS),
    fun x hx hx1 => ?_, fun x hx => ?_⟩
  · have hcm := hC.cm_mem_A_C hS hinv hx
    have hcm2 : cm t x * cm t x = 1 := by
      rw [← hC.cm_mul_C hS hinv hx hx, hx1]; simp [cm]
    have hcmQ := hC.level.mem_Q _ hcm hcm2
    have hπ : (cm t x) ^ 2 ^ (k - 1) = 1 := by
      rw [show 2 ^ (k - 1) = 2 * 2 ^ (k - 2) by rw [← pow_succ']; congr 1; omega, pow_mul, sq,
        hcm2, one_pow]
    have hc0 : cOf ψ t k x = 0 := by
      rw [cOf, ← inv_inv (wOf t x), ← hC.cm_eq_wOf_inv hS hinv (mem_Rsub.1 (C_le_R hx)).1,
        inv_pow, hπ, inv_one, ← hS.rad.ψ_zero, hS.rad.coord_ψ]
    exact hC.level.mem_Q x (hC.mem_A_of_cOf_C hS hinv hx hc0) hx1
  · rw [pow_succ', pow_mul, sq]
    exact hC.level.pow_eq_one _ (hsqA x hx)

theorem tact_C [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (hE : EndF2 ε)
    (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) : TAct t (k + 1) (Csub t Q A) := by
  have hk := hC.two_le
  have hcomm := hC.C_comm hS hinv hM3 hM4 htr
  have hLC := hC.level_C hS hinv hM3 hM4 htr
  have hsqA : ∀ x ∈ Csub t Q A, x * x ∈ A := fun x hx => by
    refine hC.mem_A_of_cOf_C hS hinv (mul_mem hx hx) ?_
    rw [hC.cOf_mul_R hS hinv (C_le_R hx) (C_le_R hx), v6_add_self]
  set μ : G → G := fun x => x * x * (cm t x)⁻¹
  have hμA : ∀ x ∈ Csub t Q A, μ x ∈ A := fun x hx =>
    mul_mem (hsqA x hx) (inv_mem (hC.cm_mem_A_C hS hinv hx))
  have hμmul : ∀ x ∈ Csub t Q A, ∀ y ∈ Csub t Q A, μ (x * y) = μ x * μ y := by
    intro x hx y hy
    simp only [μ]
    rw [hC.cm_mul_C hS hinv hx hy]
    have hcx := hC.A_le_C hS (hC.cm_mem_A_C hS hinv hx)
    have hcy := hC.A_le_C hS (hC.cm_mem_A_C hS hinv hy)
    have h1 := hcomm _ hx _ hy
    have h2 := hcomm _ hy _ (inv_mem hcx)
    have h3 := hcomm _ (mul_mem hx hx) _ (inv_mem hcy)
    calc x * y * (x * y) * (cm t x * cm t y)⁻¹ = x * (y * x) * y * (cm t y)⁻¹ * (cm t x)⁻¹ := by
          group
      _ = x * (x * y) * y * (cm t y)⁻¹ * (cm t x)⁻¹ := by rw [h1]
      _ = x * x * (y * y * (cm t y)⁻¹) * (cm t x)⁻¹ := by group
      _ = x * x * (cm t x)⁻¹ * (y * y * (cm t y)⁻¹) := by
          rw [mul_assoc (x * x), hcomm _ (mul_mem (mul_mem hy hy) (inv_mem hcy)) _ (inv_mem hcx),
            ← mul_assoc]
  have hμ1 : ∀ b ∈ A, μ b = 1 := by
    intro b hb
    simp only [μ]
    rw [cm_eq_sq hinv hb, mul_inv_cancel]
  have hμQ : ∀ x ∈ Csub t Q A, μ x ∈ Q := by
    intro x hx
    refine hC.level.mem_Q _ (hμA x hx) ?_
    rw [← hμmul x hx x hx, hμ1 _ (hsqA x hx)]
  choose sC hsC hsCc using hC.exists_C_cOf hS hinv hM3 hM4 htr
  have hμdec : ∀ x ∈ Csub t Q A, μ x = μ (sC (cOf ψ t k x)) := by
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hC.decomp_C hS hinv hx (hsC _) (hsCc _).symm
    conv_lhs => rw [hbx]
    rw [hμmul _ (hsC _) _ (hC.A_le_C hS hb), hμ1 b hb, mul_one]
  set f : V6 → V6 := fun u => coord ψ (μ (sC u))
  have hfψ : ∀ u, ψ (f u) = μ (sC u) := fun u => hS.rad.ψ_coord (hμQ _ (hsC u))
  have hfadd : ∀ u u', f (u + u') = f u + f u' := by
    intro u u'
    apply hS.rad.ψ_inj
    have hss := mul_mem (hsC u) (hsC u')
    rw [hfψ, hS.rad.ψ_add, hfψ, hfψ, hμdec _ (hsC (u + u')), hsCc,
      ← hμmul _ (hsC u) _ (hsC u'), hμdec _ hss,
      hC.cOf_mul_R hS hinv (C_le_R (hsC u)) (C_le_R (hsC u')), hsCc, hsCc]
  have hfeq : ∀ i : Fin 6, ∀ u, f (genMat ε i *ᵥ u) = genMat ε i *ᵥ f u := by
    intro i u
    have hp := hS.rad.p_mem i
    have hxu := hC.conj_mem_C hS hp (hsC u)
    apply hS.rad.ψ_inj
    rw [hfψ, ← hS.rad.p_act, hfψ]
    have hc : cOf ψ t k (p i * sC u * (p i)⁻¹) = genMat ε i *ᵥ u := by
      rw [hC.cOf_conj_P hS hinv hp (C_le_R (hsC u)), hsCc, hS.rad.lin_p]
    rw [← hc, ← hμdec _ hxu]
    simp only [μ]
    rw [cm_conj hS hp]
    group
  rcases hE f hfadd hfeq with h0 | hid
  · left
    intro x hx
    have hμx : μ x = 1 := by rw [hμdec x hx, ← hfψ, h0, hS.rad.ψ_zero]
    have hsq : x * x = cm t x := by
      have := hμx
      simp only [μ] at this
      exact mul_inv_eq_one.1 this
    have h3 : x * x = x * (t * x⁻¹ * t⁻¹) := by rw [hsq]; simp only [cm]; group
    have h2 : x = t * x⁻¹ * t⁻¹ := mul_left_cancel h3
    calc t * x * t⁻¹ = (t * x⁻¹ * t⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [← h2]
  · right
    refine ⟨by omega, fun x hx => ?_⟩
    have hxN := (mem_Rsub.1 (C_le_R hx)).1
    have hcmA := hC.cm_mem_A_C hS hinv hx
    have hcmC := hC.A_le_C hS hcmA
    have hπQ : (cm t x) ^ 2 ^ (k - 1) ∈ Q := hC.level.pow_mem_Q hC.k_pos hcmA
    have hμx : μ x = (cm t x) ^ 2 ^ (k - 1) := by
      rw [hμdec x hx, ← hfψ, hid, cOf, hS.rad.ψ_coord (hC.pow_wOf_mem_Q hS hxN),
        ← inv_inv (wOf t x), ← hC.cm_eq_wOf_inv hS hinv hxN, inv_pow]
      exact inv_eq_of_mul_eq_one_right (hS.rad.Q_mul_self hπQ)
    have hcm : cm t x = x * x * (μ x)⁻¹ := by
      have hc := hcomm _ hcmC _ (mul_mem hx hx)
      simp only [μ]
      rw [_root_.mul_inv_rev, inv_inv, ← mul_assoc, ← hc, mul_inv_cancel_right]
    have hμx' : μ x = x ^ 2 ^ k := by
      have hμq := hμQ x hx
      have hμ2 : (μ x)⁻¹ ^ 2 ^ (k - 1) = 1 := by
        rw [show 2 ^ (k - 1) = 2 * 2 ^ (k - 2) by rw [← pow_succ']; congr 1; omega, pow_mul,
          sq, ← _root_.mul_inv_rev, hS.rad.Q_mul_self hμq, inv_one, one_pow]
      rw [hμx, hcm, Commute.mul_pow (hcomm _ (mul_mem hx hx) _ (inv_mem (hC.level.Q_le hμq |>
        hC.A_le_C hS))), hμ2, mul_one, ← sq, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hC.k_pos]
    have h1 : t * x⁻¹ * t⁻¹ = x⁻¹ * cm t x := by simp only [cm]; group
    calc t * x * t⁻¹ = (t * x⁻¹ * t⁻¹)⁻¹ := by group
      _ = (x⁻¹ * (x * x * (μ x)⁻¹))⁻¹ := by rw [h1, hcm]
      _ = μ x * x⁻¹ := by group
      _ = x⁻¹ * μ x := hcomm _ (hC.A_le_C hS (hμA x hx)) _ (inv_mem hx)
      _ = x⁻¹ * x ^ 2 ^ (k + 1 - 1) := by rw [hμx', Nat.add_sub_cancel]

theorem pw_C [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) :
    pw (Csub t Q A) 2 = A := by
  have hLC := hC.level_C hS hinv hM3 hM4 htr
  have hle : pw (Csub t Q A) 2 ≤ A := by
    rw [pw, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [sq]
    refine hC.mem_A_of_cOf_C hS hinv (mul_mem hx hx) ?_
    rw [hC.cOf_mul_R hS hinv (C_le_R hx) (C_le_R hx), v6_add_self]
  refine eq_of_le_of_card_ge hle ?_
  rw [hLC.card_pw_two hS.rad.card_Q (fun _ hq => hS.rad.Q_mul_self hq) (by omega),
    Nat.add_sub_cancel, hC.level.card_eq]

theorem normalizer_le_C [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) :
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤ Csub t Q A ⊔ (P ⊔ zpowers t) := by
  intro g hg
  obtain ⟨x, hx, hxg⟩ := hC.exists_C_cOf hS hinv hM3 hM4 htr (cOf ψ t k g)
  have hxN := (mem_Rsub.1 (C_le_R hx)).1
  have hy : cOf ψ t k (x⁻¹ * g) = 0 := by
    rw [hC.cOf_mul hS hinv (inv_mem hxN) hg, hC.cOf_inv_R hS hinv (C_le_R hx)]
    have hlin : lin ψ x⁻¹ (cOf ψ t k g) = cOf ψ t k g := by
      rw [hS.rad.lin_eq_iff (hC.normalizes_Q hS hinv (inv_mem hxN))]
      have := (mem_Rsub.1 (C_le_R (inv_mem hx))).2 _ (hS.rad.ψ_mem (cOf ψ t k g))
      rw [this, mul_inv_cancel_right]
    rw [hlin, hxg, v6_add_self]
  have hyNA := hC.mem_NA_of_cOf_eq_zero hS hinv (mul_mem (inv_mem hxN) hg) hy
  have hle : A ⊔ (P ⊔ zpowers t) ≤ Csub t Q A ⊔ (P ⊔ zpowers t) :=
    sup_le_sup_right (hC.A_le_C hS) _
  have : g = x * (x⁻¹ * g) := by group
  rw [this]
  exact mul_mem (mem_sup_left hx) (hle hyNA)

theorem next_level [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (hE : EndF2 ε)
    (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) :
    Config t Q P (k + 1) (Csub t Q A) := by
  refine ⟨by have := hC.two_le; omega, hC.level_C hS hinv hM3 hM4 htr,
    hC.tact_C hS hinv hM3 hM4 hE htr, fun x hx y hy => hC.conj_mem_C hS hx hy, ?_⟩
  rw [hC.pw_C hS hinv hM3 hM4 htr]
  exact hC.normalizer_le_C hS hinv hM3 hM4 htr

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
