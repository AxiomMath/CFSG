module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitAct
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1D

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn

variable {G : Type} [Group G]

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {k : ℕ} {A : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) k A) (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
include hS hC hinv

theorem R_conj_memX [Finite G] {r : G} (hr : r ∈ Rsub t Q A) : ∀ x ∈ A, r * x * r⁻¹ ∈ A :=
  fun _ hx => hC.conj_mem_AX hS hinv (mem_Rsub.1 hr).1 hx

theorem dl_mem_pwX [Finite G] {r : G} (hr : r ∈ Rsub t Q A) {x : G} (hx : x ∈ A) :
    dl r x ∈ pw A 2 := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  have hrx := hC.R_conj_memX hS hinv hr x hx
  have hπ : (r * x * r⁻¹) ^ 2 ^ (k - 1) = x ^ 2 ^ (k - 1) := by
    rw [conj_pow, (mem_Rsub.1 hr).2 _ (hC.level.pow_mem_Q hC.k_pos hx), mul_inv_cancel_right]
  refine (hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos (dl_mem (hC.R_conj_memX hS hinv hr) hx)).1 ?_
  rw [dl, Commute.mul_pow (hC.level.comm _ hrx _ (inv_mem hx)), hπ, inv_pow, mul_inv_cancel]

theorem cOf_mul_RX [Finite G] {r s : G} (hr : r ∈ Rsub t Q A) (hs : s ∈ Rsub t Q A) :
    cOf ψ t k (r * s) = cOf ψ t k r + cOf ψ t k s := by
  rw [hC.cOf_mulX hS hinv (mem_Rsub.1 hr).1 (mem_Rsub.1 hs).1]
  congr 1
  rw [hS.rad.lin_eq_iff (hC.normalizes_QX hS hinv (mem_Rsub.1 hr).1),
    (mem_Rsub.1 hr).2 _ (hS.rad.ψ_mem _), mul_inv_cancel_right]

theorem mem_At_of_cOfX [Finite G] {r : G} (hr : r ∈ Rsub t Q A) (h : cOf ψ t k r = 0) :
    r ∈ A ⊔ zpowers t := by
  have hNA := hC.mem_NA_of_cOf_eq_zeroX hS hinv (mem_Rsub.1 hr).1 h
  obtain ⟨b, hb, x, hx, rfl⟩ := exists_mul_of_mem_sup_normalizer hC.PT_le_normalizer hNA
  have hxc : ∀ q ∈ Q, x * q = q * x := by
    intro q hq
    have h1 := (mem_Rsub.1 hr).2 q hq
    have h2 := hC.level.comm b hb q (hC.level.Q_le hq)
    have : b * (x * q) = b * (q * x) := by
      calc b * (x * q) = b * x * q := (mul_assoc _ _ _).symm
        _ = q * (b * x) := h1
        _ = q * b * x := (mul_assoc _ _ _).symm
        _ = b * q * x := by rw [h2]
        _ = b * (q * x) := mul_assoc _ _ _
    exact mul_left_cancel this
  obtain ⟨y, hy, hxy | hxy⟩ := (hS.mem_supT_iff hS.K_le_H₀).1 hx
  · have hyQ : y ∈ Q := hS.mem_Q_of_mem_K hy (mem_centralizer_iff.2 fun q hq =>
      (hxy ▸ hxc q hq).symm)
    rw [hxy]
    exact mem_sup_left (mul_mem hb (hC.level.Q_le hyQ))
  · have hyQ : y ∈ Q := by
      refine hS.mem_Q_of_mem_K hy (mem_centralizer_iff.2 fun q hq => ?_)
      have h1 := hxc q hq
      rw [hxy] at h1
      have h2 := hS.shape.commute_of_mem (hS.rad.Q_le_L hq)
      have : y * q * t = q * y * t := by
        calc y * q * t = y * (q * t) := mul_assoc _ _ _
          _ = y * (t * q) := by rw [h2]
          _ = y * t * q := (mul_assoc _ _ _).symm
          _ = q * (y * t) := h1
          _ = q * y * t := (mul_assoc _ _ _).symm
      exact (mul_right_cancel this).symm
    rw [hxy, ← mul_assoc]
    exact mul_mem (mem_sup_left (mul_mem hb (hC.level.Q_le hyQ))) (mem_sup_right (mem_zpowers t))

omit hinv in
theorem level_mX [Finite G] {m : ℕ} (hm : m + 1 ≤ k) : Level Q (k - m) (pw A (2 ^ m)) :=
  hC.level.level_pw hS.rad.card_Q (fun _ hq => hS.rad.Q_mul_self hq) m hm

omit hinv in
theorem pi_mem_QX [Finite G] {m : ℕ} (hm : m + 1 ≤ k) {b : G} (hb : b ∈ pw A (2 ^ m)) :
    b ^ 2 ^ (k - 1 - m) ∈ Q := by
  have := (hC.level_mX hS hm).pow_mem_Q (by omega) hb
  rwa [show k - m - 1 = k - 1 - m by omega] at this

omit hinv in
theorem pi_eq_one_iffX [Finite G] {m : ℕ} (hm : m + 1 ≤ k) {b : G} (hb : b ∈ pw A (2 ^ m)) :
    b ^ 2 ^ (k - 1 - m) = 1 ↔ b ∈ pw A (2 ^ (m + 1)) := by
  have h := (hC.level_mX hS hm).pow_eq_one_iff hS.rad.card_Q
    (fun q hq => hS.rad.Q_mul_self hq) (by omega) hb
  rw [show k - m - 1 = k - 1 - m by omega, pw_pw hC.level.comm, ← pow_succ] at h
  exact h

omit hinv in
theorem pi_mul_of_memX [Finite G] {m : ℕ} (hm : m + 1 ≤ k) {b y : G} (hb : b ∈ pw A (2 ^ m))
    (hy : y ∈ pw A (2 ^ (m + 1))) : (b * y) ^ 2 ^ (k - 1 - m) = b ^ 2 ^ (k - 1 - m) := by
  have hy' : y ∈ pw A (2 ^ m) := by
    rw [pow_succ, ← pw_pw hC.level.comm] at hy
    exact pw_le _ _ hy
  rw [hC.pi_mul hb hy', (hC.pi_eq_one_iffX hS hm hy').2 hy, mul_one]

theorem pi_conj_RX [Finite G] {m : ℕ} (hm : m + 1 ≤ k) {r : G} (hr : r ∈ Rsub t Q A) {b : G}
    (hb : b ∈ pw A (2 ^ m)) : (r * b * r⁻¹) ^ 2 ^ (k - 1 - m) = b ^ 2 ^ (k - 1 - m) := by
  have hdl : dl r b ∈ pw A (2 ^ (1 + m)) :=
    dl_pw_mem hC.level.comm (hC.R_conj_memX hS hinv hr)
      (m := 1) (fun x hx => by rw [pow_one]; exact hC.dl_mem_pwX hS hinv hr hx) m hb
  rw [conj_eq_dl_mul, hC.level.comm _ (dl_mem (hC.R_conj_memX hS hinv hr) (pw_le A _ hb)) _
    (pw_le A _ hb), hC.pi_mul_of_memX hS hm hb (by rwa [add_comm] at hdl)]

theorem pi_dl_mul_leftX [Finite G] {m : ℕ} (hm : m + 1 ≤ k) {r r' : G} (hr : r ∈ Rsub t Q A)
    (hrm : ∀ x ∈ A, dl r x ∈ pw A (2 ^ m))
    (hrm' : ∀ x ∈ A, dl r' x ∈ pw A (2 ^ m)) {x : G} (hx : x ∈ A) :
    dl (r * r') x ^ 2 ^ (k - 1 - m) = dl r x ^ 2 ^ (k - 1 - m) * dl r' x ^ 2 ^ (k - 1 - m) := by
  rw [dl_mul_left, hC.pi_mul (pw_conj_mem_gen hC.level.comm (hC.R_conj_memX hS hinv hr)
    (hrm' x hx)) (hrm x hx), hC.pi_conj_RX hS hinv hm hr (hrm' x hx)]
  exact Commute.pow_pow (hC.level.comm _ (pw_le A _ (hrm' x hx)) _ (pw_le A _ (hrm x hx))) _ _

theorem pi_dl_mul_rightX [Finite G] {m : ℕ} {r : G} (hr : r ∈ Rsub t Q A)
    (hrm : ∀ x ∈ A, dl r x ∈ pw A (2 ^ m)) {x x' : G} (hx : x ∈ A) (hx' : x' ∈ A) :
    dl r (x * x') ^ 2 ^ (k - 1 - m) = dl r x ^ 2 ^ (k - 1 - m) * dl r x' ^ 2 ^ (k - 1 - m) := by
  rw [dl_mul_right hC.level.comm (hC.R_conj_memX hS hinv hr) hx hx', hC.pi_mul (hrm x hx)
    (hrm x' hx')]

theorem pi_dl_pwX [Finite G] {m : ℕ} (hm : m + 1 ≤ k) {r : G} (hr : r ∈ Rsub t Q A)
    (hrm : ∀ x ∈ A, dl r x ∈ pw A (2 ^ m)) {d : G} (hd : d ∈ pw A 2) :
    dl r d ^ 2 ^ (k - 1 - m) = 1 := by
  have h := dl_pw_mem hC.level.comm (hC.R_conj_memX hS hinv hr) hrm 1 (by rwa [pow_one])
  have hm' : dl r d ∈ pw A (2 ^ m) := by
    rw [pow_add, ← pw_pw hC.level.comm] at h
    exact pw_le _ _ h
  exact (hC.pi_eq_one_iffX hS hm hm').2 h

omit hC hinv in
theorem t_mem_RX [Finite G] : t ∈ Rsub t Q A :=
  mem_Rsub.2 ⟨t_mem_N1, fun _ hq => (hS.shape.commute_of_mem (hS.rad.Q_le_L hq)).symm⟩

omit hinv in
theorem At_le_RX [Finite G] : A ⊔ zpowers t ≤ Rsub t Q A := by
  refine sup_le (fun b hb => mem_Rsub.2 ⟨A_le_N1 hb, fun q hq =>
    hC.level.comm b hb q (hC.level.Q_le hq)⟩) ?_
  rw [zpowers_le]
  exact t_mem_RX hS

theorem pi_dl_AtX [Finite G] {z : G} (hz : z ∈ A ⊔ zpowers t) :
    ∃ e : ZMod 2, ∀ y ∈ A, dl z y ^ 2 ^ (k - 1 - 1) = ψ (e • coord ψ (y ^ 2 ^ (k - 1))) := by
  obtain ⟨b, hb, hzb | hzb⟩ := hC.mem_AtX hS hz
  · refine ⟨0, fun y hy => ?_⟩
    rw [hzb, (dl_At hinv hC.level.comm hb hy).1, one_pow, zero_smul, hS.rad.ψ_zero]
  · refine ⟨1, fun y hy => ?_⟩
    have hk := hC.two_le
    have hq := hC.level.pow_mem_Q hC.k_pos hy
    rw [hzb, (dl_At hinv hC.level.comm hb hy).2, one_smul, hS.rad.ψ_coord hq]
    have e1 : y⁻¹ * y⁻¹ = (y ^ 2)⁻¹ := by rw [sq, _root_.mul_inv_rev]
    rw [e1, inv_pow, ← pow_mul, ← pow_succ', show k - 1 - 1 + 1 = k - 1 by omega]
    exact inv_eq_of_mul_eq_one_right (hS.rad.Q_mul_self hq)

theorem cOf_inv_RX [Finite G] {r : G} (hr : r ∈ Rsub t Q A) : cOf ψ t k r⁻¹ = cOf ψ t k r := by
  have h := hC.cOf_mul_RX hS hinv (inv_mem hr) hr
  rw [inv_mul_cancel, cOf_oneX hS] at h
  have := congrArg (· + cOf ψ t k r) h
  simp only [zero_add, add_assoc, v6_add_self, add_zero] at this
  exact this.symm

theorem decomp_RX [Finite G] {r s : G} (hr : r ∈ Rsub t Q A) (hs : s ∈ Rsub t Q A)
    (h : cOf ψ t k r = cOf ψ t k s) : ∃ z ∈ A ⊔ zpowers t, r = s * z := by
  refine ⟨s⁻¹ * r, hC.mem_At_of_cOfX hS hinv (mul_mem (inv_mem hs) hr) ?_, by group⟩
  rw [hC.cOf_mul_RX hS hinv (inv_mem hs) hr, hC.cOf_inv_RX hS hinv hs, h, v6_add_self]

omit hinv in
theorem conj_mem_RX [Finite G] {x : G} (hx : x ∈ P ⊔ zpowers x₀) {r : G}
    (hr : r ∈ Rsub t Q A) : x * r * x⁻¹ ∈ Rsub t Q A := by
  have hxN := hC.K_le_N1X hS hx
  refine mem_Rsub.2 ⟨mul_mem (mul_mem hxN (mem_Rsub.1 hr).1) (inv_mem hxN), fun q hq => ?_⟩
  have hxQ := hS.K_le_normalizer_Q hx
  have hq' : x⁻¹ * q * x ∈ Q := by
    have := (mem_normalizer_iff.1 (inv_mem hxQ) q).1 hq
    rwa [inv_inv] at this
  have h1 := (mem_Rsub.1 hr).2 _ hq'
  calc x * r * x⁻¹ * q = x * (r * (x⁻¹ * q * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * q * x) * r) * x⁻¹ := by rw [h1]
    _ = q * (x * r * x⁻¹) := by group

theorem cOf_conj_PX [Finite G] {x : G} (hx : x ∈ P) {r : G} (hr : r ∈ Rsub t Q A) :
    cOf ψ t k (x * r * x⁻¹) = lin ψ x (cOf ψ t k r) := by
  have hxN := hC.P_le_N1X hS hx
  have hrN := (mem_Rsub.1 hr).1
  rw [hC.cOf_mulX hS hinv (mul_mem hxN hrN) (inv_mem hxN), hC.cOf_mulX hS hinv hxN hrN,
    cOf_eq_zero_of_commuteX hS (hS.commute_of_mem_P hx),
    cOf_eq_zero_of_commuteX hS (hS.commute_of_mem_P (inv_mem hx)), zero_add,
    hS.rad.lin_mul (hS.rad.P_le_normalizer hx) (hC.normalizes_QX hS hinv hrN)]
  have h0 : ∀ g ∈ normalizer (Q : Set G), lin ψ g 0 = 0 := fun g hg => by
    rw [hS.rad.lin_eq_iff hg, hS.rad.ψ_zero]; group
  rw [h0 r (hC.normalizes_QX hS hinv hrN), h0 x (hS.rad.P_le_normalizer hx), add_zero]

theorem layer_oneX [Finite G] (hM4 : HomEndModZero ε)
    (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) {r : G} (hr : r ∈ Rsub t Q A) :
    (∀ x ∈ A, dl r x ∈ pw A (2 ^ 2)) ∨ (∀ x ∈ A, dl (r * t) x ∈ pw A (2 ^ 2)) := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  have hk : 1 + 1 ≤ k := hC.two_le
  choose sR hsR hsc using htr
  have hα : ∀ v : V6, ∃ x ∈ A, x ^ 2 ^ (k - 1) = ψ v := fun v =>
    hC.level.exists_pow_eq hQ hQ2 hC.k_pos (hS.rad.ψ_mem v)
  choose α hαA hαp using hα
  have hR1 : ∀ r ∈ Rsub t Q A, ∀ x ∈ A, dl r x ∈ pw A (2 ^ 1) := fun r hr x hx => by
    rw [pow_one]; exact hC.dl_mem_pwX hS hinv hr hx
  have hdec : ∀ x ∈ A, ∃ d ∈ pw A 2, x = α (coord ψ (x ^ 2 ^ (k - 1))) * d := by
    intro x hx
    set v := coord ψ (x ^ 2 ^ (k - 1))
    refine ⟨(α v)⁻¹ * x, ?_, by group⟩
    refine (hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos (mul_mem (inv_mem (hαA v)) hx)).1 ?_
    rw [Commute.mul_pow (hC.level.comm _ (inv_mem (hαA v)) _ hx), inv_pow, hαp,
      hS.rad.ψ_coord (hC.level.pow_mem_Q hC.k_pos hx), inv_mul_cancel]
  have hmod : ∀ r ∈ Rsub t Q A, ∀ x ∈ A, dl r x ^ 2 ^ (k - 1 - 1) =
      dl r (α (coord ψ (x ^ 2 ^ (k - 1)))) ^ 2 ^ (k - 1 - 1) := by
    intro r hr x hx
    obtain ⟨d, hd, hxd⟩ := hdec x hx
    conv_lhs => rw [hxd]
    rw [hC.pi_dl_mul_rightX hS hinv hr (hR1 r hr) (hαA _) (pw_le A 2 hd),
      hC.pi_dl_pwX hS hinv hk hr (hR1 r hr) hd, mul_one]
  set F : V6 → V6 → V6 := fun u v => coord ψ (dl (sR u) (α v) ^ 2 ^ (k - 1 - 1))
  have hFψ : ∀ u v, ψ (F u v) = dl (sR u) (α v) ^ 2 ^ (k - 1 - 1) := fun u v =>
    hS.rad.ψ_coord (hC.pi_mem_QX hS hk (hR1 _ (hsR u) _ (hαA v)))
  have hcoordα : ∀ v, coord ψ (α v ^ 2 ^ (k - 1)) = v := fun v => by
    rw [hαp, hS.rad.coord_ψ]
  have hRAt := hC.At_le_RX hS
  have ha : ∀ u v v', F u (v + v') = F u v + F u v' := by
    intro u v v'
    apply hS.rad.ψ_inj
    rw [hFψ, hS.rad.ψ_add, hFψ, hFψ]
    have hc : coord ψ ((α v * α v') ^ 2 ^ (k - 1)) = v + v' := by
      rw [Commute.mul_pow (hC.level.comm _ (hαA v) _ (hαA v')), hαp, hαp, ← hS.rad.ψ_add,
        hS.rad.coord_ψ]
    have h1 := hmod (sR u) (hsR u) _ (mul_mem (hαA v) (hαA v'))
    rw [hc] at h1
    rw [← h1, hC.pi_dl_mul_rightX hS hinv (hsR u) (hR1 _ (hsR u)) (hαA v) (hαA v')]
  have hb : ∀ u u', ∃ e : ZMod 2, ∀ v, F (u + u') v = F u v + F u' v + e • v := by
    intro u u'
    have hss := mul_mem (hsR u) (hsR u')
    obtain ⟨z, hz, hzeq⟩ := hC.decomp_RX hS hinv (hsR (u + u')) hss (by
      rw [hsc, hC.cOf_mul_RX hS hinv (hsR u) (hsR u'), hsc, hsc])
    obtain ⟨e, he⟩ := hC.pi_dl_AtX hS hinv hz
    refine ⟨e, fun v => ?_⟩
    apply hS.rad.ψ_inj
    rw [hFψ, hS.rad.ψ_add, hS.rad.ψ_add, hFψ, hFψ, hzeq,
      hC.pi_dl_mul_leftX hS hinv hk hss (hR1 _ hss) (hR1 z (hRAt hz)) (hαA v),
      hC.pi_dl_mul_leftX hS hinv hk (hsR u) (hR1 _ (hsR u)) (hR1 _ (hsR u')) (hαA v),
      he _ (hαA v), hcoordα]
  have hc : ∀ i : Fin 6, ∀ u, ∃ e : ZMod 2, ∀ v,
      F (genMat ε i *ᵥ u) (genMat ε i *ᵥ v) = genMat ε i *ᵥ F u v + e • (genMat ε i *ᵥ v) := by
    intro i u
    have hx := hS.rad.p_mem i
    have hxr := hC.conj_mem_RX hS (mem_sup_left hx) (hsR u)
    obtain ⟨z, hz, hzeq⟩ := hC.decomp_RX hS hinv (hsR (genMat ε i *ᵥ u)) hxr (by
      rw [hsc, hC.cOf_conj_PX hS hinv hx (hsR u), hsc, hS.rad.lin_p])
    obtain ⟨e, he⟩ := hC.pi_dl_AtX hS hinv hz
    refine ⟨e, fun v => ?_⟩
    have hxα := hC.P_norm _ (mem_sup_left hx) _ (hαA v)
    have hcv : coord ψ ((p i * α v * (p i)⁻¹) ^ 2 ^ (k - 1)) = genMat ε i *ᵥ v := by
      rw [conj_pow, hαp, hS.rad.p_act, hS.rad.coord_ψ]
    apply hS.rad.ψ_inj
    rw [hFψ, hS.rad.ψ_add, ← hS.rad.p_act, hFψ, hzeq]
    have h1 := hmod _ (mul_mem hxr (hRAt hz)) _ hxα
    rw [hcv] at h1
    rw [← h1, hC.pi_dl_mul_leftX hS hinv hk hxr (hR1 _ hxr) (hR1 z (hRAt hz)) hxα,
      dl_conj_conj, conj_pow, he _ hxα, hcv]
  have hF := hM4 F ha hb hc
  obtain ⟨z, hz, hzeq⟩ := hC.decomp_RX hS hinv hr (hsR (cOf ψ t k r)) (hsc _).symm
  obtain ⟨ez, hez⟩ := hC.pi_dl_AtX hS hinv hz
  obtain ⟨eu, heu⟩ := hF (cOf ψ t k r)
  have hval : ∀ x ∈ A, dl r x ^ 2 ^ (k - 1 - 1) =
      ψ ((eu + ez) • coord ψ (x ^ 2 ^ (k - 1))) := by
    intro x hx
    rw [hmod r hr x hx, hzeq, hC.pi_dl_mul_leftX hS hinv hk (hsR _) (hR1 _ (hsR _))
      (hR1 z (hRAt hz)) (hαA _), ← hFψ, heu, hez _ (hαA _), hcoordα, ← hS.rad.ψ_add, add_smul]
  have ht1 : ∀ x ∈ A, dl t x ^ 2 ^ (k - 1 - 1) = ψ (coord ψ (x ^ 2 ^ (k - 1))) := by
    intro x hx
    have h := (hC.pi_dl_AtX hS hinv (mem_sup_right (mem_zpowers t) : t ∈ A ⊔ zpowers t))
    have hq := hC.level.pow_mem_Q hC.k_pos hx
    have e1 : dl t x = x⁻¹ * x⁻¹ := by
      have := (dl_At hinv hC.level.comm (one_mem A) hx).2
      rwa [one_mul] at this
    rw [e1, hS.rad.ψ_coord hq]
    have e2 : x⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by rw [sq, _root_.mul_inv_rev]
    rw [e2, inv_pow, ← pow_mul, ← pow_succ', show k - 1 - 1 + 1 = k - 1 by omega]
    exact inv_eq_of_mul_eq_one_right (hS.rad.Q_mul_self hq)
  have hE : eu + ez = 0 ∨ eu + ez = 1 := by
    generalize eu + ez = E
    fin_cases E
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hE with hE | hE
  · left
    intro x hx
    have := hval x hx
    rw [hE, zero_smul, hS.rad.ψ_zero] at this
    have h := (hC.pi_eq_one_iffX hS hk (hR1 r hr x hx)).1 this
    simpa using h
  · right
    intro x hx
    have h1 := hval x hx
    rw [hE, one_smul] at h1
    have h2 : dl (r * t) x ^ 2 ^ (k - 1 - 1) = 1 := by
      rw [hC.pi_dl_mul_leftX hS hinv hk hr (hR1 r hr) (hR1 t (t_mem_RX hS)) hx, h1,
        ht1 x hx, hS.rad.ψ_mul_self]
    have h := (hC.pi_eq_one_iffX hS hk (hR1 _ (mul_mem hr (t_mem_RX hS)) x hx)).1 h2
    simpa using h

theorem not_dl_mul_tX [Finite G] {b : G} (hb : b ∈ A) :
    ¬ ∀ x ∈ A, dl (b * t) x ∈ pw A (2 ^ 2) := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  intro h
  obtain ⟨x, hx, hxπ⟩ := hC.level.exists_pow_eq hQ hQ2 hC.k_pos
    (hS.rad.ψ_mem (Pi.single 0 1))
  have hne : x ^ 2 ^ (k - 1) ≠ 1 := by
    rw [hxπ, ← hS.rad.ψ_zero]
    intro h0
    have := congrFun (hS.rad.ψ_inj h0) 0
    simp at this
  have h1 := h x hx
  rw [(dl_At hinv hC.level.comm hb hx).2] at h1
  obtain ⟨y, hy, hy4⟩ := (mem_pw hC.level.comm).1 h1
  have hy2 : (x * y ^ 2) * (x * y ^ 2) = 1 := by
    have hc := hC.level.comm x hx _ (pow_mem hy 2)
    have e : (x * y ^ 2) * (x * y ^ 2) = x * x * y ^ 4 := by
      rw [show x * y ^ 2 * (x * y ^ 2) = x * (y ^ 2 * x) * y ^ 2 by group, ← hc,
        show (4 : ℕ) = 2 + 2 by rfl, pow_add]
      group
    rw [e, show 2 ^ 2 = 4 by rfl] at *
    rw [hy4]
    group
  have hq := hC.level.mem_Q _ (mul_mem hx (pow_mem hy 2)) hy2
  apply hne
  have hk := hC.two_le
  have h2 : (x * y ^ 2) ^ 2 ^ (k - 1) = 1 := by
    rw [show 2 ^ (k - 1) = 2 * 2 ^ (k - 2) by
      rw [← pow_succ']; congr 1; omega, pow_mul, sq, hQ2 _ hq, one_pow]
  rw [Commute.mul_pow (hC.level.comm _ hx _ (pow_mem hy 2)), ← pow_mul, ← pow_succ',
    show k - 1 + 1 = k by omega, hC.level.pow_eq_one y hy, mul_one] at h2
  exact h2

theorem layer_highX [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) :
    ∀ m, 2 ≤ m → m ≤ k → ∀ r ∈ Rsub t Q A, (∀ x ∈ A, dl r x ∈ pw A (2 ^ 2)) →
      ∀ x ∈ A, dl r x ∈ pw A (2 ^ m) := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  have hR1 : ∀ r ∈ Rsub t Q A, ∀ x ∈ A, dl r x ∈ pw A (2 ^ 1) := fun r hr x hx => by
    rw [pow_one]; exact hC.dl_mem_pwX hS hinv hr hx
  have hRAt := hC.At_le_RX hS
  have hs₂ : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v ∧ ∀ x ∈ A, dl g x ∈ pw A (2 ^ 2) := by
    intro v
    obtain ⟨g, hg, hgv⟩ := htr v
    rcases hC.layer_oneX hS hinv hM4 htr hg with h | h
    · exact ⟨g, hg, hgv, h⟩
    · refine ⟨g * t, mul_mem hg (t_mem_RX hS), ?_, h⟩
      rw [hC.cOf_mul_RX hS hinv hg (t_mem_RX hS), cOf_eq_zero_of_commuteX hS rfl, add_zero, hgv]
  choose s₂ hs₂R hs₂c hs₂2 using hs₂
  have hα : ∀ v : V6, ∃ x ∈ A, x ^ 2 ^ (k - 1) = ψ v := fun v =>
    hC.level.exists_pow_eq hQ hQ2 hC.k_pos (hS.rad.ψ_mem v)
  choose α hαA hαp using hα
  have hz2 : ∀ z ∈ A ⊔ zpowers t, (∀ x ∈ A, dl z x ∈ pw A (2 ^ 2)) → ∀ x ∈ A, dl z x = 1 := by
    intro z hz hz2 x hx
    obtain ⟨b, hb, hzb | hzb⟩ := hC.mem_AtX hS hz
    · rw [hzb]; exact (dl_At hinv hC.level.comm hb hx).1
    · exact absurd (hzb ▸ hz2) (hC.not_dl_mul_tX hS hinv hb)
  intro m hm2
  induction m, hm2 using Nat.le_induction with
  | base => intro _ r _ h; exact h
  | succ m hm2 ih =>
    intro hmk r hr hr2
    have hm : m + 1 ≤ k := hmk
    have ih' := ih (by omega)
    have hR2 : ∀ g ∈ Rsub t Q A, (∀ x ∈ A, dl g x ∈ pw A (2 ^ 2)) →
        ∀ x ∈ A, dl g x ∈ pw A (2 ^ m) := ih'
    have hR2mul : ∀ g ∈ Rsub t Q A, ∀ g' ∈ Rsub t Q A, (∀ x ∈ A, dl g x ∈ pw A (2 ^ 2)) →
        (∀ x ∈ A, dl g' x ∈ pw A (2 ^ 2)) → ∀ x ∈ A, dl (g⁻¹ * g') x ∈ pw A (2 ^ 2) := by
      intro g hg g' hg' h1 h2
      have hgi : ∀ x ∈ A, g⁻¹ * x * g⁻¹⁻¹ ∈ A := hC.R_conj_memX hS hinv (inv_mem hg)
      exact hC.dl_mul_mem hgi (hC.dl_inv_mem hgi h1) h2
    have hdecR2 : ∀ g ∈ Rsub t Q A, ∀ g' ∈ Rsub t Q A, (∀ x ∈ A, dl g x ∈ pw A (2 ^ 2)) →
        (∀ x ∈ A, dl g' x ∈ pw A (2 ^ 2)) → cOf ψ t k g = cOf ψ t k g' →
        ∃ z ∈ A ⊔ zpowers t, g = g' * z ∧ ∀ x ∈ A, dl z x = 1 := by
      intro g hg g' hg' h1 h2 hc
      obtain ⟨z, hz, hzeq⟩ := hC.decomp_RX hS hinv hg hg' hc
      refine ⟨z, hz, hzeq, hz2 z hz ?_⟩
      have : z = g'⁻¹ * g := by rw [hzeq]; group
      rw [this]
      exact hR2mul g' hg' g hg h2 h1
    have hdlz : ∀ z : G, (∀ x ∈ A, dl z x = 1) → ∀ x ∈ A, dl z x ∈ pw A (2 ^ m) :=
      fun z hz x hx => by rw [hz x hx]; exact one_mem _
    have hR2conj : ∀ i : Fin 6, ∀ g ∈ Rsub t Q A, (∀ x ∈ A, dl g x ∈ pw A (2 ^ 2)) →
        ∀ x ∈ A, dl (p i * g * (p i)⁻¹) x ∈ pw A (2 ^ 2) := by
      intro i g hg h x hx
      have hpi := hS.rad.p_mem i
      have hx' : (p i)⁻¹ * x * (p i)⁻¹⁻¹ ∈ A := hC.P_norm _ (inv_mem (mem_sup_left hpi)) x hx
      have e := dl_conj_conj (p i) g ((p i)⁻¹ * x * (p i)⁻¹⁻¹)
      rw [show p i * ((p i)⁻¹ * x * (p i)⁻¹⁻¹) * (p i)⁻¹ = x by group] at e
      rw [e]
      exact pw_conj_mem_gen hC.level.comm (hC.P_norm _ (mem_sup_left hpi)) (h _ hx')
    have hmod : ∀ g ∈ Rsub t Q A, (∀ x ∈ A, dl g x ∈ pw A (2 ^ m)) → ∀ x ∈ A,
        dl g x ^ 2 ^ (k - 1 - m) = dl g (α (coord ψ (x ^ 2 ^ (k - 1)))) ^ 2 ^ (k - 1 - m) := by
      intro g hg hgm x hx
      set v := coord ψ (x ^ 2 ^ (k - 1))
      have hd : (α v)⁻¹ * x ∈ pw A 2 := by
        refine (hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos (mul_mem (inv_mem (hαA v)) hx)).1 ?_
        rw [Commute.mul_pow (hC.level.comm _ (inv_mem (hαA v)) _ hx), inv_pow, hαp,
          hS.rad.ψ_coord (hC.level.pow_mem_Q hC.k_pos hx), inv_mul_cancel]
      have hxd : x = α v * ((α v)⁻¹ * x) := by group
      conv_lhs => rw [hxd]
      rw [hC.pi_dl_mul_rightX hS hinv hg hgm (hαA _) (pw_le A 2 hd),
        hC.pi_dl_pwX hS hinv hm hg hgm hd, mul_one]
    set F : V6 → V6 → V6 := fun u v => coord ψ (dl (s₂ u) (α v) ^ 2 ^ (k - 1 - m))
    have hs₂m : ∀ u, ∀ x ∈ A, dl (s₂ u) x ∈ pw A (2 ^ m) := fun u => hR2 _ (hs₂R u) (hs₂2 u)
    have hFψ : ∀ u v, ψ (F u v) = dl (s₂ u) (α v) ^ 2 ^ (k - 1 - m) := fun u v =>
      hS.rad.ψ_coord (hC.pi_mem_QX hS hm (hs₂m u _ (hαA v)))
    have ha : ∀ u v v', F u (v + v') = F u v + F u v' := by
      intro u v v'
      apply hS.rad.ψ_inj
      rw [hFψ, hS.rad.ψ_add, hFψ, hFψ]
      have hc : coord ψ ((α v * α v') ^ 2 ^ (k - 1)) = v + v' := by
        rw [Commute.mul_pow (hC.level.comm _ (hαA v) _ (hαA v')), hαp, hαp, ← hS.rad.ψ_add,
          hS.rad.coord_ψ]
      have h1 := hmod (s₂ u) (hs₂R u) (hs₂m u) _ (mul_mem (hαA v) (hαA v'))
      rw [hc] at h1
      rw [← h1, hC.pi_dl_mul_rightX hS hinv (hs₂R u) (hs₂m u) (hαA v) (hαA v')]
    have hb : ∀ u u' v, F (u + u') v = F u v + F u' v := by
      intro u u' v
      have hss := mul_mem (hs₂R u) (hs₂R u')
      have hss2 : ∀ x ∈ A, dl (s₂ u * s₂ u') x ∈ pw A (2 ^ 2) :=
        hC.dl_mul_mem (hC.R_conj_memX hS hinv (hs₂R u)) (hs₂2 u) (hs₂2 u')
      obtain ⟨z, -, hzeq, hz1⟩ := hdecR2 _ (hs₂R (u + u')) _ hss (hs₂2 _) hss2 (by
        rw [hs₂c, hC.cOf_mul_RX hS hinv (hs₂R u) (hs₂R u'), hs₂c, hs₂c])
      apply hS.rad.ψ_inj
      rw [hFψ, hS.rad.ψ_add, hFψ, hFψ, hzeq,
        hC.pi_dl_mul_leftX hS hinv hm hss (hR2 _ hss hss2) (hdlz z hz1) (hαA v), hz1 _ (hαA v),
        one_pow, mul_one, hC.pi_dl_mul_leftX hS hinv hm (hs₂R u) (hs₂m u) (hs₂m u') (hαA v)]
    have hc : ∀ i : Fin 6, ∀ u v,
        F (genMat ε i *ᵥ u) (genMat ε i *ᵥ v) = genMat ε i *ᵥ F u v := by
      intro i u v
      have hx := hS.rad.p_mem i
      have hxr := hC.conj_mem_RX hS (mem_sup_left hx) (hs₂R u)
      have hxr2 := hR2conj i _ (hs₂R u) (hs₂2 u)
      obtain ⟨z, -, hzeq, hz1⟩ := hdecR2 _ (hs₂R (genMat ε i *ᵥ u)) _ hxr (hs₂2 _) hxr2 (by
        rw [hs₂c, hC.cOf_conj_PX hS hinv hx (hs₂R u), hs₂c, hS.rad.lin_p])
      have hxα := hC.P_norm _ (mem_sup_left hx) _ (hαA v)
      have hcv : coord ψ ((p i * α v * (p i)⁻¹) ^ 2 ^ (k - 1)) = genMat ε i *ᵥ v := by
        rw [conj_pow, hαp, hS.rad.p_act, hS.rad.coord_ψ]
      apply hS.rad.ψ_inj
      rw [hFψ, ← hS.rad.p_act, hFψ, hzeq]
      have hm2 : ∀ x ∈ A, dl (p i * s₂ u * (p i)⁻¹ * z) x ∈ pw A (2 ^ m) :=
        hC.dl_mul_mem (hC.R_conj_memX hS hinv hxr) (hR2 _ hxr hxr2) (hdlz z hz1)
      have hmemR : p i * s₂ u * (p i)⁻¹ * z ∈ Rsub t Q A := by rw [← hzeq]; exact hs₂R _
      have h1 := hmod _ hmemR hm2 _ hxα
      rw [hcv] at h1
      rw [← h1, hC.pi_dl_mul_leftX hS hinv hm hxr (hR2 _ hxr hxr2) (hdlz z hz1) hxα,
        hz1 _ hxα, one_pow, mul_one, dl_conj_conj, conj_pow]
    have hF := hM3 F hb ha hc
    intro x hx
    obtain ⟨z, -, hzeq, hz1⟩ := hdecR2 r hr _ (hs₂R (cOf ψ t k r)) hr2 (hs₂2 _) (hs₂c _).symm
    refine (hC.pi_eq_one_iffX hS hm (hR2 r hr hr2 x hx)).1 ?_
    rw [hmod r hr (hR2 r hr hr2) x hx, hzeq,
      hC.pi_dl_mul_leftX hS hinv hm (hs₂R _) (hs₂m _) (hdlz z hz1) (hαA _), hz1 _ (hαA _),
      one_pow, mul_one, ← hFψ, hF, hS.rad.ψ_zero]

theorem R_centralizesX [Finite G] (hM3 : HomEndZero ε)
    (hM4 : HomEndModZero ε) (htr : ∀ v : V6, ∃ g ∈ Rsub t Q A, cOf ψ t k g = v) {r : G}
    (hr : r ∈ Rsub t Q A) :
    (∀ x ∈ A, r * x = x * r) ∨ (∀ x ∈ A, r * t * x = x * (r * t)) := by
  have hk := hC.two_le
  have conv : ∀ g, (∀ x ∈ A, dl g x ∈ pw A (2 ^ k)) → ∀ x ∈ A, g * x = x * g := by
    intro g h x hx
    have h1 := h x hx
    rw [hC.level.pw_eq_bot, mem_bot] at h1
    simp only [dl] at h1
    have h2 : g * x * g⁻¹ = x := by rw [← mul_inv_eq_one]; exact h1
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h2]
  rcases hC.layer_oneX hS hinv hM4 htr hr with h | h
  · exact Or.inl (conv r (hC.layer_highX hS hinv hM3 hM4 htr k hk le_rfl r hr h))
  · exact Or.inr (conv (r * t) (hC.layer_highX hS hinv hM3 hM4 htr k hk le_rfl (r * t)
      (mul_mem hr (t_mem_RX hS)) h))

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
