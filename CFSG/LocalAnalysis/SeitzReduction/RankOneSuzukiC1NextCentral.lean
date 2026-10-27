module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextUOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1

theorem sq_chi_eq_one {G : Type*} [Group G] {W : Subgroup G}
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {m : ℕ} (hexp : ∀ w ∈ W, w ^ 2 ^ m = 1) {x : G}
    (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hx2 : ∀ w ∈ W, x * (x * w * x⁻¹) * x⁻¹ = w)
    (h4 : ∀ w ∈ W, ∃ s ∈ W, w⁻¹ * (x * w * x⁻¹) = s ^ 4) :
    ∀ w ∈ W, (w⁻¹ * (x * w * x⁻¹)) ^ 2 = 1 := by
  have hχW : ∀ w ∈ W, w⁻¹ * (x * w * x⁻¹) ∈ W := fun w hw => mul_mem (inv_mem hw) (hxW w hw)
  have hmul : ∀ w ∈ W, ∀ w' ∈ W, (w * w')⁻¹ * (x * (w * w') * x⁻¹) =
      (w⁻¹ * (x * w * x⁻¹)) * (w'⁻¹ * (x * w' * x⁻¹)) := by
    intro w hw w' hw'
    have e1 : w'⁻¹ * (w⁻¹ * (x * w * x⁻¹)) = (w⁻¹ * (x * w * x⁻¹)) * w'⁻¹ :=
      hcomm _ (inv_mem hw') _ (hχW w hw)
    calc (w * w')⁻¹ * (x * (w * w') * x⁻¹) = w'⁻¹ * (w⁻¹ * (x * w * x⁻¹)) * (x * w' * x⁻¹) := by
          group
      _ = (w⁻¹ * (x * w * x⁻¹)) * w'⁻¹ * (x * w' * x⁻¹) := by rw [e1]
      _ = _ := by group
  have hpow : ∀ w ∈ W, ∀ n : ℕ, (w ^ n)⁻¹ * (x * w ^ n * x⁻¹) = (w⁻¹ * (x * w * x⁻¹)) ^ n := by
    intro w hw n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, hmul _ (pow_mem hw n) _ hw, ih, pow_succ]
  have hχχ : ∀ w ∈ W, (w⁻¹ * (x * w * x⁻¹)) ^ 2 *
      ((w⁻¹ * (x * w * x⁻¹))⁻¹ * (x * (w⁻¹ * (x * w * x⁻¹)) * x⁻¹)) = 1 := by
    intro w hw
    set c := w⁻¹ * (x * w * x⁻¹) with hc
    have hcW := hχW w hw
    have e1 : x * w * x⁻¹ = w * c := by rw [hc]; group
    have e2 : x * (x * w * x⁻¹) * x⁻¹ = w * c * (c * (c⁻¹ * (x * c * x⁻¹))) := by
      rw [e1, show x * (w * c) * x⁻¹ = (x * w * x⁻¹) * (x * c * x⁻¹) by group, e1]
      group
    have e3 := (hx2 w hw).symm.trans e2
    have e4 : c * (c * (c⁻¹ * (x * c * x⁻¹))) = 1 := by
      have := congrArg (fun z => w⁻¹ * z) e3
      simp only [inv_mul_cancel] at this
      rw [this]
      group
    rw [sq, ← e4]
    group
  have step : ∀ j : ℕ, (∀ w ∈ W, (w⁻¹ * (x * w * x⁻¹)) ^ (2 * 2 ^ (j + 1)) = 1) →
      ∀ w ∈ W, (w⁻¹ * (x * w * x⁻¹)) ^ (2 * 2 ^ j) = 1 := by
    intro j hj w hw
    obtain ⟨s, hs, hs4⟩ := h4 w hw
    have e1 := hχχ w hw
    rw [hs4, hpow s hs 4] at e1
    rw [← hs4] at e1
    have e2 : (w⁻¹ * (x * w * x⁻¹)) ^ 2 = ((s⁻¹ * (x * s * x⁻¹)) ^ 4)⁻¹ :=
      eq_inv_of_mul_eq_one_left e1
    rw [pow_mul, e2, inv_pow, ← pow_mul, show 4 * 2 ^ j = 2 * 2 ^ (j + 1) by ring, hj s hs,
      inv_one]
  have hall : ∀ i : ℕ, ∀ w ∈ W, (w⁻¹ * (x * w * x⁻¹)) ^ (2 * 2 ^ (m - i)) = 1 := by
    intro i
    induction i with
    | zero =>
      intro w hw
      rw [Nat.sub_zero, mul_comm, pow_mul, hexp _ (hχW w hw), one_pow]
    | succ i ih =>
      by_cases hi : i < m
      · have e : m - i = (m - (i + 1)) + 1 := by omega
        rw [e] at ih
        exact step _ ih
      · have e : m - (i + 1) = m - i := by omega
        rw [e]
        exact ih
  intro w hw
  have := hall m w hw
  rwa [Nat.sub_self, pow_zero, mul_one] at this

theorem chi_sq_mul_chi_chi {G : Type*} [Group G] {x w : G}
    (hx2 : x * (x * w * x⁻¹) * x⁻¹ = w) :
    (w⁻¹ * (x * w * x⁻¹)) ^ 2 *
      ((w⁻¹ * (x * w * x⁻¹))⁻¹ * (x * (w⁻¹ * (x * w * x⁻¹)) * x⁻¹)) = 1 := by
  have e : (w⁻¹ * (x * w * x⁻¹)) ^ 2 *
      ((w⁻¹ * (x * w * x⁻¹))⁻¹ * (x * (w⁻¹ * (x * w * x⁻¹)) * x⁻¹)) =
        w⁻¹ * (x * (x * w * x⁻¹) * x⁻¹) := by rw [sq]; group
  rw [e, hx2, inv_mul_cancel]

theorem eq_zero_of_idem {K : Type*} [Field K] [Fintype K] {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    (hf : 2 ≤ f) {C : K}
    (h : ∀ b : K, C * (C * b ^ 2 ^ (f - 1)) ^ 2 ^ (f - 1) = C * b ^ 2 ^ (f - 1)) : C = 0 := by
  classical
  have hq : ∀ c : K, c ^ 2 ^ f = c := fun c => by rw [← hK]; exact FiniteField.pow_card c
  have hsq : ∀ c : K, (c ^ 2 ^ (f - 1)) ^ 2 = c := fun c => by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ f), hq]
  by_contra hC
  have h1 := h 1
  rw [one_pow, mul_one] at h1
  have hC1 : C ^ 2 ^ (f - 1) = 1 := by
    have := mul_left_cancel₀ hC (h1.trans (mul_one C).symm)
    exact this
  have hC' : C = 1 := by rw [← hsq C, hC1, one_pow]
  subst hC'
  have hall : ∀ c : K, c ^ 2 = c := by
    intro c
    have e := h (c ^ 2)
    simp only [one_mul] at e
    have hsq' : (c ^ 2) ^ 2 ^ (f - 1) = c := by rw [← pow_mul, mul_comm, pow_mul, hsq]
    rw [hsq'] at e
    calc c ^ 2 = (c ^ 2 ^ (f - 1)) ^ 2 := by rw [e]
      _ = c := hsq c
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun c _ => by
    have e := hall c
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq, e, sub_self]
    rcases mul_eq_zero.mp this with h0 | h0
    · simp [h0]
    · simp [sub_eq_zero.mp h0]
  have h4 := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, hK] at h4
  have h5 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

end SzC1

namespace SzC1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {u v : G → K} {κ : K} (H : SzC1Next G L f a t T d V U U₁ k K u v κ)

section NoE

include H

theorem exists_sq_of_pow_eq_one {r : G} (hr : r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (h1 : r ^ 2 ^ (k + 1) = 1) : ∃ s ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), r = s ^ 2 := by
  obtain ⟨-, hcomm, hcard, hΩ, hpow, -, -, -⟩ := H.stage.nextConf H.mu H.lam H.nu
  exact SzC1.exists_sq_eq_of_pow_eq_one hcomm hΩ hpow
    (by rw [H.stage.card_szA₁ H.card_K H.coords, hcard]) hr h1

theorem exists_sq_of_mem_V {r : G} (hr : r ∈ V) :
    ∃ s ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), r = s ^ 2 :=
  H.exists_sq_of_pow_eq_one (H.V_le_V₁ hr) (H.stage.pow r hr)

theorem X_conj_d {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((d⁻¹ * w * d) ^ 2 ^ (k + 1)) = κ ^ (2 ^ (a + 1) + 1) * v (w ^ 2 ^ (k + 1)) := by
  rw [show d⁻¹ * w * d = d⁻¹ * w * d⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv,
    H.coords.v_conj_szA₁ H.stage.ha H.card_K' (H.stage.pow_mem_szA₁_V₁ H.card_K H.coords hw)]

end NoE

variable
  {E : Subgroup (Equiv.Perm K)} (hE : H.RegData E)
include H hE

theorem chi_mul_right_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    (w * w')⁻¹ * (x * (w * w') * x⁻¹) = (w⁻¹ * (x * w * x⁻¹)) * (w'⁻¹ * (x * w' * x⁻¹)) := by
  have hcx := H.V_le_V₁ (H.chi_mem_V_of_mem_nextU hE hx hw)
  have e1 : w'⁻¹ * (w⁻¹ * (x * w * x⁻¹)) = (w⁻¹ * (x * w * x⁻¹)) * w'⁻¹ :=
    H.V₁_comm (inv_mem hw') hcx
  calc (w * w')⁻¹ * (x * (w * w') * x⁻¹) = w'⁻¹ * (w⁻¹ * (x * w * x⁻¹)) * (x * w' * x⁻¹) := by
        group
    _ = (w⁻¹ * (x * w * x⁻¹)) * w'⁻¹ * (x * w' * x⁻¹) := by rw [e1]
    _ = _ := by group

theorem M_mul_right {x : G} (hx : x ∈ H.nextU E) {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v (((w * w')⁻¹ * (x * (w * w') * x⁻¹)) ^ 2 ^ k) =
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) + v ((w'⁻¹ * (x * w' * x⁻¹)) ^ 2 ^ k) := by
  have hc := H.chi_mem_V_of_mem_nextU hE hx hw
  have hc' := H.chi_mem_V_of_mem_nextU hE hx hw'
  rw [H.chi_mul_right_of_mem_nextU hE hx hw hw', (Commute.mul_pow (H.stage.comm _ hc _ hc') _),
    H.coords.v_mul_szA₁ H.stage.ha H.card_K' (H.stage.pow_mem_szA₁ hc) (H.stage.pow_mem_szA₁ hc')]

theorem M_eq_zero_of_mem_V {x : G} (hx : x ∈ H.nextU E) {r : G} (hr : r ∈ V) :
    v ((r⁻¹ * (x * r * x⁻¹)) ^ 2 ^ k) = 0 := by
  obtain ⟨s, hs, rfl⟩ := H.exists_sq_of_mem_V hr
  have hcs := H.chi_mem_V_of_mem_nextU hE hx hs
  rw [sq s, H.chi_mul_right_of_mem_nextU hE hx hs hs, ← sq, ← pow_mul, ← pow_succ',
    H.stage.pow _ hcs, H.coords.v_one]

theorem M_eq_of_X_eq {x : G} (hx : x ∈ H.nextU E) {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hX : v (w ^ 2 ^ (k + 1)) = v (w' ^ 2 ^ (k + 1))) :
    v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = v ((w'⁻¹ * (x * w' * x⁻¹)) ^ 2 ^ k) := by
  have hV := (H.X_eq_iff hw hw').mp hX
  have e : w' = w * (w⁻¹ * w') := by group
  rw [e, H.M_mul_right hE hx hw (H.V_le_V₁ hV), H.M_eq_zero_of_mem_V hE hx hV, add_zero]

theorem M_conj_d {x : G} (hx : x ∈ H.nextU E) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v (((d⁻¹ * w * d)⁻¹ * ((d⁻¹ * x * d) * (d⁻¹ * w * d) * (d⁻¹ * x * d)⁻¹)) ^ 2 ^ k) =
      κ ^ (2 ^ (a + 1) + 1) * v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) := by
  rw [show (d⁻¹ * w * d)⁻¹ * ((d⁻¹ * x * d) * (d⁻¹ * w * d) * (d⁻¹ * x * d)⁻¹) =
    d⁻¹ * (w⁻¹ * (x * w * x⁻¹)) * d⁻¹⁻¹ by group, conj_pow, inv_inv,
    H.coords.v_conj_szA₁ H.stage.ha H.card_K'
      (H.stage.pow_mem_szA₁ (H.chi_mem_V_of_mem_nextU hE hx hw))]

theorem S'_mul {x y : G} (hx : x ∈ H.nextU E) (hy : y ∈ H.nextU E) :
    v ((x * y * t * (x * y)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) =
      v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) + v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) := by
  set hxN := H.nextU_le hE hx
  set hyN := H.nextU_le hE hy
  have e2 : (⟨x * y, mul_mem hxN hyN⟩ : normalizer (U : Set G)) = ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
  have e3 := H.perm_zero ⟨x * y, mul_mem hxN hyN⟩
  rw [e2, map_mul, Equiv.Perm.mul_apply, H.perm_nextU hE hx, H.perm_zero, H.perm_zero] at e3
  exact e3.symm

theorem S'_conj_d {x : G} (hx : x ∈ H.nextU E) :
    v ((d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) =
      κ ^ (2 ^ (a + 1) + 1) * v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) := by
  rw [H.stage.comm_t_conj_d x, H.X_conj_d (H.comm_t_mem_V₁ (H.nextU_le hE hx))]


theorem conj_V₁_of_mem_U₁' {U₁' : Subgroup G} (hle : U₁' ≤ H.nextU E)
    (hN : H.nextU E ≤ normalizer (U₁' : Set G)) (hsup : U₁' ⊔ zpowers t = H.nextU E)
    (hd : d ∈ normalizer (U₁' : Set G)) (hinf : U₁' ⊓ U = U₁) :
    ∀ x ∈ U₁', ∀ r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      r⁻¹ * (x * r * x⁻¹) ∈ szA₁ (szT₁ L T) := by
  have hK' := H.card_K'
  have hf : 2 ≤ f := by have := H.stage.ha; rw [H.stage.hfa]; omega
  obtain ⟨-, hV₁comm, -, -, hV₁pow, -, -, -⟩ := H.stage.nextConf H.mu H.lam H.nu
  set S' : G → K := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) with hS'
  have htU' : t ∈ H.nextU E := H.U_le_nextU hE H.stage.t_mem_U
  have hS't : S' t = 0 := by
    show v ((t * t * t⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = 0
    rw [show t * t * t⁻¹ * t⁻¹ = (1 : G) by group, one_pow, H.coords.v_one]
  have hS'mul : ∀ x ∈ U₁', ∀ y ∈ U₁', S' (x * y) = S' x + S' y := fun x hx y hy =>
    H.S'_mul hE (hle hx) (hle hy)
  have hS'surj : ∀ s : K, ∃ x ∈ U₁', S' x = s := by
    intro s
    obtain ⟨e, he, -⟩ := hE.reg 0 s
    obtain ⟨n, hn⟩ := hE.le e.2
    have hnU' : (n : G) ∈ H.nextU E := (H.mem_nextU hE).mpr ⟨n.2, by rw [hn]; exact e.2⟩
    have hS'n : S' n = s := by
      show v (((n : G) * t * (n : G)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = s
      rw [← H.perm_zero n, hn, he]
    have htN : t ∈ normalizer (U₁' : Set G) := hN htU'
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers H.stage.t_mul_self htN
      (hsup ▸ hnU') with h1 | h1
    · exact ⟨n, h1, hS'n⟩
    · refine ⟨n * t, h1, ?_⟩
      have e := H.S'_mul hE hnU' htU'
      show v (((n : G) * t * t * ((n : G) * t)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = s
      rw [e]
      show S' n + S' t = s
      rw [hS't, add_zero, hS'n]
  have hS'ker : ∀ x ∈ U₁', S' x = 0 → x ∈ U₁ := by
    intro x hx h0
    have hxU := H.mem_U_of_mem_nextU hE (hle hx) (by rw [H.perm_zero]; exact h0)
    rw [← hinf]
    exact mem_inf.mpr ⟨hx, hxU⟩
  have hU₁M : ∀ x ∈ U₁, ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = 0 := by
    intro x hx w hw
    rw [← mem_centralizer_iff.mp (H.U₁_le_centralizer_V₁ hx) w hw, mul_inv_cancel_right,
      inv_mul_cancel, one_pow, H.coords.v_one]
  obtain ⟨D, hD⟩ := exists_addMonoidHom₂_of_hom (M := U₁') (S := S')
    (Φ := fun x b => v (((H.sec b)⁻¹ * (x * H.sec b * x⁻¹)) ^ 2 ^ k)) hS'mul hS'surj
    (fun x hx y hy b => H.M_mul_of_mem_nextU hE (hle hx) (hle hy) (H.sec_mem b))
    (fun x hx b b' => by
      show v (((H.sec (b + b'))⁻¹ * (x * H.sec (b + b') * x⁻¹)) ^ 2 ^ k) =
        v (((H.sec b)⁻¹ * (x * H.sec b * x⁻¹)) ^ 2 ^ k) +
          v (((H.sec b')⁻¹ * (x * H.sec b' * x⁻¹)) ^ 2 ^ k)
      rw [H.M_eq_of_X_eq hE (hle hx) (H.sec_mem (b + b')) (mul_mem (H.sec_mem b) (H.sec_mem b'))
        (by rw [H.sec_X, H.X_mul (H.sec_mem b) (H.sec_mem b'), H.sec_X, H.sec_X]),
        H.M_mul_right hE (hle hx) (H.sec_mem b) (H.sec_mem b')])
    (fun x hx h0 b => hU₁M x (hS'ker x hx h0) _ (H.sec_mem b))
  have hM : ∀ x ∈ U₁', ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = D (S' x) (v (w ^ 2 ^ (k + 1))) := by
    intro x hx w hw
    rw [H.M_eq_of_X_eq hE (hle hx) hw (H.sec_mem _) (H.sec_X _).symm]
    exact hD x hx _
  obtain ⟨C, hC⟩ := bilinear_eq_mul_sqrt_of_equivariant H.card_K (by omega) D H.gen_mu
    fun s b => by
      obtain ⟨x, hx, rfl⟩ := hS'surj s
      have hdx : d⁻¹ * x * d ∈ U₁' := by simpa using (mem_normalizer_iff.mp (inv_mem hd) x).mp hx
      have hdw := H.stage.conj_d_mem_V₁ (H.sec_mem b)
      have e1 := hM _ hdx _ hdw
      rw [H.M_conj_d hE (hle hx) (H.sec_mem b), H.X_conj_d (H.sec_mem b), H.sec_X] at e1
      have e2 : S' (d⁻¹ * x * d) = κ ^ (2 ^ (a + 1) + 1) * S' x := H.S'_conj_d hE (hle hx)
      rw [e2] at e1
      rw [← e1, hM x hx _ (H.sec_mem b), H.sec_X]
  have hidem : ∀ x ∈ U₁', ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      D (S' x) (v (w ^ 2 ^ (k + 1))) = D (S' x) (D (S' x) (v (w ^ 2 ^ (k + 1)))) := by
    intro x hx w hw
    have hxU' := hle hx
    have hcV := H.chi_mem_V_of_mem_nextU hE hxU' hw
    obtain ⟨s, hs, hs2⟩ := H.exists_sq_of_mem_V hcV
    have hx2 : x * (x * w * x⁻¹) * x⁻¹ = w := by
      have h1 := mem_centralizer_iff.mp
        (H.U₁_le_centralizer_V₁ (H.sq_mem_U₁_of_mem_nextU hE hxU')) w hw
      calc x * (x * w * x⁻¹) * x⁻¹ = x ^ 2 * w * (x ^ 2)⁻¹ := by rw [sq]; group
        _ = w := by rw [← h1, mul_inv_cancel_right]
    have e1 := SzC1.chi_sq_mul_chi_chi hx2
    rw [hs2, sq s, H.chi_mul_right_of_mem_nextU hE hxU' hs hs, ← sq (s⁻¹ * (x * s * x⁻¹)),
      ← sq s, ← hs2] at e1
    have e2 : (w⁻¹ * (x * w * x⁻¹)) ^ 2 = ((s⁻¹ * (x * s * x⁻¹)) ^ 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left e1
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := H.stage.one_le_k H.card_K H.coords; omega⟩
    have hcs := H.chi_mem_V_of_mem_nextU hE hxU' hs
    have hMeq : v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = v ((s⁻¹ * (x * s * x⁻¹)) ^ 2 ^ k) := by
      rw [hj, pow_succ', pow_mul, e2, inv_pow, ← pow_mul, ← pow_succ',
        H.coords.v_inv_szA₁ H.stage.ha hK' (by rw [← hj]; exact H.stage.pow_mem_szA₁ hcs)]
    have hXs : v (s ^ 2 ^ (k + 1)) = v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) := by
      rw [hs2, pow_succ', pow_mul]
    calc D (S' x) (v (w ^ 2 ^ (k + 1))) = v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) := (hM x hx w hw).symm
      _ = v ((s⁻¹ * (x * s * x⁻¹)) ^ 2 ^ k) := hMeq
      _ = D (S' x) (v (s ^ 2 ^ (k + 1))) := hM x hx s hs
      _ = D (S' x) (v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k)) := by rw [hXs]
      _ = D (S' x) (D (S' x) (v (w ^ 2 ^ (k + 1)))) := by rw [hM x hx w hw]
  have hC0 : C = 0 := by
    obtain ⟨x₁, hx₁, hS₁⟩ := hS'surj 1
    refine SzC1.eq_zero_of_idem H.card_K hf fun b => ?_
    have e := hidem x₁ hx₁ (H.sec b) (H.sec_mem b)
    rw [H.sec_X, hS₁, hC, hC, one_mul, one_mul] at e
    exact e.symm
  intro x hx w hw
  have hxU' := hle hx
  have hxN := H.nextU_le hE hxU'
  have hk1 : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      (w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k = 1 := by
    intro w hw
    have hcV := H.chi_mem_V_of_mem_nextU hE hxU' hw
    refine H.coords.eq_one_of_v_eq_zero H.stage.ha hK' (H.stage.pow_mem_szA₁ hcV) ?_
    rw [hM x hx w hw, hC, hC0, zero_mul]
  have h4 : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), ∃ s ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      w⁻¹ * (x * w * x⁻¹) = s ^ 4 := by
    intro w hw
    have hcV₁ := H.V_le_V₁ (H.chi_mem_V_of_mem_nextU hE hxU' hw)
    have hc1 := hk1 w hw
    obtain ⟨w₁, hw₁, hw₁e⟩ := H.exists_sq_of_pow_eq_one hcV₁ (by
      rw [pow_succ, pow_mul, hc1, one_pow])
    obtain ⟨s, hs, hse⟩ := H.exists_sq_of_pow_eq_one hw₁ (by
      rw [pow_succ', pow_mul, ← hw₁e, hc1])
    exact ⟨s, hs, by rw [hw₁e, hse, ← pow_mul]⟩
  have hx2 : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), x * (x * w * x⁻¹) * x⁻¹ = w := by
    intro w hw
    have h1 := mem_centralizer_iff.mp
      (H.U₁_le_centralizer_V₁ (H.sq_mem_U₁_of_mem_nextU hE hxU')) w hw
    calc x * (x * w * x⁻¹) * x⁻¹ = x ^ 2 * w * (x ^ 2)⁻¹ := by rw [sq]; group
      _ = w := by rw [← h1, mul_inv_cancel_right]
  have hsq := SzC1.sq_chi_eq_one hV₁comm hV₁pow (fun w hw => H.conj_mem_V₁ hxN hw) hx2 h4 w hw
  exact H.stage.omega _ (H.chi_mem_V_of_mem_nextU hE hxU' hw) hsq

end SzC1Next

end CFSG.SeitzReduction.RankOne
