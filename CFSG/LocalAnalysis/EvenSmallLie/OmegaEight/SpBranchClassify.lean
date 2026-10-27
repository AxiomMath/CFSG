module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchFib
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchNorm

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open KFacts

structure AutFacts (N : ℕ) (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (D : AutData) : Prop where
  h0 : mul 0 0 = 0
  inv_ok : invOK mul inv N = true
  kf : KFacts N mul D.K
  g_lt : ∀ l, l < D.q → D.g l < N
  nf : ∀ x, x < N → D.nfE x < 2 ^ D.q ∧ D.nfA x < 2 ^ D.K.n ∧
    x = mul (wprodN mul D.q D.g (D.nfE x)) (D.K.lin (D.nfA x))
  rel : ∀ i, i < D.q → ∀ j, j ≤ i → D.relA i j < 2 ^ D.K.n ∧
    (if j < i then cconj mul inv (D.g i) (D.g j) else mul (D.g i) (D.g i)) =
      mul (wprodN mul i D.g (D.relE i j)) (D.K.lin (D.relA i j))
  gens_lt : ∀ g ∈ D.gens, g < N
  gen : Gen mul D.gens N
  olen : ∀ v, v < 2 ^ D.K.n → ∃ O : List (ℕ × ℕ), orbOK mul inv N (D.K.lin v) O = true ∧
    orbClosed mul inv D.gens (D.K.lin v) O = true ∧ O.length = D.olen v
  M_eq : ∀ e, e < 2 ^ D.q → ∀ v, v < 2 ^ D.K.n → D.M e v < 2 ^ D.K.n ∧
    D.K.lin (D.M e v) = cconj mul inv (wprodN mul D.q D.g e) (D.K.lin v)
  cb_eq : ∀ j, j < D.q → ∀ i, i < D.K.n → D.cb j i < 2 ^ (i + 1) ∧
    D.K.lin (D.cb j i) = cconj mul inv (D.g j) (D.K.lin (2 ^ i))
  leaves : ∀ V ∈ nSearch D.K.n D.q D.M D.cb D.olen, ∃ k, k < D.nk ∧ ∃ e, e < 2 ^ D.q ∧
    ∀ i, i < D.K.n → V.getD i 0 = D.M e (D.P k i)
  P_lt : ∀ k, k < D.nk → ∀ i, i < D.K.n → D.P k i < 2 ^ D.K.n
  h_lt : ∀ k, k < D.nk → ∀ i, i < D.q → D.h k i < N
  h_act : ∀ k, k < D.nk → ∀ i, i < D.q → ∀ v, v < 2 ^ D.K.n →
    D.K.co (cconj mul inv (D.h k i) (D.K.lin (D.Pk k v))) =
      D.Pk k (D.K.co (cconj mul inv (D.g i) (D.K.lin v)))
  R_lt : ∀ k, k < D.nk → ∀ i, i < D.q → ∀ d ∈ D.R k i, d < 2 ^ D.K.n
  canon : ∀ k, k < D.nk → ∀ i, i < D.q → ∀ d, d < 2 ^ D.K.n →
    D.cA k i d < 2 ^ D.K.n ∧ D.cD k i d ∈ D.R k i ∧
    (∀ l, l < i → mul (D.K.lin (D.cA k i d)) (D.h k l) = mul (D.h k l) (D.K.lin (D.cA k i d))) ∧
    cconj mul inv (D.K.lin (D.cA k i d)) (mul (D.h k i) (D.K.lin d)) =
      mul (D.h k i) (D.K.lin (D.cD k i d))

namespace AutFacts

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {D : AutData}
  (hF : AutFacts N mul inv D) (Φ : CodeIso H N mul)

include hF in
theorem f_conj' (x y : H) : Φ.f (x * y * x⁻¹) = cconj mul inv (Φ.f x) (Φ.f y) :=
  Φ.f_conj hF.h0 (fun _ hc => inv_spec hF.inv_ok hc) x y

include hF in
theorem el_zero : el Φ D.K 0 = 1 := by
  have h := hF.kf.el_xor Φ (Nat.two_pow_pos D.K.n) (Nat.two_pow_pos D.K.n)
  rw [Nat.xor_self] at h
  exact mul_eq_left.1 h.symm

variable (hchar : ∀ γ : H ≃* H, ∀ x : H, Mem Φ D.K x → Mem Φ D.K (γ x))

include hchar in
theorem mem_conj {x : H} (hx : Mem Φ D.K x) (y : H) : Mem Φ D.K (y * x * y⁻¹) := by
  have := hchar (MulAut.conj y) x hx
  simpa using this

include hF in
theorem el_mem {v : ℕ} (hv : v < 2 ^ D.K.n) : Mem Φ D.K (el Φ D.K v) :=
  (hF.kf.mem_iff Φ).2 ⟨v, hv, rfl⟩

include hF in
theorem el_co {x : H} (hx : Mem Φ D.K x) : el Φ D.K (D.K.co (Φ.f x)) = x :=
  Φ.inj (by rw [hF.kf.f_el Φ hx.1, hx.2])

include hF hchar in
theorem psi_ne_zero (γ : H ≃* H) {i : ℕ} (hi : i < D.K.n) : psi Φ D.K γ (2 ^ i) ≠ 0 := by
  intro h0
  have h2 : 2 ^ i < 2 ^ D.K.n := Nat.pow_lt_pow_right Nat.one_lt_two hi
  have h1 := hF.kf.el_psi Φ hchar γ h2
  rw [h0, hF.el_zero Φ] at h1
  have h3 : el Φ D.K (2 ^ i) = el Φ D.K 0 := by
    rw [hF.el_zero Φ]; exact (γ.map_eq_one_iff.1 h1.symm)
  have h4 := congrArg (fun x => D.K.co (Φ.f x)) h3
  simp only [hF.kf.f_el Φ h2, hF.kf.f_el Φ (Nat.two_pow_pos _), hF.kf.co_lin _ h2,
    hF.kf.co_lin _ (Nat.two_pow_pos _)] at h4
  exact absurd h4 (Nat.two_pow_pos i).ne'

include hF in
theorem ncard_el {v : ℕ} (hv : v < 2 ^ D.K.n) :
    (MulAction.orbit (ConjAct H) (el Φ D.K v)).ncard = D.olen v := by
  obtain ⟨O, hO, hC, hlen⟩ := hF.olen v hv
  rw [← hF.kf.f_el Φ hv] at hO hC
  rw [Φ.ncard_eq hF.h0 hF.inv_ok hF.gens_lt hF.gen hO hC, hlen]

include hF hchar in
theorem exists_coset (γ : H ≃* H) : ∃ k, k < D.nk ∧ ∃ e, e < 2 ^ D.q ∧
    ∀ i, i < D.K.n → γ (el Φ D.K (2 ^ i)) =
      Φ.g (wprodN mul D.q D.g e) * el Φ D.K (D.P k i) * (Φ.g (wprodN mul D.q D.g e))⁻¹ := by
  set V : ℕ → ℕ := fun i => psi Φ D.K γ (2 ^ i) with hVdef
  set E : ℕ → ℕ := fun j => D.nfE (Φ.f (γ (Φ.g (D.g j)))) with hEdef
  have h2 : ∀ i, i < D.K.n → 2 ^ i < 2 ^ D.K.n := fun i hi =>
    Nat.pow_lt_pow_right Nat.one_lt_two hi
  have hVlt : ∀ i, i < D.K.n → V i < 2 ^ D.K.n := fun i hi => hF.kf.psi_lt Φ hchar γ (h2 i hi)
  have hV : ∀ i, i < D.K.n → V i ≠ 0 ∧ V i < 2 ^ D.K.n ∧ D.olen (V i) = D.olen (2 ^ i) := by
    intro i hi
    refine ⟨hF.psi_ne_zero Φ hchar γ hi, hVlt i hi, ?_⟩
    rw [← hF.ncard_el Φ (hVlt i hi), ← hF.ncard_el Φ (h2 i hi), hF.kf.el_psi Φ hchar γ (h2 i hi),
      CodeIso.ncard_orbit_map]
  have hE : ∀ j, j < D.q → E j < 2 ^ D.q := fun j _ => (hF.nf _ (Φ.lt _)).1
  have hM : ∀ i, i < D.K.n → ∀ j, j < D.q → D.M (E j) (V i) = xorBits (i + 1) V (D.cb j i) := by
    intro i hi j hj
    obtain ⟨hEl, hAl, hnf⟩ := hF.nf _ (Φ.lt (γ (Φ.g (D.g j))))
    set w := Φ.g (wprodN mul D.q D.g (E j))
    set a := el Φ D.K (D.nfA (Φ.f (γ (Φ.g (D.g j)))))
    have hga : γ (Φ.g (D.g j)) = w * a := by
      apply Φ.inj
      rw [Φ.map_mul, Φ.f_g (Φ.g_wprodN hF.h0 hF.g_lt _).1, hF.kf.f_el Φ hAl]
      exact hnf
    have hcb := hF.cb_eq j hj i hi
    have hcbl : D.cb j i < 2 ^ D.K.n :=
      lt_of_lt_of_le hcb.1 (Nat.pow_le_pow_right Nat.two_pos (by omega))
    have hconj : Φ.g (D.g j) * el Φ D.K (2 ^ i) * (Φ.g (D.g j))⁻¹ = el Φ D.K (D.cb j i) := by
      apply Φ.inj
      rw [hF.f_conj' Φ, Φ.f_g (hF.g_lt j hj), hF.kf.f_el Φ (h2 i hi), hF.kf.f_el Φ hcbl, hcb.2]
    have hlhs : w * el Φ D.K (V i) * w⁻¹ = el Φ D.K (xorBits (i + 1) V (D.cb j i)) := by
      have e1 : w * el Φ D.K (V i) * w⁻¹ = γ (Φ.g (D.g j)) * γ (el Φ D.K (2 ^ i)) *
          (γ (Φ.g (D.g j)))⁻¹ := by
        rw [hga, ← hF.kf.el_psi Φ hchar γ (h2 i hi)]
        have hc := hF.kf.mem_comm Φ (hF.el_mem Φ hAl) (hF.el_mem Φ (hVlt i hi))
        calc w * el Φ D.K (V i) * w⁻¹ = w * (a * el Φ D.K (V i) * a⁻¹) * w⁻¹ := by
              rw [hc, mul_inv_cancel_right]
          _ = w * a * el Φ D.K (V i) * (w * a)⁻¹ := by group
      rw [e1, ← map_mul, ← map_inv, ← map_mul, hconj, ← hF.kf.el_psi Φ hchar γ hcbl,
        hF.kf.psi_eq_xorBits Φ hchar γ hcbl]
      congr 1
      have := xorBits_eq_of_lt (f := fun j => psi Φ D.K γ (2 ^ j)) hcb.1 (D.K.n - (i + 1))
      rw [show i + 1 + (D.K.n - (i + 1)) = D.K.n by omega] at this
      exact this
    have hMl := hF.M_eq (E j) (hE j hj) (V i) (hVlt i hi)
    have hxl : xorBits (i + 1) V (D.cb j i) < 2 ^ D.K.n := by
      have e := xorBits_eq_of_lt (f := V) hcb.1 (D.K.n - (i + 1))
      rw [show i + 1 + (D.K.n - (i + 1)) = D.K.n by omega] at e
      rw [← e]
      exact xorBits_lt (fun l hl => hVlt l hl) _
    apply hF.kf.co_lin _ hMl.1 |>.symm.trans
    rw [hMl.2, ← hF.kf.co_lin _ hxl]
    congr 1
    rw [← hF.kf.f_el Φ (hVlt i hi), ← Φ.f_g (Φ.g_wprodN hF.h0 hF.g_lt (E j)).1, ← hF.f_conj' Φ,
      hlhs, hF.kf.f_el Φ hxl]
  obtain ⟨k, hk, e, he, hP⟩ := hF.leaves _ (mem_nSearch hV hE hM)
  refine ⟨k, hk, e, he, fun i hi => ?_⟩
  have hVi : V i = D.M e (D.P k i) := by
    have := hP i hi
    rwa [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range] at this
  have hMe := hF.M_eq e he _ (hF.P_lt k hk i hi)
  rw [← hF.kf.el_psi Φ hchar γ (h2 i hi)]
  change el Φ D.K (V i) = _
  apply Φ.inj
  rw [hF.f_conj' Φ, hF.kf.f_el Φ (hVlt i hi), hVi, hMe.2, Φ.f_g (Φ.g_wprodN hF.h0 hF.g_lt e).1,
    hF.kf.f_el Φ (hF.P_lt k hk i hi)]

include hF hchar in
theorem mem_of_comm_image (γ : H ≃* H) {x : H}
    (hx : ∀ j, j < D.K.n → x * γ (el Φ D.K (2 ^ j)) = γ (el Φ D.K (2 ^ j)) * x) :
    Mem Φ D.K x := by
  have hy : Mem Φ D.K (γ.symm x) := by
    refine hF.kf.mem_of_comm Φ fun j hj => ?_
    have := congrArg γ.symm (hx j hj)
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
  have := hchar γ _ hy
  rwa [MulEquiv.apply_symm_apply] at this

@[expose] def OnK (D : AutData) (γ : H ≃* H) (k : ℕ) : Prop :=
  ∀ i, i < D.K.n → γ (el Φ D.K (2 ^ i)) = el Φ D.K (D.P k i)

include hF in
theorem Pk_lt {k : ℕ} (hk : k < D.nk) (v : ℕ) : D.Pk k v < 2 ^ D.K.n :=
  xorBits_lt (fun i hi => hF.P_lt k hk i hi) v

include hF hchar in
theorem el_Pk {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) {v : ℕ}
    (hv : v < 2 ^ D.K.n) : γ (el Φ D.K v) = el Φ D.K (D.Pk k v) := by
  have hps : ∀ i, i < D.K.n → psi Φ D.K γ (2 ^ i) = D.P k i := by
    intro i hi
    unfold psi
    rw [hγ i hi, hF.kf.f_el Φ (hF.P_lt k hk i hi), hF.kf.co_lin _ (hF.P_lt k hk i hi)]
  rw [← hF.kf.el_psi Φ hchar γ hv, hF.kf.psi_eq_xorBits Φ hchar γ hv]
  unfold AutData.Pk
  rw [xorBits_congr hps]

include hF hchar in
theorem conj_el_eq {x : H} {v w : ℕ} (hv : v < 2 ^ D.K.n)
    (h : D.K.co (cconj mul inv (Φ.f x) (D.K.lin v)) = w) :
    x * el Φ D.K v * x⁻¹ = el Φ D.K w := by
  have hm := mem_conj Φ hchar (hF.el_mem Φ hv) x
  rw [← hF.el_co Φ hm, hF.f_conj' Φ, hF.kf.f_el Φ hv, h]

include hF hchar in
theorem mem_comp {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) {l : ℕ} (hl : l < D.q) :
    Mem Φ D.K ((Φ.g (D.h k l))⁻¹ * γ (Φ.g (D.g l))) := by
  set x := (Φ.g (D.h k l))⁻¹ * γ (Φ.g (D.g l))
  have hcomm : ∀ v, v < 2 ^ D.K.n → x * el Φ D.K (D.Pk k v) = el Φ D.K (D.Pk k v) * x := by
    intro v hv
    set w := D.K.co (cconj mul inv (D.g l) (D.K.lin v))
    have hw : Φ.g (D.g l) * el Φ D.K v * (Φ.g (D.g l))⁻¹ = el Φ D.K w :=
      hF.conj_el_eq Φ hchar hv (by rw [Φ.f_g (hF.g_lt l hl)])
    have hwlt : w < 2 ^ D.K.n := by
      have hm := mem_conj Φ hchar (hF.el_mem Φ hv) (Φ.g (D.g l))
      have := hm.1
      rwa [hF.f_conj' Φ, Φ.f_g (hF.g_lt l hl), hF.kf.f_el Φ hv] at this
    have h1 : γ (Φ.g (D.g l)) * el Φ D.K (D.Pk k v) * (γ (Φ.g (D.g l)))⁻¹ =
        el Φ D.K (D.Pk k w) := by
      rw [← hF.el_Pk Φ hchar hk hγ hv, ← map_mul, ← map_inv, ← map_mul, hw,
        hF.el_Pk Φ hchar hk hγ hwlt]
    have h2 : Φ.g (D.h k l) * el Φ D.K (D.Pk k v) * (Φ.g (D.h k l))⁻¹ = el Φ D.K (D.Pk k w) :=
      hF.conj_el_eq Φ hchar (hF.Pk_lt hk v) (by
        rw [Φ.f_g (hF.h_lt k hk l hl)]; exact hF.h_act k hk l hl v hv)
    have e : γ (Φ.g (D.g l)) * el Φ D.K (D.Pk k v) * (γ (Φ.g (D.g l)))⁻¹ =
        Φ.g (D.h k l) * el Φ D.K (D.Pk k v) * (Φ.g (D.h k l))⁻¹ := by rw [h1, h2]
    have e2 : x * el Φ D.K (D.Pk k v) * x⁻¹ = el Φ D.K (D.Pk k v) := by
      calc x * el Φ D.K (D.Pk k v) * x⁻¹ = (Φ.g (D.h k l))⁻¹ * (γ (Φ.g (D.g l)) *
            el Φ D.K (D.Pk k v) * (γ (Φ.g (D.g l)))⁻¹) * Φ.g (D.h k l) := by
              simp only [x]; group
        _ = (Φ.g (D.h k l))⁻¹ * (Φ.g (D.h k l) * el Φ D.K (D.Pk k v) * (Φ.g (D.h k l))⁻¹) *
            Φ.g (D.h k l) := by rw [e]
        _ = el Φ D.K (D.Pk k v) := by group
    calc x * el Φ D.K (D.Pk k v) = x * el Φ D.K (D.Pk k v) * x⁻¹ * x := by group
      _ = el Φ D.K (D.Pk k v) * x := by rw [e2]
  exact hF.mem_of_comm_image Φ hchar γ fun j hj => by
    have h2 : 2 ^ j < 2 ^ D.K.n := Nat.pow_lt_pow_right Nat.one_lt_two hj
    rw [hF.el_Pk Φ hchar hk hγ h2]
    exact hcomm _ h2

@[expose] noncomputable def comp (D : AutData) (γ : H ≃* H) (k l : ℕ) : ℕ :=
  D.K.co (Φ.f ((Φ.g (D.h k l))⁻¹ * γ (Φ.g (D.g l))))

include hF hchar in
theorem comp_spec {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) {l : ℕ}
    (hl : l < D.q) : comp Φ D γ k l < 2 ^ D.K.n ∧
      Φ.f (γ (Φ.g (D.g l))) = mul (D.h k l) (D.K.lin (comp Φ D γ k l)) := by
  have hm := hF.mem_comp Φ hchar hk hγ hl
  refine ⟨hm.1, ?_⟩
  have e : γ (Φ.g (D.g l)) = Φ.g (D.h k l) * el Φ D.K (comp Φ D γ k l) := by
    unfold comp
    rw [hF.el_co Φ hm]; group
  rw [e, Φ.map_mul, Φ.f_g (hF.h_lt k hk l hl),
    hF.kf.f_el Φ (show comp Φ D γ k l < 2 ^ D.K.n from hm.1)]

include hF in
theorem comp_eq_of {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) {l : ℕ} (hl : l < D.q) {w : ℕ}
    (hw : w < 2 ^ D.K.n) (h : Φ.f (γ (Φ.g (D.g l))) = mul (D.h k l) (D.K.lin w)) :
    comp Φ D γ k l = w := by
  have e : γ (Φ.g (D.g l)) = Φ.g (D.h k l) * el Φ D.K w := by
    apply Φ.inj
    rw [h, Φ.map_mul, Φ.f_g (hF.h_lt k hk l hl), hF.kf.f_el Φ hw]
  unfold comp
  rw [e, inv_mul_cancel_left, hF.kf.f_el Φ hw, hF.kf.co_lin _ hw]

include hF in
theorem onK_conj {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) {a : ℕ}
    (ha : a < 2 ^ D.K.n) : OnK Φ D (γ.trans (MulAut.conj (el Φ D.K a))) k := by
  intro i hi
  simp only [MulEquiv.trans_apply, MulAut.conj_apply]
  rw [hγ i hi, hF.kf.el_comm Φ ha (hF.P_lt k hk i hi), mul_inv_cancel_right]

include hF Φ in
theorem cconj_fix {a c h : ℕ} (ha : a < 2 ^ D.K.n) (hc : c < 2 ^ D.K.n) (hh : h < N)
    (hcomm : mul (D.K.lin a) h = mul h (D.K.lin a)) :
    cconj mul inv (D.K.lin a) (mul h (D.K.lin c)) = mul h (D.K.lin c) := by
  have hAH : el Φ D.K a * Φ.g h = Φ.g h * el Φ D.K a := by
    apply Φ.inj
    rw [Φ.map_mul, Φ.map_mul, hF.kf.f_el Φ ha, Φ.f_g hh, hcomm]
  have hAC := hF.kf.el_comm Φ ha hc
  have e : el Φ D.K a * (Φ.g h * el Φ D.K c) * (el Φ D.K a)⁻¹ = Φ.g h * el Φ D.K c := by
    calc el Φ D.K a * (Φ.g h * el Φ D.K c) * (el Φ D.K a)⁻¹ =
        (el Φ D.K a * Φ.g h) * el Φ D.K c * (el Φ D.K a)⁻¹ := by group
      _ = Φ.g h * (el Φ D.K a * el Φ D.K c) * (el Φ D.K a)⁻¹ := by rw [hAH]; group
      _ = Φ.g h * el Φ D.K c := by rw [hAC]; group
  have := congrArg Φ.f e
  rw [hF.f_conj' Φ, Φ.map_mul, hF.kf.f_el Φ ha, Φ.f_g hh, hF.kf.f_el Φ hc] at this
  exact this

include hF hchar in
theorem exists_canon {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) :
    ∃ a, a < 2 ^ D.K.n ∧ ∀ l, l < D.q →
      comp Φ D (γ.trans (MulAut.conj (el Φ D.K a))) k l ∈ D.R k l := by
  have key : ∀ m, m ≤ D.q → ∃ a, a < 2 ^ D.K.n ∧ ∀ l, l < m →
      comp Φ D (γ.trans (MulAut.conj (el Φ D.K a))) k l ∈ D.R k l := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨0, Nat.two_pow_pos _, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨a, ha, hR⟩ := ih (by omega)
      set γa := γ.trans (MulAut.conj (el Φ D.K a))
      have hγa := hF.onK_conj Φ hk hγ ha
      set d := comp Φ D γa k m
      have hd := hF.comp_spec Φ hchar hk hγa (show m < D.q by omega)
      obtain ⟨ha', hR', hcomm, hconj⟩ := hF.canon k hk m (by omega) d hd.1
      set a' := D.cA k m d
      refine ⟨a' ^^^ a, Nat.xor_lt_two_pow ha' ha, fun l hl => ?_⟩
      have hγ' : ∀ x, (γ.trans (MulAut.conj (el Φ D.K (a' ^^^ a)))) x =
          el Φ D.K a' * γa x * (el Φ D.K a')⁻¹ := by
        intro x
        simp only [γa, MulEquiv.trans_apply, MulAut.conj_apply, hF.kf.el_xor Φ ha' ha]
        group
      have hfl : ∀ l, l < D.q → Φ.f ((γ.trans (MulAut.conj (el Φ D.K (a' ^^^ a)))) (Φ.g (D.g l))) =
          cconj mul inv (D.K.lin a') (mul (D.h k l) (D.K.lin (comp Φ D γa k l))) := by
        intro l hl
        rw [hγ', hF.f_conj' Φ, hF.kf.f_el Φ ha', (hF.comp_spec Φ hchar hk hγa hl).2]
      by_cases hlm : l < m
      ·
        have hcl := hF.comp_spec Φ hchar hk hγa (show l < D.q by omega)
        rw [hF.comp_eq_of Φ hk (show l < D.q by omega) hcl.1 (by
          rw [hfl l (by omega)]
          exact hF.cconj_fix Φ ha' hcl.1 (hF.h_lt k hk l (by omega)) (hcomm l hlm))]
        exact hR l hlm
      · have hl' : l = m := by omega
        subst hl'
        rw [hF.comp_eq_of Φ hk (show l < D.q by omega) (hF.R_lt k hk l (by omega) _ hR')
          (by rw [hfl l (by omega)]; exact hconj)]
        exact hR'
  exact key D.q le_rfl

include hF hchar in
theorem ys_eq {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) {m : ℕ} (hm : m ≤ D.q)
    {l : ℕ} (hl : l < m) :
    D.ys mul k ((List.range m).map (comp Φ D γ k)) l = Φ.f (γ (Φ.g (D.g l))) := by
  unfold AutData.ys
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range,
    (hF.comp_spec Φ hchar hk hγ (by omega)).2]

include hF hchar in
theorem f_wprod {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) {m i : ℕ}
    (hm : m ≤ D.q) (hi : i ≤ m) (e : ℕ) :
    Φ.f (γ (Φ.g (wprodN mul i D.g e))) =
      wprodN mul i (D.ys mul k ((List.range m).map (comp Φ D γ k))) e := by
  rw [Φ.f_map_wprodN hF.h0 γ (fun l hl => hF.g_lt l (by omega)) e]
  exact wprodN_congr mul (fun l hl => (hF.ys_eq Φ hchar hk hγ hm (by omega)).symm) e

include hF hchar in
theorem relOK_comp {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) {i : ℕ}
    (hi : i < D.q) : D.relOK mul inv k i ((List.range (i + 1)).map (comp Φ D γ k)) = true := by
  unfold AutData.relOK
  rw [List.all_eq_true]
  intro j hj
  have hj' : j ≤ i := by have := List.mem_range.1 hj; omega
  obtain ⟨hAlt, hrel⟩ := hF.rel i hi j hj'
  rw [beq_iff_eq, hF.ys_eq Φ hchar hk hγ (show i + 1 ≤ D.q by omega) (show i < i + 1 by omega)]
  have hrhs : mul (wprodN mul i (D.ys mul k ((List.range (i + 1)).map (comp Φ D γ k)))
      (D.relE i j)) (D.K.lin (D.Pk k (D.relA i j))) =
      Φ.f (γ (Φ.g (wprodN mul i D.g (D.relE i j)) * el Φ D.K (D.relA i j))) := by
    rw [map_mul, Φ.map_mul, ← hF.f_wprod Φ hchar hk hγ (show i + 1 ≤ D.q by omega)
      (show i ≤ i + 1 by omega), hF.el_Pk Φ hchar hk hγ hAlt, hF.kf.f_el Φ (hF.Pk_lt hk _)]
  rw [hrhs]
  have hlhs : Φ.g (wprodN mul i D.g (D.relE i j)) * el Φ D.K (D.relA i j) =
      Φ.g (mul (wprodN mul i D.g (D.relE i j)) (D.K.lin (D.relA i j))) := by
    apply Φ.inj
    rw [Φ.map_mul, Φ.f_g (Φ.g_wprodN hF.h0 (fun l hl => hF.g_lt l (by omega)) _).1,
      hF.kf.f_el Φ hAlt, Φ.f_g]
    rw [← Φ.f_g (Φ.g_wprodN hF.h0 (fun l hl => hF.g_lt l (by omega)) (D.relE i j)).1,
      ← hF.kf.f_el Φ hAlt, ← Φ.map_mul]
    exact Φ.lt _
  rw [hlhs, ← hrel]
  split
  · rename_i hji
    rw [hF.ys_eq Φ hchar hk hγ (show i + 1 ≤ D.q by omega) (show j < i + 1 by omega),
      ← hF.f_conj' Φ, ← map_mul, ← map_inv, ← map_mul]
    congr 2
    apply Φ.inj
    rw [hF.f_conj' Φ, Φ.f_g (hF.g_lt i hi), Φ.f_g (hF.g_lt j (by omega)), Φ.f_g]
    rw [cconj, ← Φ.f_g (hF.g_lt i hi), ← Φ.f_g (hF.g_lt j (by omega)),
      ← Φ.f_inv hF.h0 (inv_spec hF.inv_ok (Φ.lt _)).1 (inv_spec hF.inv_ok (Φ.lt _)).2,
      ← Φ.map_mul, ← Φ.map_mul]
    exact Φ.lt _
  · rw [← Φ.map_mul, ← map_mul]
    congr 2
    apply Φ.inj
    rw [Φ.map_mul, Φ.f_g (hF.g_lt i hi), Φ.f_g]
    rw [← Φ.f_g (hF.g_lt i hi), ← Φ.map_mul]
    exact Φ.lt _

include hF hchar in
theorem f_eq_F {γ : H ≃* H} {k : ℕ} (hk : k < D.nk) (hγ : OnK Φ D γ k) (x : H) :
    Φ.f (γ x) = D.F mul k ((List.range D.q).map (comp Φ D γ k)) (Φ.f x) := by
  obtain ⟨hE, hA, hnf⟩ := hF.nf _ (Φ.lt x)
  have hx : x = Φ.g (wprodN mul D.q D.g (D.nfE (Φ.f x))) * el Φ D.K (D.nfA (Φ.f x)) := by
    apply Φ.inj
    rw [Φ.map_mul, Φ.f_g (Φ.g_wprodN hF.h0 hF.g_lt _).1, hF.kf.f_el Φ hA]
    exact hnf
  unfold AutData.F
  conv_lhs => rw [hx]
  rw [map_mul, Φ.map_mul, hF.f_wprod Φ hchar hk hγ le_rfl le_rfl, hF.el_Pk Φ hchar hk hγ hA,
    hF.kf.f_el Φ (hF.Pk_lt hk _)]

include hF hchar in
theorem classify (γ : H ≃* H) : ∃ s : H, ∃ k, k < D.nk ∧ ∃ ds ∈ D.fSearch mul inv k,
    ∀ x : H, Φ.f (γ x) = cconj mul inv (Φ.f s) (D.F mul k ds (Φ.f x)) := by
  obtain ⟨k, hk, e, he, hcos⟩ := hF.exists_coset Φ hchar γ
  set w := Φ.g (wprodN mul D.q D.g e)
  set γ₁ := γ.trans (MulAut.conj w)⁻¹
  have hγ₁ : OnK Φ D γ₁ k := by
    intro i hi
    simp only [γ₁, MulEquiv.trans_apply, hcos i hi]
    change (MulAut.conj w)⁻¹ (w * el Φ D.K (D.P k i) * w⁻¹) = _
    rw [MulAut.inv_def, MulAut.conj_symm_apply]
    group
  obtain ⟨a, ha, hR⟩ := hF.exists_canon Φ hchar hk hγ₁
  set γ' := γ₁.trans (MulAut.conj (el Φ D.K a))
  have hγ' : OnK Φ D γ' k := hF.onK_conj Φ hk hγ₁ ha
  refine ⟨w * (el Φ D.K a)⁻¹, k, hk, (List.range D.q).map (comp Φ D γ' k), ?_, fun x => ?_⟩
  · exact D.mem_fSearch mul inv (fun l hl => hR l hl)
      (fun i hi => hF.relOK_comp Φ hchar hk hγ' hi)
  · rw [← hF.f_eq_F Φ hchar hk hγ' x, ← hF.f_conj' Φ]
    congr 1
    simp only [γ', γ₁, MulEquiv.trans_apply, MulAut.conj_apply, MulAut.inv_def,
      MulAut.conj_symm_apply]
    group

end AutFacts

end CFSG.EvenSmallLie.OmegaEight.SpBranch
