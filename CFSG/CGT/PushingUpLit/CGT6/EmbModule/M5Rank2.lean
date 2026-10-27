module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Basic
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

variable {V : Type} [CommGroup V] {G : Type} [Group G]

section Product

theorem prod_zmod3 (f : ZMod 3 → V) : ∏ x : ZMod 3, f x = f 0 * f 1 * f 2 := by
  have hU : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  ac_rfl

theorem prod_zmod3_sq (f : ZMod 3 × ZMod 3 → V) :
    ∏ x : ZMod 3 × ZMod 3, f x =
      f (0, 0) * f (0, 1) * f (0, 2) * f (1, 0) * f (1, 1) * f (1, 2) * f (2, 0) * f (2, 1) *
        f (2, 2) := by
  rw [Fintype.prod_prod_type, prod_zmod3]
  simp only [prod_zmod3]
  ac_rfl

end Product

section Stab

variable (ρ : G →* MulAut V)

@[expose] def stab (w : V) : Subgroup G where
  carrier := {g | ρ g w = w}
  one_mem' := by
    change ρ 1 w = w
    rw [map_one]
    rfl
  mul_mem' := fun {a b} ha hb => by
    change ρ (a * b) w = w
    change ρ a w = w at ha
    change ρ b w = w at hb
    rw [← rho_rho, hb, ha]
  inv_mem' := fun {a} ha => by
    change ρ a⁻¹ w = w
    change ρ a w = w at ha
    calc ρ a⁻¹ w = ρ a⁻¹ (ρ a w) := by rw [ha]
      _ = w := by rw [rho_rho, inv_mul_cancel, map_one]; rfl

theorem mem_stab {g : G} {w : V} : g ∈ stab ρ w ↔ ρ g w = w := Iff.rfl

end Stab

section El

variable (e1 e2 : G)

structure Comm3 (e1 e2 : G) : Prop where
  pow1 : e1 ^ 3 = 1
  pow2 : e2 ^ 3 = 1
  comm : e1 * e2 = e2 * e1

@[expose] def el (x : ZMod 3 × ZMod 3) : G := e1 ^ x.1.val * e2 ^ x.2.val

variable {e1 e2}

theorem el_zero : el e1 e2 0 = 1 := by simp [el]

theorem el_add (h : Comm3 e1 e2) (x y : ZMod 3 × ZMod 3) :
    el e1 e2 (x + y) = el e1 e2 x * el e1 e2 y := by
  simp only [el, Prod.fst_add, Prod.snd_add, ZMod.val_add]
  rw [← pow_eq_pow_mod _ h.pow1, ← pow_eq_pow_mod _ h.pow2, pow_add, pow_add]
  have hc : e1 ^ y.1.val * e2 ^ x.2.val = e2 ^ x.2.val * e1 ^ y.1.val :=
    (Commute.pow_pow h.comm y.1.val x.2.val).eq
  calc e1 ^ x.1.val * e1 ^ y.1.val * (e2 ^ x.2.val * e2 ^ y.2.val)
      = e1 ^ x.1.val * (e1 ^ y.1.val * e2 ^ x.2.val) * e2 ^ y.2.val := by simp only [mul_assoc]
    _ = e1 ^ x.1.val * (e2 ^ x.2.val * e1 ^ y.1.val) * e2 ^ y.2.val := by rw [hc]
    _ = _ := by simp only [mul_assoc]

theorem val_one3 : (1 : ZMod 3).val = 1 := rfl
theorem val_two3 : (2 : ZMod 3).val = 2 := rfl

theorem el_10 : el e1 e2 (1, 0) = e1 := by simp [el, val_one3]
theorem el_01 : el e1 e2 (0, 1) = e2 := by simp [el, val_one3]
theorem el_11 : el e1 e2 (1, 1) = e1 * e2 := by simp [el, val_one3]
theorem el_12 : el e1 e2 (1, 2) = e1 * e2 ^ 2 := by simp [el, val_one3, val_two3]
theorem three_add_eq_zero : ∀ x : ZMod 3 × ZMod 3, x + x + x = 0 := by decide

theorem el_pow_three (h : Comm3 e1 e2) (x : ZMod 3 × ZMod 3) : el e1 e2 x ^ 3 = 1 := by
  have h2 : el e1 e2 x ^ 3 = el e1 e2 (x + x + x) := by
    rw [el_add h, el_add h, pow_succ, pow_two]
  rw [h2, three_add_eq_zero, el_zero]

theorem commute_el (h : Comm3 e1 e2) (x y : ZMod 3 × ZMod 3) :
    el e1 e2 x * el e1 e2 y = el e1 e2 y * el e1 e2 x := by
  rw [← el_add h, ← el_add h, add_comm]

end El

section Avg

variable (ρ : G →* MulAut V) (e1 e2 : G)

@[expose] def avgA (w : V) : V := ∏ x : ZMod 3 × ZMod 3, ρ (el e1 e2 x) w

theorem avgA_mul (v w : V) : avgA ρ e1 e2 (v * w) = avgA ρ e1 e2 v * avgA ρ e1 e2 w := by
  simp only [avgA, map_mul, Finset.prod_mul_distrib]

@[expose] def avgHom : V →* V where
  toFun := avgA ρ e1 e2
  map_one' := by simp [avgA]
  map_mul' := avgA_mul ρ e1 e2

theorem avgHom_apply (w : V) : avgHom ρ e1 e2 w = avgA ρ e1 e2 w := rfl

@[expose] def kerA : Subgroup V := (avgHom ρ e1 e2).ker

@[expose] def cen : Subgroup V := fixSub ρ e1 ⊓ fixSub ρ e2

variable {e1 e2}

theorem eps_el (h : Comm3 e1 e2) (d : ZMod 3 × ZMod 3) (w : V) :
    eps ρ (el e1 e2 d) w = ρ (el e1 e2 0) w * ρ (el e1 e2 d) w * ρ (el e1 e2 (d + d)) w := by
  rw [el_zero, el_add h, ← pow_two]
  simp only [eps, map_one]
  rfl

theorem zmod3_smul_zero : ∀ d : ZMod 3 × ZMod 3, (0 : ZMod 3) • d = 0 := by decide

theorem zmod3_smul_one : ∀ d : ZMod 3 × ZMod 3, (1 : ZMod 3) • d = d := by decide

theorem zmod3_smul_two : ∀ d : ZMod 3 × ZMod 3, (2 : ZMod 3) • d = d + d := by decide

theorem eps_el_prod (h : Comm3 e1 e2) (d : ZMod 3 × ZMod 3) (w : V) :
    eps ρ (el e1 e2 d) w = ∏ i : ZMod 3, ρ (el e1 e2 (i • d)) w := by
  rw [prod_zmod3, zmod3_smul_zero, zmod3_smul_one, zmod3_smul_two, eps_el ρ h]

theorem eps_comp (h : Comm3 e1 e2) (d d' : ZMod 3 × ZMod 3)
    (hb : Function.Bijective (fun p : ZMod 3 × ZMod 3 => p.1 • d + p.2 • d')) (w : V) :
    eps ρ (el e1 e2 d) (eps ρ (el e1 e2 d') w) = avgA ρ e1 e2 w := by
  rw [eps_el_prod ρ h d, eps_el_prod ρ h d' w]
  simp only [map_prod]
  have step : ∀ i j : ZMod 3, ρ (el e1 e2 (i • d)) (ρ (el e1 e2 (j • d')) w)
      = ρ (el e1 e2 (i • d + j • d')) w := by
    intro i j
    rw [rho_rho, el_add h]
  simp only [step]
  calc ∏ i : ZMod 3, ∏ j : ZMod 3, ρ (el e1 e2 (i • d + j • d')) w
      = ∏ p : ZMod 3 × ZMod 3, ρ (el e1 e2 (p.1 • d + p.2 • d')) w :=
        (Fintype.prod_prod_type
          (fun p : ZMod 3 × ZMod 3 => ρ (el e1 e2 (p.1 • d + p.2 • d')) w)).symm
    _ = avgA ρ e1 e2 w := Fintype.prod_equiv (Equiv.ofBijective _ hb) _ _ (fun p => rfl)

theorem rho_el_avgA (h : Comm3 e1 e2) (y : ZMod 3 × ZMod 3) (w : V) :
    ρ (el e1 e2 y) (avgA ρ e1 e2 w) = avgA ρ e1 e2 w := by
  simp only [avgA, map_prod, rho_rho, ← el_add h]
  exact Fintype.prod_equiv (Equiv.addLeft y) _ _ (fun x => rfl)

theorem fixed_el {w : V} (h1 : ρ e1 w = w) (h2 : ρ e2 w = w) (x : ZMod 3 × ZMod 3) :
    ρ (el e1 e2 x) w = w :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ ((mem_stab ρ).2 h1) _)
    (Subgroup.pow_mem _ ((mem_stab ρ).2 h2) _)

theorem avgA_eq_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {w : V} (h1 : ρ e1 w = w)
    (h2 : ρ e2 w = w) : avgA ρ e1 e2 w = w := by
  simp only [avgA, fixed_el ρ h1 h2, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card]
  rw [show 3 * 3 = 2 * 4 + 1 by norm_num, pow_succ, pow_mul, hV, one_pow, one_mul]

end Avg

section Pieces

variable (ρ : G →* MulAut V) (e1 e2 : G)

@[expose] def dirs : Fin 4 → ZMod 3 × ZMod 3
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)

theorem dirs_bij : ∀ i j : Fin 4, i ≠ j →
    Function.Bijective (fun p : ZMod 3 × ZMod 3 => p.1 • dirs i + p.2 • dirs j) := by decide

@[expose] def piece (i : Fin 4) : Subgroup V := fixSub ρ (el e1 e2 (dirs i)) ⊓ kerA ρ e1 e2

@[expose] def proj (i : Fin 4) (w : V) : V :=
  eps ρ (el e1 e2 (dirs i)) w * avgA ρ e1 e2 w

variable {ρ e1 e2}

theorem proj_mul (i : Fin 4) (v w : V) :
    proj ρ e1 e2 i (v * w) = proj ρ e1 e2 i v * proj ρ e1 e2 i w := by
  unfold proj
  rw [eps_mul, avgA_mul]
  exact mul_mul_mul_comm _ _ _ _

variable (ρ e1 e2)

@[expose] def projHom (i : Fin 4) : V →* V where
  toFun := proj ρ e1 e2 i
  map_one' := by simp [proj, eps, avgA]
  map_mul' := proj_mul i

theorem projHom_apply (i : Fin 4) (w : V) : projHom ρ e1 e2 i w = proj ρ e1 e2 i w := rfl

variable {ρ e1 e2}

theorem proj_cen (hV : ∀ v : V, v ^ 2 = 1) {c : V} (hc : c ∈ cen ρ e1 e2) (i : Fin 4) :
    proj ρ e1 e2 i c = 1 := by
  have h1 : ρ (el e1 e2 (dirs i)) c = c := fixed_el ρ hc.1 hc.2 _
  unfold proj
  rw [eps_eq_self_of_fixed ρ hV h1, avgA_eq_of_fixed ρ hV hc.1 hc.2, mul_self_eq_one' hV]

theorem proj_piece_self (hV : ∀ v : V, v ^ 2 = 1) {i : Fin 4} {w : V}
    (hw : w ∈ piece ρ e1 e2 i) : proj ρ e1 e2 i w = w := by
  have hA : avgA ρ e1 e2 w = 1 := hw.2
  unfold proj
  rw [eps_eq_self_of_fixed ρ hV hw.1, hA, mul_one]

theorem proj_piece_ne (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2) {i j : Fin 4} (hij : i ≠ j)
    {w : V} (hw : w ∈ piece ρ e1 e2 j) : proj ρ e1 e2 i w = 1 := by
  have hA : avgA ρ e1 e2 w = 1 := hw.2
  have hfix : eps ρ (el e1 e2 (dirs j)) w = w := eps_eq_self_of_fixed ρ hV hw.1
  have h1 : eps ρ (el e1 e2 (dirs i)) w = 1 := by
    calc eps ρ (el e1 e2 (dirs i)) w
        = eps ρ (el e1 e2 (dirs i)) (eps ρ (el e1 e2 (dirs j)) w) := by rw [hfix]
      _ = avgA ρ e1 e2 w := eps_comp ρ h _ _ (dirs_bij i j hij) w
      _ = 1 := hA
  unfold proj
  rw [h1, hA, one_mul]

theorem indep (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2) {c : V} (hc : c ∈ cen ρ e1 e2)
    {p : Fin 4 → V} (hp : ∀ i, p i ∈ piece ρ e1 e2 i) (hprod : c * ∏ i, p i = 1) :
    c = 1 ∧ ∀ i, p i = 1 := by
  have hA : avgA ρ e1 e2 c = c := avgA_eq_of_fixed ρ hV hc.1 hc.2
  have hAp : ∀ i, avgA ρ e1 e2 (p i) = 1 := fun i => (hp i).2
  have hc1 : c = 1 := by
    have h1 := congrArg (avgHom ρ e1 e2) hprod
    rw [map_mul, map_prod, map_one] at h1
    simpa [avgHom_apply, hA, hAp] using h1
  refine ⟨hc1, fun i => ?_⟩
  have h2 := congrArg (projHom ρ e1 e2 i) hprod
  rw [map_mul, map_prod, map_one] at h2
  simp only [projHom_apply] at h2
  rw [proj_cen hV hc, one_mul,
    Finset.prod_eq_single i (fun j _ hj => proj_piece_ne hV h (Ne.symm hj) (hp j))
      (by simp), proj_piece_self hV (hp i)] at h2
  exact h2

theorem prod_eps_dirs (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2) (w : V) :
    ∏ i : Fin 4, eps ρ (el e1 e2 (dirs i)) w = w * avgA ρ e1 e2 w := by
  have key : ∀ f : ZMod 3 × ZMod 3 → V, f (0, 0) * f (0, 0) = 1 →
      ∏ i : Fin 4, (f (0, 0) * f (dirs i) * f (dirs i + dirs i)) = f (0, 0) * ∏ x, f x := by
    intro f hf
    simp only [Fin.prod_univ_four]
    rw [prod_zmod3_sq]
    have e0 : dirs 0 + dirs 0 = (2, 0) := by decide
    have e1' : dirs 1 + dirs 1 = (0, 2) := by decide
    have e2' : dirs 2 + dirs 2 = (2, 2) := by decide
    have e3 : dirs 3 + dirs 3 = (2, 1) := by decide
    have d0 : dirs 0 = (1, 0) := rfl
    have d1 : dirs 1 = (0, 1) := rfl
    have d2 : dirs 2 = (1, 1) := rfl
    have d3 : dirs 3 = (1, 2) := rfl
    rw [e0, e1', e2', e3, d0, d1, d2, d3]
    calc _ = (f (0, 0) * f (0, 0)) * (f (0, 0) * f (0, 0)) *
          (f (0, 1) * f (0, 2) * f (1, 0) * f (1, 1) * f (1, 2) * f (2, 0) * f (2, 1) *
            f (2, 2)) := by ac_rfl
      _ = (f (0, 0) * f (0, 0)) *
          (f (0, 1) * f (0, 2) * f (1, 0) * f (1, 1) * f (1, 2) * f (2, 0) * f (2, 1) *
            f (2, 2)) := by rw [hf, one_mul]
      _ = _ := by ac_rfl
  have hf : ρ (el e1 e2 (0, 0)) w * ρ (el e1 e2 (0, 0)) w = 1 := by
    have h0 : el e1 e2 (0, 0) = 1 := el_zero
    rw [h0, map_one]
    exact mul_self_eq_one' hV w
  have hk := key (fun x => ρ (el e1 e2 x) w) hf
  have h00 : el e1 e2 (0, 0) = 1 := el_zero
  have hw : ρ (el e1 e2 (0, 0)) w = w := by rw [h00, map_one]; rfl
  calc ∏ i : Fin 4, eps ρ (el e1 e2 (dirs i)) w
      = ∏ i : Fin 4, (ρ (el e1 e2 (0, 0)) w * ρ (el e1 e2 (dirs i)) w *
          ρ (el e1 e2 (dirs i + dirs i)) w) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        exact eps_el ρ h _ w
    _ = ρ (el e1 e2 (0, 0)) w * ∏ x : ZMod 3 × ZMod 3, ρ (el e1 e2 x) w := hk
    _ = w * avgA ρ e1 e2 w := by rw [hw]; rfl

theorem avgA_eps (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2) (i : Fin 4)
    (w : V) :
    avgA ρ e1 e2 (eps ρ (el e1 e2 (dirs i)) w) = avgA ρ e1 e2 w := by
  have hne : ∀ i : Fin 4, i + 1 ≠ i := by decide
  have hfix : ρ (el e1 e2 (dirs i)) (eps ρ (el e1 e2 (dirs i)) w) =
      eps ρ (el e1 e2 (dirs i)) w := rho_eps ρ (el_pow_three h _) w
  have h1 := eps_comp ρ h (dirs (i + 1)) (dirs i) (dirs_bij (i + 1) i (hne i))
    (eps ρ (el e1 e2 (dirs i)) w)
  rw [eps_eq_self_of_fixed ρ hV hfix,
    eps_comp ρ h (dirs (i + 1)) (dirs i) (dirs_bij _ _ (hne i)) w] at h1
  exact h1.symm

theorem avgA_avgA (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2) (w : V) :
    avgA ρ e1 e2 (avgA ρ e1 e2 w) = avgA ρ e1 e2 w := by
  have h1 := rho_el_avgA ρ h (1, 0) w
  have h2 := rho_el_avgA ρ h (0, 1) w
  rw [el_10] at h1
  rw [el_01] at h2
  exact avgA_eq_of_fixed ρ hV h1 h2

theorem mem_cen_avgA (ρ : G →* MulAut V) (h : Comm3 e1 e2) (w : V) :
    avgA ρ e1 e2 w ∈ cen ρ e1 e2 := by
  have h1 := rho_el_avgA ρ h (1, 0) w
  have h2 := rho_el_avgA ρ h (0, 1) w
  rw [el_10] at h1
  rw [el_01] at h2
  exact ⟨h1, h2⟩

theorem proj_mem_piece (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2)
    (i : Fin 4) (w : V) :
    proj ρ e1 e2 i w ∈ piece ρ e1 e2 i := by
  refine ⟨?_, ?_⟩
  · change ρ (el e1 e2 (dirs i)) (proj ρ e1 e2 i w) = proj ρ e1 e2 i w
    unfold proj
    rw [(ρ _).map_mul, rho_eps ρ (el_pow_three h _) w, rho_el_avgA ρ h]
  · change avgA ρ e1 e2 (proj ρ e1 e2 i w) = 1
    unfold proj
    rw [avgA_mul, avgA_eps ρ hV h, avgA_avgA ρ hV h, mul_self_eq_one' hV]

theorem spanning (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2) (w : V) :
    ∃ c ∈ cen ρ e1 e2, ∃ p : Fin 4 → V, (∀ i, p i ∈ piece ρ e1 e2 i) ∧ w = c * ∏ i, p i := by
  refine ⟨avgA ρ e1 e2 w, mem_cen_avgA ρ h w, fun i => proj ρ e1 e2 i w,
    fun i => proj_mem_piece ρ hV h i w, ?_⟩
  have h4 : ∏ i : Fin 4, proj ρ e1 e2 i w = (∏ i : Fin 4, eps ρ (el e1 e2 (dirs i)) w) *
      avgA ρ e1 e2 w ^ 4 := by
    unfold proj
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h4, prod_eps_dirs ρ hV h, pow_mul' (avgA ρ e1 e2 w) 2 2, hV, mul_one]
  rw [mul_comm w, ← mul_assoc, mul_self_eq_one' hV, one_mul]

theorem eps_conj (ρ : G →* MulAut V) (c y : G) (w : V) :
    ρ c (eps ρ y w) = eps ρ (c * y * c⁻¹) (ρ c w) := by
  have hy2 : (c * y * c⁻¹) ^ 2 = c * y ^ 2 * c⁻¹ := conj_pow
  simp only [eps, hy2]
  rw [(ρ c).map_mul, (ρ c).map_mul, rho_rho, rho_rho, rho_rho, rho_rho, inv_mul_cancel_right,
    inv_mul_cancel_right]

theorem rho_avgA_conj (ρ : G →* MulAut V) (h : Comm3 e1 e2) {c : G} {m1 m2 : ZMod 3 × ZMod 3}
    (hm : Function.Bijective (fun p : ZMod 3 × ZMod 3 => p.1 • m1 + p.2 • m2))
    (h1 : c * e1 * c⁻¹ = el e1 e2 m1) (h2 : c * e2 * c⁻¹ = el e1 e2 m2) (w : V) :
    ρ c (avgA ρ e1 e2 w) = avgA ρ e1 e2 (ρ c w) := by
  have hb : Function.Bijective (fun p : ZMod 3 × ZMod 3 => p.1 • ((1 : ZMod 3), (0 : ZMod 3)) +
      p.2 • ((0 : ZMod 3), (1 : ZMod 3))) := by decide
  have e : ∀ v : V, avgA ρ e1 e2 v = eps ρ e1 (eps ρ e2 v) := by
    intro v
    have := eps_comp ρ h (1, 0) (0, 1) hb v
    rw [el_10, el_01] at this
    exact this.symm
  rw [e w, e (ρ c w), eps_conj, eps_conj, h1, h2]
  exact (eps_comp ρ h m1 m2 hm (ρ c w)).trans (e (ρ c w))

theorem piece_map (ρ : G →* MulAut V) {c : G}
    (hA : ∀ w, ρ c (avgA ρ e1 e2 w) = avgA ρ e1 e2 (ρ c w)) {i j : Fin 4}
    (hij : c * el e1 e2 (dirs i) * c⁻¹ = el e1 e2 (dirs j) ∨
      c * el e1 e2 (dirs i) * c⁻¹ = (el e1 e2 (dirs j))⁻¹)
    {w : V} (hw : w ∈ piece ρ e1 e2 i) : ρ c w ∈ piece ρ e1 e2 j := by
  refine ⟨?_, ?_⟩
  · have hfix : ρ (c * el e1 e2 (dirs i) * c⁻¹) (ρ c w) = ρ c w := by
      have h0 : ρ (el e1 e2 (dirs i)) w = w := hw.1
      rw [rho_rho, inv_mul_cancel_right, ← rho_rho, h0]
    rcases hij with hij | hij
    · rwa [hij] at hfix
    · rw [hij] at hfix
      have hmem : (el e1 e2 (dirs j))⁻¹ ∈ stab ρ (ρ c w) := hfix
      have := inv_mem hmem
      rw [inv_inv] at this
      exact this
  · have h0 : avgA ρ e1 e2 w = 1 := hw.2
    change avgA ρ e1 e2 (ρ c w) = 1
    rw [← hA, h0, map_one]

theorem card_piece_le [Finite V] (ρ : G →* MulAut V) {c : G}
    (hA : ∀ w, ρ c (avgA ρ e1 e2 w) = avgA ρ e1 e2 (ρ c w)) {i j : Fin 4}
    (hij : c * el e1 e2 (dirs i) * c⁻¹ = el e1 e2 (dirs j) ∨
      c * el e1 e2 (dirs i) * c⁻¹ = (el e1 e2 (dirs j))⁻¹) :
    Nat.card (piece ρ e1 e2 i) ≤ Nat.card (piece ρ e1 e2 j) :=
  Nat.card_le_card_of_injective (fun w => ⟨ρ c w, piece_map ρ hA hij w.2⟩) (by
    intro a b hab
    apply Subtype.ext
    exact (ρ c).injective (congrArg Subtype.val hab))

theorem card_cen_mul_prod_piece_le [Finite V] (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1)
    (h : Comm3 e1 e2) :
    Nat.card (cen ρ e1 e2) * ∏ i, Nat.card (piece ρ e1 e2 i) ≤ Nat.card V := by
  classical
  let f : cen ρ e1 e2 × ((i : Fin 4) → piece ρ e1 e2 i) → V :=
    fun q => q.1.1 * ∏ i, (q.2 i).1
  have hf : Function.Injective f := by
    intro q q' hq
    have hc : q.1.1 * q'.1.1⁻¹ ∈ cen ρ e1 e2 := mul_mem q.1.2 (inv_mem q'.1.2)
    have hp : ∀ i, (q.2 i).1 * ((q'.2 i).1)⁻¹ ∈ piece ρ e1 e2 i :=
      fun i => mul_mem (q.2 i).2 (inv_mem (q'.2 i).2)
    have hq' : q.1.1 * ∏ i, (q.2 i).1 = q'.1.1 * ∏ i, (q'.2 i).1 := hq
    have hprod : (q.1.1 * q'.1.1⁻¹) * ∏ i, ((q.2 i).1 * ((q'.2 i).1)⁻¹) = 1 := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      calc q.1.1 * q'.1.1⁻¹ * ((∏ i, (q.2 i).1) * (∏ i, (q'.2 i).1)⁻¹)
          = (q.1.1 * ∏ i, (q.2 i).1) * (q'.1.1 * ∏ i, (q'.2 i).1)⁻¹ := by
            rw [mul_inv]; ac_rfl
        _ = 1 := by rw [hq', mul_inv_cancel]
    obtain ⟨hc1, hp1⟩ := indep hV h hc hp hprod
    exact Prod.ext (Subtype.ext (mul_inv_eq_one.1 hc1))
      (funext fun i => Subtype.ext (mul_inv_eq_one.1 (hp1 i)))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_pi] at this

theorem piece_fpf (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1) (h : Comm3 e1 e2) {i j : Fin 4}
    (hij : i ≠ j) {w : V} (hw : w ∈ piece ρ e1 e2 i) (hfix : ρ (el e1 e2 (dirs j)) w = w) :
    w = 1 := by
  have hA : avgA ρ e1 e2 w = 1 := hw.2
  have h1 : eps ρ (el e1 e2 (dirs j)) w = w := eps_eq_self_of_fixed ρ hV hfix
  have := eps_comp ρ h (dirs i) (dirs j) (dirs_bij i j hij) w
  rw [h1, eps_eq_self_of_fixed ρ hV hw.1, hA] at this
  exact this

theorem conj_el_comm (h : Comm3 e1 e2) (x y : ZMod 3 × ZMod 3) :
    el e1 e2 x * el e1 e2 y * (el e1 e2 x)⁻¹ = el e1 e2 y := by
  rw [commute_el h x y]
  group

theorem avgA_rho_el (ρ : G →* MulAut V) (h : Comm3 e1 e2) (y : ZMod 3 × ZMod 3) (w : V) :
    avgA ρ e1 e2 (ρ (el e1 e2 y) w) = avgA ρ e1 e2 w := by
  simp only [avgA, rho_rho, ← el_add h]
  exact Fintype.prod_equiv (Equiv.addRight y) _ _ (fun x => rfl)

theorem piece_invariant (ρ : G →* MulAut V) (h : Comm3 e1 e2) (y : ZMod 3 × ZMod 3) {i : Fin 4}
    {w : V} (hw : w ∈ piece ρ e1 e2 i) : ρ (el e1 e2 y) w ∈ piece ρ e1 e2 i :=
  piece_map ρ (fun w => by rw [rho_el_avgA ρ h, avgA_rho_el ρ h])
    (Or.inl (conj_el_comm h y _)) hw

theorem piece_modEq [Finite V] (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1)
    (h : Comm3 e1 e2) (i : Fin 4) : Nat.card (piece ρ e1 e2 i) ≡ 1 [MOD 3] := by
  have hne : ∀ i : Fin 4, i ≠ i + 1 := by decide
  refine card_modEq_one ρ (y := el e1 e2 (dirs (i + 1))) (el_pow_three h _) _
    (fun w hw => piece_invariant ρ h _ hw) (fun w hw hfix => piece_fpf ρ hV h (hne i) hw hfix)

theorem piece_eq_bot_or_four_le [Finite V] (ρ : G →* MulAut V) (hV : ∀ v : V, v ^ 2 = 1)
    (h : Comm3 e1 e2) (i : Fin 4) :
    piece ρ e1 e2 i = ⊥ ∨ 4 ≤ Nat.card (piece ρ e1 e2 i) :=
  eq_bot_or_four_le (piece_modEq ρ hV h i)

end Pieces

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
