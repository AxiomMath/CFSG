module

public import CFSG.LocalAnalysis.Mason73.Fusion34c
public import CFSG.LocalAnalysis.Mason73.Powers
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup
open scoped commutatorElement

variable {n : ℕ}

abbrev red2 (hn : 1 ≤ n) : ZMod (2 ^ n) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 (by omega)) (ZMod 2)

theorem red2_hh (hn : 2 ≤ n) : red2 (by omega) (hh n) = 0 := by
  rw [hh, map_natCast, ZMod.natCast_eq_zero_iff]
  exact dvd_pow_self 2 (by omega)

theorem red2_sgnH (hn : 2 ≤ n) (π : Fin81.R0) : red2 (by omega) (sgnH (n := n) π) = 0 := by
  rcases Int.units_eq_one_or (Perm.sign (π : Perm (Fin 4))) with h | h
  · rw [sgnH_even h, map_zero]
  · rw [sgnH_swap (by omega) h, red2_hh hn]

theorem red2_sum_of_detSum (hn : 2 ≤ n) {e : Fin 4 → ZMod (2 ^ n)} {σ : Fin81.R0}
    (h : detSum e σ) : red2 (by omega) (e 0 + e 1 + e 2 + e 3) = 0 := by
  have h' : e 0 + e 1 + e 2 + e 3 = -sgnH σ := by
    rw [detSum, Fin.sum_univ_four] at h
    linear_combination h
  rw [h', map_neg, red2_sgnH hn, neg_zero]

theorem red2_pv_add (hn : 2 ≤ n) {e : Fin 4 → ZMod (2 ^ n)} {σ : Fin81.R0} (h : detSum e σ)
    (π : Fin81.R0) :
    red2 (by omega) (pv (π : Perm (Fin 4)) e 0 + pv (π : Perm (Fin 4)) e 1) =
      red2 (by omega) (e 0 + e 1) := by
  have key : ∀ π : Fin81.R0, ((π : Perm (Fin 4))⁻¹ 0 = 0 ∧ (π : Perm (Fin 4))⁻¹ 1 = 1) ∨
      ((π : Perm (Fin 4))⁻¹ 0 = 1 ∧ (π : Perm (Fin 4))⁻¹ 1 = 0) ∨
      ((π : Perm (Fin 4))⁻¹ 0 = 2 ∧ (π : Perm (Fin 4))⁻¹ 1 = 3) ∨
      ((π : Perm (Fin 4))⁻¹ 0 = 3 ∧ (π : Perm (Fin 4))⁻¹ 1 = 2) := by
    decide
  have hs := red2_sum_of_detSum hn h
  have h23 : red2 (n := n) (by omega) (e 2 + e 3) = red2 (by omega) (e 0 + e 1) := by
    have : e 2 + e 3 = (e 0 + e 1 + e 2 + e 3) - (e 0 + e 1) := by ring
    rw [this, map_sub, hs, zero_sub, ZMod.neg_eq_self_mod_two]
  simp only [pv]
  rcases key π with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
  · rw [add_comm]
  · exact h23
  · rw [add_comm]
    exact h23

@[expose] def xParityP (hn : 2 ≤ n) : L4P n →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (red2 (by omega)
      (Multiplicative.toAdd (a : L4Hat n).left 0 + Multiplicative.toAdd (a : L4Hat n).left 1)))
    (fun a b => by
      have hb : detSum (Multiplicative.toAdd (b : L4Hat n).left) (b : L4Hat n).right :=
        hat_mem_L4P.1 (by rw [hat_left]; exact b.2)
      have h := red2_pv_add hn hb (a : L4Hat n).right
      simp only [pv] at h
      rw [← ofAdd_add]
      congr 1
      change red2 (by omega) ((Multiplicative.toAdd (a : L4Hat n).left 0 +
          Multiplicative.toAdd (actL4 n (a : L4Hat n).right (b : L4Hat n).left) 0) +
        (Multiplicative.toAdd (a : L4Hat n).left 1 +
          Multiplicative.toAdd (actL4 n (a : L4Hat n).right (b : L4Hat n).left) 1)) = _
      rw [toAdd_actL4, toAdd_actL4, ← h]
      simp only [map_add]
      ring)

theorem zpowers_cL4_le_ker_xParityP (hn : 2 ≤ n) :
    Subgroup.zpowers (cL4 n) ≤ (xParityP hn).ker := by
  rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
  change Multiplicative.ofAdd (red2 (by omega) (zL4 n + zL4 n)) = 1
  rw [← two_mul, two_mul_zL4 hn, red2_hh hn, ofAdd_zero]

@[expose] def xParity (hn : 2 ≤ n) : L4Model n →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ (xParityP hn) (zpowers_cL4_le_ker_xParityP hn)

theorem xParity_el (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) :
    xParity hn (el d π h) = Multiplicative.ofAdd (red2 (by omega) (d 0 + d 1)) := rfl

theorem xParity_xT (hn : 2 ≤ n) : xParity hn (xT n) = Multiplicative.ofAdd 1 := by
  rw [xT, xParity_el]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_zero, map_one]

theorem xParity_xT_zpow (hn : 2 ≤ n) (m : ℤ) :
    xParity hn (xT n ^ m) = Multiplicative.ofAdd (m : ZMod 2) := by
  rw [map_zpow, xParity_xT, ← ofAdd_zsmul, zsmul_eq_mul, mul_one]

theorem eq_ofAdd_one_of_ne_one : ∀ q : Multiplicative (ZMod 2), q ≠ 1 →
    q = Multiplicative.ofAdd 1 := by
  decide

theorem ofAdd_one_ne_one_zmod2 : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
  decide

theorem xParity_hv (hn : 2 ≤ n) {χ : Fin 4 → ℕ} {π : Fin81.R0} (h : detSum (hv n χ) π) :
    xParity hn (el (hv n χ) π h) = 1 := by
  rw [xParity_el]
  simp only [hv]
  rw [← mul_add, map_mul, red2_hh hn, zero_mul, ofAdd_zero]

theorem xParity_uT (hn : 2 ≤ n) : xParity hn (uT (n := n) (by omega)) = 1 := xParity_hv hn _
theorem xParity_tT (hn : 2 ≤ n) : xParity hn (tT (n := n) (by omega)) = 1 := xParity_hv hn _
theorem xParity_uvT (hn : 2 ≤ n) : xParity hn (uvT (n := n) (by omega)) = 1 := xParity_hv hn _

theorem xParity_txT (hn : 2 ≤ n) : xParity hn (txT n) = Multiplicative.ofAdd 1 := by
  rw [txT, xParity_el]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_zero, map_neg,
    map_one]
  rfl

theorem uvT_mem_commutator (hn : 2 ≤ n) : uvT (n := n) (by omega) ∈ commutator (L4Model n) := by
  have hu : (uT (n := n) (by omega))⁻¹ = uT (by omega) :=
    inv_eq_of_mul_eq_one_right (uT_mul_self hn)
  have ht : (tT (n := n) (by omega))⁻¹ = tT (by omega) :=
    inv_eq_of_mul_eq_one_right (tT_mul_self hn)
  have h : ⁅uT (n := n) (by omega), tT (n := n) (by omega)⁆ = uvT (by omega) := by
    rw [commutatorElement_def, hu, ht]
    calc uT (n := n) (by omega) * tT (by omega) * uT (by omega) * tT (by omega) =
        uT (by omega) * (tT (by omega) * uT (by omega) * tT (by omega)) := by group
      _ = uvT (by omega) := by rw [tT_mul_uT_mul_tT hn, uT_mul_vT hn]
  rw [← h, _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem detSum_sub_pv {e : Fin 4 → ZMod (2 ^ n)} (he : detSum e 1) (τ : Perm (Fin 4)) :
    detSum (e - pv τ e) 1 := by
  rw [detSum_one_iff] at he ⊢
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib, sum_pv, sub_self]

theorem el_sub_pv_mem_commutator (hn : 2 ≤ n) {e f : Fin 4 → ZMod (2 ^ n)} {τ : Fin81.R0}
    (he : detSum e 1) (hf : detSum f τ) :
    el (e - pv (τ : Perm (Fin 4)) e) 1 (detSum_sub_pv he _) ∈ commutator (L4Model n) := by
  have h := commutatorElement_el hn he hf (by rw [one_mul, mul_one])
  have heq : el (e - pv (τ : Perm (Fin 4)) e) 1 (detSum_sub_pv he _) = ⁅el e 1 he, el f τ hf⁆ := by
    rw [h]
    refine el_congr _ _ ?_ rfl
    rw [OneMemClass.coe_one, pv_one]
    abel
  rw [heq, _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem red2_two (hn : 1 ≤ n) : red2 (n := n) hn 2 = 0 := by
  rw [show (2 : ZMod (2 ^ n)) = ((2 : ℕ) : ZMod (2 ^ n)) by norm_num, map_natCast]
  rfl

theorem el_one_mem_commutator (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1)
    (hd : red2 (by omega) (d 0 + d 1) = 0) : el d 1 h ∈ commutator (L4Model n) := by
  obtain ⟨α, hα⟩ : ∃ α : ZMod (2 ^ n), d 0 - d 1 = 2 * α := by
    obtain ⟨k, hk | hk⟩ := exists_eq_two_mul_or (d 0 - d 1)
    · exact ⟨k, hk⟩
    · exfalso
      have h1 : red2 (n := n) (by omega) (d 0 - d 1) = 1 := by
        rw [hk, map_add, map_mul, red2_two, zero_mul, zero_add, map_one]
      have h2 : red2 (n := n) (by omega) (d 0 - d 1) = 0 := by
        rw [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, ← map_add, hd]
      rw [h1] at h2
      exact absurd h2 (by decide)
  have hsum := detSum_one_iff.1 h
  rw [Fin.sum_univ_four] at hsum
  obtain ⟨γ, hγ⟩ : ∃ γ : ZMod (2 ^ n), γ = d 0 - α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ZMod (2 ^ n), β = d 2 + γ := ⟨_, rfl⟩
  have he₁ : detSum (![α, 0, 0, -α] : Fin 4 → ZMod (2 ^ n)) 1 := by
    rw [detSum_one_iff, Fin.sum_univ_four]
    simp
  have he₂ : detSum (![-β, 0, β, 0] : Fin 4 → ZMod (2 ^ n)) 1 := by
    rw [detSum_one_iff, Fin.sum_univ_four]
    simp
  have he₃ : detSum (![γ, 0, 0, -γ] : Fin 4 → ZMod (2 ^ n)) 1 := by
    rw [detSum_one_iff, Fin.sum_univ_four]
    simp
  have c₁ := el_sub_pv_mem_commutator (by omega) he₁
    (detSum_hv_odd (n := n) (χ := ![0, 0, 1, 0]) (by omega) (sgnH_s01 (by omega)) (by decide))
  have c₂ := el_sub_pv_mem_commutator (by omega) he₂
    (detSum_hv_odd (n := n) (χ := ![1, 0, 0, 0]) (by omega) (sgnH_s23 (by omega)) (by decide))
  have c₃ := el_sub_pv_mem_commutator (by omega) he₃
    (detSum_hv_even (n := n) (χ := ![0, 0, 0, 0]) (π := tP) (by omega) (by decide) (by decide))
  have hprod := mul_mem (mul_mem c₁ c₂) c₃
  rw [el_mul, el_mul] at hprod
  convert hprod using 1
  refine el_congr _ _ ?_ (by rw [mul_one, mul_one])
  simp only [mul_one, OneMemClass.coe_one, pv_one]
  rw [pv_s01, pv_s23, pv_tP]
  funext i
  fin_cases i
  · simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val, Fin.zero_eta]
    linear_combination -hγ
  · simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val, Fin.mk_one]
    linear_combination -hα - hγ
  · simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val, Fin.reduceFinMk]
    linear_combination -hβ
  · simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val, Fin.reduceFinMk]
    linear_combination hsum + hβ + 2 * hγ + hα

theorem mem_commutator_of_xParity (hn : 3 ≤ n) {g : L4Model n} (hg : xParity (by omega) g = 1)
    (hπ : piT g = 1 ∨ piT g = zP) : g ∈ commutator (L4Model n) := by
  have hdiag : ∀ g : L4Model n, xParity (by omega) g = 1 → piT g = 1 →
      g ∈ commutator (L4Model n) := by
    intro g hg hπ
    obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
    rw [piT_el] at hπ
    subst hπ
    rw [xParity_el] at hg
    exact el_one_mem_commutator hn h (by simpa using hg)
  rcases hπ with hπ | hπ
  · exact hdiag g hg hπ
  · have h1 : (uvT (n := n) (by omega))⁻¹ * g ∈ commutator (L4Model n) := by
      refine hdiag _ ?_ ?_
      · rw [map_mul, map_inv, xParity_uvT, inv_one, one_mul, hg]
      · rw [map_mul, map_inv, hπ, piT_uvT]
        decide
    have := mul_mem (uvT_mem_commutator (by omega)) h1
    rwa [mul_inv_cancel_left] at this

theorem el_pow_two_pow_pred (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) (hπ : π * π = 1) :
    ∃ h' : detSum (fun i => zL4 n * (d i + pv (π : Perm (Fin 4)) d i)) 1,
      el d π h ^ 2 ^ (n - 1) = el (fun i => zL4 n * (d i + pv (π : Perm (Fin 4)) d i)) 1 h' := by
  have hsq : el d π h ^ 2 = el (d + pv (π : Perm (Fin 4)) d) 1 (hπ ▸ detSum_mul h h) := by
    rw [pow_two, el_mul]
    exact el_congr _ _ rfl hπ
  have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨?_, ?_⟩
  · have := detSum_nsmul (hπ ▸ detSum_mul h h : detSum (d + pv (π : Perm (Fin 4)) d) 1)
      (2 ^ (n - 2))
    convert this using 1
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul]
  · rw [h2, pow_mul, hsq, el_one_pow]
    refine el_congr _ _ ?_ rfl
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul]

theorem pow_eq_one_iff_and_pow_eq_zT_iff (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) (hπ : π * π = 1) :
    (el d π h ^ 2 ^ (n - 1) = 1 ↔
      IsConst (fun i => zL4 n * (d i + pv (π : Perm (Fin 4)) d i))) ∧
    (el d π h ^ 2 ^ (n - 1) = zT (by omega) ↔
      IsConst (hv n χz - fun i => zL4 n * (d i + pv (π : Perm (Fin 4)) d i))) := by
  obtain ⟨h', hP⟩ := el_pow_two_pow_pred (by omega) h hπ
  rw [hP]
  constructor
  · rw [← el_zero_one, el_eq_el_iff (by omega), zero_sub, isConst_neg_iff]
    simp
  · rw [zT_eq, el_eq_el_iff (by omega)]
    simp

abbrev red4 (hn : 2 ≤ n) : ZMod (2 ^ n) →+* ZMod 4 :=
  ZMod.castHom (by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hn) (ZMod 4)

theorem zL4_mul_natCast_eq_iff (hn : 2 ≤ n) (x y : ℕ) :
    zL4 n * (x : ZMod (2 ^ n)) = zL4 n * (y : ZMod (2 ^ n)) ↔ (x : ZMod 4) = (y : ZMod 4) := by
  have h4 : 2 ^ n = 2 ^ (n - 2) * 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [zL4, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff', h4,
    Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mul_right_inj (by positivity),
    ZMod.natCast_eq_natCast_iff']

theorem zL4_mul_eq_iff (hn : 2 ≤ n) (a b : ZMod (2 ^ n)) :
    zL4 n * a = zL4 n * b ↔ red4 hn a = red4 hn b := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, zL4_mul_natCast_eq_iff hn,
    map_natCast, map_natCast]

theorem hh_eq_zL4_mul_two (hn : 2 ≤ n) : hh n = zL4 n * 2 := by
  rw [mul_comm, two_mul_zL4 hn]

theorem red4_hh (hn : 3 ≤ n) : red4 (by omega) (hh n) = 0 := by
  rw [hh, map_natCast, ZMod.natCast_eq_zero_iff, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact pow_dvd_pow 2 (by omega)

theorem red4_sgnH (hn : 3 ≤ n) (π : Fin81.R0) : red4 (by omega) (sgnH (n := n) π) = 0 := by
  rcases Int.units_eq_one_or (Perm.sign (π : Perm (Fin 4))) with h | h
  · rw [sgnH_even h, map_zero]
  · rw [sgnH_swap (by omega) h, red4_hh hn]

theorem red2_eq_red4 (hn : 2 ≤ n) (a : ZMod (2 ^ n)) :
    red2 (by omega) a = ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (red4 hn a) := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  rw [← ZMod.natCast_zmod_val a, map_natCast, map_natCast, map_natCast]

theorem parity_check : ∀ π ∈ ({1, s01, s23, zP} : Finset Fin81.R0),
    ∀ (a₀ a₁ a₂ a₃ : ZMod 4) (e : ZMod 2), a₀ + a₁ + a₂ + a₃ = 0 →
    ((∀ i j, ![a₀, a₁, a₂, a₃] i + ![a₀, a₁, a₂, a₃] ((π : Perm (Fin 4))⁻¹ i) =
      ![a₀, a₁, a₂, a₃] j + ![a₀, a₁, a₂, a₃] ((π : Perm (Fin 4))⁻¹ j)) ↔ e = 0) →
    ¬ (∀ i j, 2 * ((χz i : ℕ) : ZMod 4) -
        (![a₀, a₁, a₂, a₃] i + ![a₀, a₁, a₂, a₃] ((π : Perm (Fin 4))⁻¹ i)) =
      2 * ((χz j : ℕ) : ZMod 4) -
        (![a₀, a₁, a₂, a₃] j + ![a₀, a₁, a₂, a₃] ((π : Perm (Fin 4))⁻¹ j))) →
    ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (a₀ + a₁) = e := by
  decide

theorem mem_finset_of_mem_V1 {π : Fin81.R0} (hπ : π ∈ V1) :
    π ∈ ({1, s01, s23, zP} : Finset Fin81.R0) := by
  have key : ∀ π : Fin81.R0, π ∈ V1 → π ∈ ({1, s01, s23, zP} : Finset Fin81.R0) := by
    decide
  exact key π hπ

theorem piT_mul_self_of_mem_V1 : ∀ π ∈ (V1 : Subgroup Fin81.R0), π * π = 1 := by
  decide

theorem xParity_eq_of_piT_mem_V1 (hn : 3 ≤ n) {b : L4Model n} (hb : piT b ∈ V1) (e : ZMod 2)
    (h1 : b ^ 2 ^ (n - 1) = 1 ↔ e = 0) (hz : b ^ 2 ^ (n - 1) ≠ zT (by omega)) :
    xParity (by omega) b = Multiplicative.ofAdd e := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el b
  rw [piT_el] at hb
  obtain ⟨hP1, hPz⟩ := pow_eq_one_iff_and_pow_eq_zT_iff hn h (piT_mul_self_of_mem_V1 π hb)
  set a : Fin 4 → ZMod 4 := fun i => red4 (by omega) (d i) with ha
  have hc : IsConst (fun i => zL4 n * (d i + pv (π : Perm (Fin 4)) d i)) ↔
      ∀ i j, a i + a ((π : Perm (Fin 4))⁻¹ i) = a j + a ((π : Perm (Fin 4))⁻¹ j) := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    change zL4 n * (d i + _) = zL4 n * (d j + _) ↔ _
    rw [zL4_mul_eq_iff (by omega), map_add, map_add]
  have hcz : IsConst (hv n χz - fun i => zL4 n * (d i + pv (π : Perm (Fin 4)) d i)) ↔
      ∀ i j, 2 * ((χz i : ℕ) : ZMod 4) - (a i + a ((π : Perm (Fin 4))⁻¹ i)) =
        2 * ((χz j : ℕ) : ZMod 4) - (a j + a ((π : Perm (Fin 4))⁻¹ j)) := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [Pi.sub_apply, hv]
    rw [hh_eq_zL4_mul_two (by omega), mul_assoc, mul_assoc, ← mul_sub, ← mul_sub,
      zL4_mul_eq_iff (by omega)]
    simp only [map_sub, map_mul, map_add, map_natCast, map_ofNat, ha, pv]
  have hsum : a 0 + a 1 + a 2 + a 3 = 0 := by
    have hd : d 0 + d 1 + d 2 + d 3 = -sgnH π := by
      rw [detSum, Fin.sum_univ_four] at h
      linear_combination h
    have := congrArg (red4 (n := n) (by omega)) hd
    simp only [map_add, map_neg, red4_sgnH hn, neg_zero] at this
    exact this
  have haeq : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [xParity_el, red2_eq_red4 (by omega), map_add]
  congr 1
  rw [haeq] at hsum hc hcz
  exact parity_check π (mem_finset_of_mem_V1 hb) (a 0) (a 1) (a 2) (a 3) e (by simpa using hsum)
    ((hc.symm.trans hP1.symm).trans h1) fun hw => hz (hPz.2 (hcz.2 hw))

end CFSG.LocalAnalysis.Mason73
