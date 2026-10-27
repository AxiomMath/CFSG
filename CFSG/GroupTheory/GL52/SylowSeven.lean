module

public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.GroupTheory.GL52.Simple
public import Mathlib.Tactic.NormNum.Prime

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix
open scoped Pointwise

@[expose] def sig7M : M5 :=
  !![0, 0, 1, 0, 0; 1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def phi7M : M5 :=
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def syl7W : Fin 3 → V5 :=
  ![Pi.single 3 1, Pi.single 4 1, Pi.single 3 1 + Pi.single 4 1]

@[expose] def syl7PermM (p : Equiv.Perm (Fin 3)) : M5 :=
  colMat ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, syl7W (p 0), syl7W (p 1)]

set_option maxRecDepth 100000 in
theorem syl7_facts : sig7M ^ 7 = 1 ∧ sig7M * sig7M ^ 6 = 1 ∧ sig7M ≠ 1 ∧ phi7M ^ 3 = 1 ∧
    phi7M * phi7M ^ 2 = 1 ∧ phi7M ≠ 1 ∧ phi7M * sig7M = sig7M ^ 2 * phi7M ∧
    phi7M ^ 2 * sig7M = sig7M ^ 4 * phi7M ^ 2 ∧ phi7M * sig7M ≠ sig7M * phi7M ∧
    phi7M ^ 2 * sig7M ≠ sig7M * phi7M ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem syl7_minpoly : ∀ k : Fin 7,
    (sig7M ^ (k : ℕ)) ^ 4 + (sig7M ^ (k : ℕ)) ^ 3 + (sig7M ^ (k : ℕ)) ^ 2 + 1 = 0 →
      (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 ∨ (k : ℕ) = 4 := by
  decide +kernel

theorem syl7_poly : sig7M ^ 4 + sig7M ^ 3 + sig7M ^ 2 + 1 = 0 := by
  decide +kernel

theorem syl7_vectors :
    sig7M *ᵥ Pi.single 0 1 = Pi.single 1 1 ∧ sig7M *ᵥ Pi.single 1 1 = Pi.single 2 1 ∧
    (∀ v : V5, (sig7M ^ 3 + sig7M + 1) *ᵥ v = 0 → v 3 = 0 ∧ v 4 = 0) ∧
    (∀ v : V5, (sig7M + 1) *ᵥ v = 0 → v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) ∧
    (sig7M ^ 3 + sig7M + 1) *ᵥ Pi.single 0 1 = 0 ∧ (sig7M + 1) *ᵥ Pi.single 3 1 = 0 ∧
    (sig7M + 1) *ᵥ Pi.single 4 1 = 0 ∧
    (∀ v : V5, v 0 = 0 → v 1 = 0 → v 2 = 0 → sig7M *ᵥ v = v) ∧
    (∀ m : Fin 7, sig7M ^ (m : ℕ) *ᵥ Pi.single 0 1 = Pi.single 0 1 → (m : ℕ) = 0) := by
  decide +kernel

theorem syl7_sig_orbit : ∀ v : V5, v ≠ 0 → v 3 = 0 → v 4 = 0 →
    ∃ m : Fin 7, sig7M ^ (m : ℕ) *ᵥ Pi.single 0 1 = v := by
  decide +kernel

theorem syl7_perm_facts :
    (∀ p : Equiv.Perm (Fin 3), syl7PermM p * syl7PermM p⁻¹ = 1) ∧
    (∀ p q : Equiv.Perm (Fin 3), syl7PermM (p * q) = syl7PermM p * syl7PermM q) ∧
    syl7PermM 1 = 1 ∧
    (∀ p q : Equiv.Perm (Fin 3), syl7PermM p = syl7PermM q → p = q) ∧
    (∀ p : Equiv.Perm (Fin 3), syl7PermM p * sig7M = sig7M * syl7PermM p) ∧
    (∀ p : Equiv.Perm (Fin 3), syl7PermM p * phi7M = phi7M * syl7PermM p) ∧
    (∀ p : Equiv.Perm (Fin 3), syl7PermM p *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      syl7PermM p *ᵥ Pi.single 1 1 = Pi.single 1 1 ∧
      syl7PermM p *ᵥ Pi.single 2 1 = Pi.single 2 1) := by
  decide +kernel

theorem syl7_W_cover : ∀ x y : ZMod 2, ¬ (x = 0 ∧ y = 0) →
    ∃ i : Fin 3, syl7W i = ![0, 0, 0, x, y] := by
  decide +kernel

theorem syl7_perm_exists : ∀ i j : Fin 3, i ≠ j → ∃ p : Equiv.Perm (Fin 3), p 0 = i ∧ p 1 = j := by
  decide

theorem syl7PermM_mulVec (p : Equiv.Perm (Fin 3)) :
    syl7PermM p *ᵥ Pi.single 3 1 = syl7W (p 0) ∧ syl7PermM p *ᵥ Pi.single 4 1 = syl7W (p 1) :=
  ⟨colMat_mulVec_single _ 3, colMat_mulVec_single _ 4⟩

theorem syl7_perm_cover (x y x' y' : ZMod 2) (h : ¬ (x = 0 ∧ y = 0)) (h' : ¬ (x' = 0 ∧ y' = 0))
    (hne : ¬ (x = x' ∧ y = y')) : ∃ p : Equiv.Perm (Fin 3),
      syl7PermM p *ᵥ Pi.single 3 1 = ![0, 0, 0, x, y] ∧
      syl7PermM p *ᵥ Pi.single 4 1 = ![0, 0, 0, x', y'] := by
  obtain ⟨i, hi⟩ := syl7_W_cover x y h
  obtain ⟨j, hj⟩ := syl7_W_cover x' y' h'
  have hij : i ≠ j := by
    rintro rfl
    rw [hi] at hj
    exact hne ⟨congrFun hj 3, congrFun hj 4⟩
  obtain ⟨p, hp0, hp1⟩ := syl7_perm_exists i j hij
  refine ⟨p, ?_, ?_⟩
  · rw [(syl7PermM_mulVec p).1, hp0, hi]
  · rw [(syl7PermM_mulVec p).2, hp1, hj]

@[expose] def sig7 : G52 :=
  mk5 sig7M (sig7M ^ 6) syl7_facts.2.1

@[expose] def phi7 : G52 :=
  mk5 phi7M (phi7M ^ 2) syl7_facts.2.2.2.2.1

@[expose] def syl7PermHom : Equiv.Perm (Fin 3) →* G52 where
  toFun p := mk5 (syl7PermM p) (syl7PermM p⁻¹) (syl7_perm_facts.1 p)
  map_one' := Units.ext syl7_perm_facts.2.2.1
  map_mul' p q := Units.ext (syl7_perm_facts.2.1 p q)

theorem syl7PermHom_injective : Function.Injective syl7PermHom := fun p q h =>
  syl7_perm_facts.2.2.2.1 p q (congrArg (fun g : G52 => (g : M5)) h)

@[expose] def syl7X : Subgroup G52 :=
  syl7PermHom.range

theorem orderOf_sig7 : orderOf sig7 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => syl7_facts.2.2.1 ?_
  · rw [Units.val_pow_eq_pow_val, sig7, coe_mk5, Units.val_one]
    exact syl7_facts.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [sig7] using this

theorem orderOf_phi7 : orderOf phi7 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => syl7_facts.2.2.2.2.2.1 ?_
  · rw [Units.val_pow_eq_pow_val, phi7, coe_mk5, Units.val_one]
    exact syl7_facts.2.2.2.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [phi7] using this

theorem syl7_card_X : Nat.card syl7X = 6 := by
  rw [syl7X, ← Nat.card_congr (MonoidHom.ofInjective syl7PermHom_injective).toEquiv,
    Nat.card_perm, Nat.card_fin]
  rfl

theorem syl7_eq_of_commute {A B : M5} (hA : A * sig7M = sig7M * A) (hB : B * sig7M = sig7M * B)
    (h0 : A *ᵥ Pi.single 0 1 = B *ᵥ Pi.single 0 1) (h3 : A *ᵥ Pi.single 3 1 = B *ᵥ Pi.single 3 1)
    (h4 : A *ᵥ Pi.single 4 1 = B *ᵥ Pi.single 4 1) : A = B := by
  obtain ⟨v1, v2, -⟩ := syl7_vectors
  have e1 : A *ᵥ Pi.single 1 1 = B *ᵥ Pi.single 1 1 := by
    rw [← v1, mulVec_comm hA, mulVec_comm hB, h0]
  have e2 : A *ᵥ Pi.single 2 1 = B *ᵥ Pi.single 2 1 := by
    rw [← v2, mulVec_comm hA, mulVec_comm hB, e1]
  refine ext_cols fun j => ?_
  fin_cases j
  exacts [h0, e1, e2, h3, h4]

theorem syl7_matrix_commute {g : G52} (hg : g ∈ Subgroup.centralizer {sig7}) :
    (g : M5) * sig7M = sig7M * (g : M5) := by
  have := congrArg (fun x : G52 => (x : M5)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [sig7] using this

theorem syl7_columns {g : G52} (hg : g ∈ Subgroup.centralizer {sig7}) :
    (((g : M5) *ᵥ Pi.single 0 1) 3 = 0 ∧ ((g : M5) *ᵥ Pi.single 0 1) 4 = 0) ∧
    (((g : M5) *ᵥ Pi.single 3 1) 0 = 0 ∧ ((g : M5) *ᵥ Pi.single 3 1) 1 = 0 ∧
      ((g : M5) *ᵥ Pi.single 3 1) 2 = 0) ∧
    (((g : M5) *ᵥ Pi.single 4 1) 0 = 0 ∧ ((g : M5) *ᵥ Pi.single 4 1) 1 = 0 ∧
      ((g : M5) *ᵥ Pi.single 4 1) 2 = 0) := by
  have hc := syl7_matrix_commute hg
  obtain ⟨-, -, kU, kW, h0, h3, h4, -⟩ := syl7_vectors
  have hp : ∀ n : ℕ, (g : M5) * sig7M ^ n = sig7M ^ n * (g : M5) := fun n =>
    (Commute.pow_right hc n).eq
  have hc3 : (g : M5) * (sig7M ^ 3 + sig7M + 1) = (sig7M ^ 3 + sig7M + 1) * (g : M5) := by
    simp only [mul_add, add_mul, hp, mul_one, one_mul, hc]
  have hc1 : (g : M5) * (sig7M + 1) = (sig7M + 1) * (g : M5) := by
    simp only [mul_add, add_mul, mul_one, one_mul, hc]
  refine ⟨kU _ ?_, kW _ ?_, kW _ ?_⟩
  · rw [← mulVec_comm hc3, h0, mulVec_zero]
  · rw [← mulVec_comm hc1, h3, mulVec_zero]
  · rw [← mulVec_comm hc1, h4, mulVec_zero]

theorem syl7_eq_W {v : V5} (h0 : v 0 = 0) (h1 : v 1 = 0) (h2 : v 2 = 0) :
    v = ![0, 0, 0, v 3, v 4] := by
  funext i
  fin_cases i <;> simp [h0, h1, h2]

theorem syl7_centralizer_cover {g : G52} (hg : g ∈ Subgroup.centralizer {sig7}) :
    ∃ m < 7, (sig7 ^ m)⁻¹ * g ∈ syl7X := by
  obtain ⟨⟨a3, a4⟩, ⟨b0, b1, b2⟩, ⟨c0, c1, c2⟩⟩ := syl7_columns hg
  obtain ⟨-, -, -, -, -, -, -, hfixW, -⟩ := syl7_vectors
  have he0 : (Pi.single 0 1 : V5) ≠ 0 := by decide
  obtain ⟨m, hm⟩ := syl7_sig_orbit _ (fun h => he0 (eq_zero_of_mulVec_eq_zero g h)) a3 a4
  have hb : (g : M5) *ᵥ Pi.single 3 1 = ![0, 0, 0, ((g : M5) *ᵥ Pi.single 3 1) 3,
      ((g : M5) *ᵥ Pi.single 3 1) 4] := syl7_eq_W b0 b1 b2
  have hc : (g : M5) *ᵥ Pi.single 4 1 = ![0, 0, 0, ((g : M5) *ᵥ Pi.single 4 1) 3,
      ((g : M5) *ᵥ Pi.single 4 1) 4] := syl7_eq_W c0 c1 c2
  have hne3 : ¬ (((g : M5) *ᵥ Pi.single 3 1) 3 = 0 ∧ ((g : M5) *ᵥ Pi.single 3 1) 4 = 0) := by
    rintro ⟨h1, h2⟩
    have hz : (g : M5) *ᵥ Pi.single 3 1 = 0 := by
      rw [hb, h1, h2]
      decide
    exact (by decide : (Pi.single 3 1 : V5) ≠ 0) (eq_zero_of_mulVec_eq_zero g hz)
  have hne4 : ¬ (((g : M5) *ᵥ Pi.single 4 1) 3 = 0 ∧ ((g : M5) *ᵥ Pi.single 4 1) 4 = 0) := by
    rintro ⟨h1, h2⟩
    have hz : (g : M5) *ᵥ Pi.single 4 1 = 0 := by
      rw [hc, h1, h2]
      decide
    exact (by decide : (Pi.single 4 1 : V5) ≠ 0) (eq_zero_of_mulVec_eq_zero g hz)
  have hne34 : ¬ (((g : M5) *ᵥ Pi.single 3 1) 3 = ((g : M5) *ᵥ Pi.single 4 1) 3 ∧
      ((g : M5) *ᵥ Pi.single 3 1) 4 = ((g : M5) *ᵥ Pi.single 4 1) 4) := by
    rintro ⟨h1, h2⟩
    have hz : (g : M5) *ᵥ (Pi.single 3 1 + Pi.single 4 1) = 0 := by
      rw [mulVec_add, hb, hc, h1, h2]
      funext i
      fin_cases i <;> simp [CharTwo.add_self_eq_zero]
    exact (by decide : (Pi.single 3 1 + Pi.single 4 1 : V5) ≠ 0)
      (eq_zero_of_mulVec_eq_zero g hz)
  obtain ⟨p, hp3, hp4⟩ := syl7_perm_cover _ _ _ _ hne3 hne4 hne34
  refine ⟨m, m.2, ⟨p, ?_⟩⟩
  have hσp : ((sig7 ^ (m : ℕ) * syl7PermHom p : G52) : M5) = sig7M ^ (m : ℕ) * syl7PermM p := by
    simp [syl7PermHom, sig7, Units.val_pow_eq_pow_val]
  have hfixWm : ∀ v : V5, v 0 = 0 → v 1 = 0 → v 2 = 0 → sig7M ^ (m : ℕ) *ᵥ v = v := by
    intro v h0 h1 h2
    induction (m : ℕ) with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mulVec_mulVec, hfixW v h0 h1 h2, ih]
  have heq : sig7 ^ (m : ℕ) * syl7PermHom p = g := by
    refine Units.ext ?_
    rw [hσp]
    obtain ⟨-, -, -, -, -, -, hpe⟩ := syl7_perm_facts
    obtain ⟨hpe0, -, -⟩ := hpe p
    refine syl7_eq_of_commute ?_ (syl7_matrix_commute hg) ?_ ?_ ?_
    · rw [mul_assoc, syl7_perm_facts.2.2.2.2.1 p, ← mul_assoc, ← pow_succ, ← mul_assoc,
        ← pow_succ']
    · rw [← mulVec_mulVec, hpe0, hm]
    · rw [← mulVec_mulVec, hp3, hb]
      exact hfixWm _ rfl rfl rfl
    · rw [← mulVec_mulVec, hp4, hc]
      exact hfixWm _ rfl rfl rfl
  rw [← heq, inv_mul_cancel_left]

theorem syl7_X_le_centralizer : syl7X ≤ Subgroup.centralizer {sig7} := by
  rintro _ ⟨p, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Units.ext (syl7_perm_facts.2.2.2.2.1 p)

theorem syl7_disj_sig (m : ℕ) (hm : m < 7) (h : sig7 ^ m ∈ syl7X) : m = 0 := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, hm0⟩ := syl7_vectors
  refine hm0 ⟨m, hm⟩ ?_
  have e := congrArg (fun g : G52 => (g : M5) *ᵥ Pi.single 0 1) hp
  simp only [syl7PermHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_mk5,
    Units.val_pow_eq_pow_val, sig7] at e
  rw [← e]
  exact (syl7_perm_facts.2.2.2.2.2.2 p).1

theorem syl7_card_centralizer : Nat.card (Subgroup.centralizer {sig7}) = 42 := by
  have hsig : sig7 ∈ Subgroup.centralizer {sig7} := Subgroup.mem_centralizer_singleton_iff.2 rfl
  rw [card_eq_mul_of_cosets syl7_X_le_centralizer hsig (fun g hg => syl7_centralizer_cover hg)
    syl7_disj_sig, syl7_card_X]

theorem syl7_centralizer_le_normalizer :
    Subgroup.centralizer {sig7} ≤ Subgroup.normalizer (Subgroup.zpowers sig7 : Set G52) := by
  intro g hg
  refine mem_normalizer_zpowers_of_conj_mem ?_
  rw [Subgroup.mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
  exact Subgroup.mem_zpowers sig7

theorem syl7_phi_conj : phi7 * sig7 * phi7⁻¹ = sig7 ^ 2 := by
  have h : phi7 * sig7 = sig7 ^ 2 * phi7 := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, phi7, sig7, coe_mk5]
    exact syl7_facts.2.2.2.2.2.2.1
  rw [h, mul_inv_cancel_right]

theorem syl7_phi_mem_normalizer :
    phi7 ∈ Subgroup.normalizer (Subgroup.zpowers sig7 : Set G52) :=
  mem_normalizer_zpowers_of_conj_mem
    (syl7_phi_conj ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers sig7) 2)

theorem syl7_cover {g : G52} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers sig7 : Set G52)) :
    ∃ j < 3, (phi7 ^ j)⁻¹ * g ∈ Subgroup.centralizer {sig7} := by
  classical
  have hmem : g * sig7 * g⁻¹ ∈ Subgroup.zpowers sig7 :=
    (Subgroup.mem_normalizer_iff.1 hg sig7).1 (Subgroup.mem_zpowers sig7)
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_sig7] at hmem
  obtain ⟨k, hk, hgk⟩ := Finset.mem_image.1 hmem
  rw [Finset.mem_range] at hk
  have hroot : (sig7M ^ k) ^ 4 + (sig7M ^ k) ^ 3 + (sig7M ^ k) ^ 2 + 1 = 0 := by
    have e : (sig7M ^ k : M5) = (g : M5) * sig7M * ((g⁻¹ : G52) : M5) := by
      have := congrArg (fun x : G52 => (x : M5)) hgk
      simpa [sig7] using this
    have hgg : ((g⁻¹ : G52) : M5) * (g : M5) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hpow : ∀ n : ℕ, ((g : M5) * sig7M * ((g⁻¹ : G52) : M5)) ^ n =
        (g : M5) * sig7M ^ n * ((g⁻¹ : G52) : M5) := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      | succ n ih =>
        rw [pow_succ, ih, pow_succ]
        calc (g : M5) * sig7M ^ n * ((g⁻¹ : G52) : M5) * ((g : M5) * sig7M * ((g⁻¹ : G52) : M5))
            = (g : M5) * sig7M ^ n * (((g⁻¹ : G52) : M5) * (g : M5)) * sig7M *
                ((g⁻¹ : G52) : M5) := by noncomm_ring
          _ = _ := by rw [hgg, mul_one, mul_assoc (g : M5)]
    have hone' : (g : M5) * ((g⁻¹ : G52) : M5) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have key : (g : M5) * (sig7M ^ 4 + sig7M ^ 3 + sig7M ^ 2 + 1) * ((g⁻¹ : G52) : M5) = 0 := by
      rw [syl7_poly, mul_zero, zero_mul]
    rw [e, hpow, hpow, hpow, ← key, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul,
      mul_one, hone']
  have hk' := syl7_minpoly ⟨k, hk⟩ hroot
  have hconj : ∀ j : ℕ, phi7 ^ j * sig7 = sig7 ^ k * phi7 ^ j →
      (phi7 ^ j)⁻¹ * g ∈ Subgroup.centralizer {sig7} := by
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgs : g * sig7 = sig7 ^ k * g := by rw [hgk, inv_mul_cancel_right]
    calc (phi7 ^ j)⁻¹ * g * sig7 = (phi7 ^ j)⁻¹ * (sig7 ^ k * g) := by rw [mul_assoc, hgs]
      _ = (phi7 ^ j)⁻¹ * (phi7 ^ j * sig7 * (phi7 ^ j)⁻¹ * g) := by
          rw [hj, mul_inv_cancel_right]
      _ = sig7 * ((phi7 ^ j)⁻¹ * g) := by group
  have hφ1 : phi7 ^ 1 * sig7 = sig7 ^ 2 * phi7 ^ 1 := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, phi7, sig7, coe_mk5, pow_one]
    exact syl7_facts.2.2.2.2.2.2.1
  have hφ2 : phi7 ^ 2 * sig7 = sig7 ^ 4 * phi7 ^ 2 := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, phi7, sig7, coe_mk5]
    exact syl7_facts.2.2.2.2.2.2.2.1
  simp only at hk'
  rcases hk' with h | h | h | h
  · exfalso
    rw [h, pow_zero] at hgk
    have : sig7 = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) hgk
      simpa [mul_assoc] using this.symm
    have h7 := orderOf_sig7
    rw [this, orderOf_one] at h7
    norm_num at h7
  · exact ⟨0, by norm_num, hconj 0 (by rw [h]; simp)⟩
  · exact ⟨1, by norm_num, hconj 1 (by rw [h]; exact hφ1)⟩
  · exact ⟨2, by norm_num, hconj 2 (by rw [h]; exact hφ2)⟩

theorem syl7_disj_phi (j : ℕ) (hj : j < 3) (h : phi7 ^ j ∈ Subgroup.centralizer {sig7}) :
    j = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  have e := congrArg (fun x : G52 => (x : M5)) h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, phi7, sig7, coe_mk5] at e
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · rfl
  · rw [pow_one] at e
    exact absurd e syl7_facts.2.2.2.2.2.2.2.2.1
  · exact absurd e syl7_facts.2.2.2.2.2.2.2.2.2

theorem syl7_card_normalizer :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers sig7 : Set G52)) = 126 := by
  rw [card_eq_mul_of_cosets syl7_centralizer_le_normalizer syl7_phi_mem_normalizer
    (fun g hg => syl7_cover hg) syl7_disj_phi, syl7_card_centralizer]

@[expose] def syl7Y : Subgroup G52 :=
  Subgroup.zpowers sig7 ⊔ Subgroup.zpowers phi7

theorem syl7_card_zpowers : Nat.card (Subgroup.zpowers sig7) = 7 := by
  rw [Nat.card_zpowers, orderOf_sig7]

theorem syl7_card_zpowers_phi : Nat.card (Subgroup.zpowers phi7) = 3 := by
  rw [Nat.card_zpowers, orderOf_phi7]

theorem syl7_inf : Subgroup.zpowers sig7 ⊓ Subgroup.zpowers phi7 = ⊥ := by
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [syl7_card_zpowers, syl7_card_zpowers_phi]
  norm_num

theorem syl7_Y_le_normalizer :
    syl7Y ≤ Subgroup.normalizer (Subgroup.zpowers sig7 : Set G52) :=
  sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 syl7_phi_mem_normalizer)

theorem syl7_card_Y : Nat.card syl7Y = 21 := by
  classical
  have hcover : ∀ y ∈ syl7Y, ∃ j < 3, (phi7 ^ j)⁻¹ * y ∈ Subgroup.zpowers sig7 := by
    intro y hy
    have hmul : ((Subgroup.zpowers phi7 ⊔ Subgroup.zpowers sig7 : Subgroup G52) : Set G52) =
        (Subgroup.zpowers phi7 : Set G52) * (Subgroup.zpowers sig7 : Set G52) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _
        ((Subgroup.zpowers_le).2 syl7_phi_mem_normalizer)
    have hy' : y ∈ ((Subgroup.zpowers phi7 ⊔ Subgroup.zpowers sig7 : Subgroup G52) : Set G52) := by
      rw [sup_comm]
      exact hy
    rw [hmul] at hy'
    obtain ⟨r, hr, k, hk, rfl⟩ := hy'
    rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_phi7] at hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr
    refine ⟨j, Finset.mem_range.1 hj, ?_⟩
    rw [inv_mul_cancel_left]
    exact hk
  have hdisj : ∀ j < 3, phi7 ^ j ∈ Subgroup.zpowers sig7 → j = 0 := by
    intro j hj h
    have h1 : phi7 ^ j ∈ Subgroup.zpowers sig7 ⊓ Subgroup.zpowers phi7 :=
      Subgroup.mem_inf.2 ⟨h, Subgroup.pow_mem _ (Subgroup.mem_zpowers phi7) j⟩
    rw [syl7_inf, Subgroup.mem_bot] at h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_phi7] at this
    omega
  have hphiY : phi7 ∈ syl7Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers phi7)
  rw [card_eq_mul_of_cosets (N := syl7Y) le_sup_left hphiY hcover hdisj, syl7_card_zpowers]

theorem syl7_frobenius_data :
    Subgroup.zpowers sig7 ≤ syl7Y ∧ Subgroup.zpowers phi7 ≤ syl7Y ∧
    syl7Y ≤ Subgroup.normalizer (Subgroup.zpowers sig7 : Set G52) ∧
    Subgroup.zpowers sig7 ⊓ Subgroup.zpowers phi7 = ⊥ ∧
    Subgroup.zpowers sig7 ⊔ Subgroup.zpowers phi7 = syl7Y ∧
    (∀ r ∈ Subgroup.zpowers phi7, r ≠ 1 → ∀ k ∈ Subgroup.zpowers sig7, k ≠ 1 →
      r * k * r⁻¹ ≠ k) ∧
    Subgroup.zpowers sig7 ≠ ⊥ ∧ Subgroup.zpowers phi7 ≠ ⊥ := by
  classical
  refine ⟨le_sup_left, le_sup_right, syl7_Y_le_normalizer, syl7_inf, rfl, ?_, ?_, ?_⟩
  · intro r hr hr1 k hk hk1 hfix
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hgen : (⟨sig7, Subgroup.mem_zpowers sig7⟩ : Subgroup.zpowers sig7) ∈
        Subgroup.zpowers (⟨k, hk⟩ : Subgroup.zpowers sig7) :=
      mem_zpowers_of_prime_card syl7_card_zpowers (fun h => hk1 (congrArg Subtype.val h))
    obtain ⟨m, hm⟩ := hgen
    have hm' : k ^ m = sig7 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hcomm : r * sig7 = sig7 * r := by
      have e : r * k = k * r := by
        calc r * k = r * k * r⁻¹ * r := by group
          _ = k * r := by rw [hfix]
      rw [← hm']
      exact (Commute.zpow_right e m).eq
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_phi7] at hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr
    have hj0 := syl7_disj_phi j (Finset.mem_range.1 hj)
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
    rw [hj0, pow_zero] at hr1
    exact hr1 rfl
  · rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    have := orderOf_sig7
    rw [h, orderOf_one] at this
    norm_num at this
  · rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    have := orderOf_phi7
    rw [h, orderOf_one] at this
    norm_num at this

theorem syl7_X_le_fix : syl7X ≤ fixSub {Pi.single 0 1, Pi.single 1 1, Pi.single 2 1} := by
  rintro _ ⟨p, rfl⟩ v hv
  obtain ⟨h0, h1, h2⟩ := syl7_perm_facts.2.2.2.2.2.2 p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  exacts [h0, h1, h2]

theorem syl7_Y_le_fix : syl7Y ≤ fixSub {Pi.single 3 1, Pi.single 4 1} := by
  have hs : sig7 ∈ fixSub {Pi.single 3 1, Pi.single 4 1} := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl <;> decide
  have hp : phi7 ∈ fixSub {Pi.single 3 1, Pi.single 4 1} := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl <;> decide
  exact sup_le ((Subgroup.zpowers_le).2 hs) ((Subgroup.zpowers_le).2 hp)

theorem syl7_X_inf_Y : syl7X ⊓ syl7Y = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hX, hY⟩ := Subgroup.mem_inf.1 hg
  have h1 := syl7_X_le_fix hX
  have h2 := syl7_Y_le_fix hY
  rw [Subgroup.mem_bot]
  refine Units.ext (ext_cols fun j => ?_)
  rw [Units.val_one, one_mulVec]
  fin_cases j
  · exact h1 _ (by simp)
  · exact h1 _ (by simp)
  · exact h1 _ (by simp)
  · exact h2 _ (by simp)
  · exact h2 _ (by simp)

theorem syl7_X_commute_Y : ∀ x ∈ syl7X, ∀ y ∈ syl7Y, x * y = y * x := by
  rintro _ ⟨p, rfl⟩ y hy
  have hs : sig7 ∈ Subgroup.centralizer {syl7PermHom p} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Units.ext (syl7_perm_facts.2.2.2.2.1 p)).symm
  have hp : phi7 ∈ Subgroup.centralizer {syl7PermHom p} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Units.ext (syl7_perm_facts.2.2.2.2.2.1 p)).symm
  have hle : syl7Y ≤ Subgroup.centralizer {syl7PermHom p} :=
    sup_le ((Subgroup.zpowers_le).2 hs) ((Subgroup.zpowers_le).2 hp)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem syl7_normalizer_eq :
    syl7X ⊔ syl7Y = Subgroup.normalizer (Subgroup.zpowers sig7 : Set G52) := by
  refine le_antisymm (sup_le (syl7_X_le_centralizer.trans syl7_centralizer_le_normalizer)
    syl7_Y_le_normalizer) fun g hg => ?_
  obtain ⟨j, -, hj⟩ := syl7_cover hg
  obtain ⟨m, -, hm⟩ := syl7_centralizer_cover hj
  have e : g = (phi7 ^ j * sig7 ^ m) * ((sig7 ^ m)⁻¹ * ((phi7 ^ j)⁻¹ * g)) := by group
  rw [e]
  refine mul_mem (Subgroup.mem_sup_right (mul_mem ?_ ?_)) (Subgroup.mem_sup_left hm)
  · exact Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers phi7) j)
  · exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers sig7) m)

theorem syl7_card_sylow (P : Sylow 7 G52) : Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact card_sylow_of_card_eq_prime_mul (m := 1428480) (by rw [card_G52]; norm_num)
    (by norm_num) P

theorem syl7_structure (S : Sylow 7 G52) :
    Nat.card (Subgroup.normalizer (S : Set G52)) = 126 ∧
    ∃ X Y : Subgroup G52, IsInnerDirectProduct X Y (Subgroup.normalizer (S : Set G52)) ∧
      Nonempty (X ≃* Equiv.Perm (Fin 3)) ∧ Nat.card Y = 21 ∧ IsFrobeniusSubgroup Y := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card syl7_card_zpowers syl7_card_sylow
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q S
  rw [hQ] at hc
  have hS : ((S : Set G52)) = ((S : Subgroup G52) : Set G52) := rfl
  rw [hS, hc, normalizer_map_conj]
  set f := (MulAut.conj c).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj c).injective
  obtain ⟨hKY, hRY, hnorm, hinf, hsup, hfpf, hK, hR⟩ := syl7_frobenius_data
  refine ⟨by rw [Subgroup.card_map_of_injective hinj, syl7_card_normalizer],
    syl7X.map f, syl7Y.map f, ⟨?_, ?_, ?_⟩, ⟨?_⟩, ?_,
    isFrobeniusSubgroup_map_conj c hKY hRY hnorm hinf hsup hfpf hK hR⟩
  · rw [← Subgroup.map_sup, syl7_normalizer_eq]
  · rw [← Subgroup.map_inf_eq _ _ _ hinj, syl7_X_inf_Y, Subgroup.map_bot]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, syl7_X_commute_Y x hx y hy]
  · exact (Subgroup.equivMapOfInjective syl7X f hinj).symm.trans
      ((MonoidHom.ofInjective syl7PermHom_injective).symm)
  · rw [Subgroup.card_map_of_injective hinj, syl7_card_Y]

end CFSG.GroupTheory.GL52
