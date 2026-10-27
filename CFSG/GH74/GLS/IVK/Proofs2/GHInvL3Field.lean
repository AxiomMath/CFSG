module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

open Polynomial Matrix

namespace CFSG.GH74.GLS.IVK.GHInv

theorem charP_of_natCard_eq_prime_pow {F : Type*} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf0 : f ≠ 0) : CharP F p := by
  have := Fintype.ofFinite F
  rw [CharP.charP_iff_prime_eq_zero hp]
  have h1 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hFc, Nat.cast_pow] at h1
  exact (pow_eq_zero_iff hf0).mp h1

theorem pow_eq_one_of_mulVec_eq_smul {K : Type*} [Field K] {n : Type*} [Fintype n]
    [DecidableEq n] {N : Matrix n n K} {ℓ : ℕ} (hN : N ^ ℓ = 1) {ζ : K} {v : n → K}
    (hv : v ≠ 0) (hNv : N *ᵥ v = ζ • v) : ζ ^ ℓ = 1 := by
  have key : ∀ k : ℕ, (N ^ k) *ᵥ v = ζ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have h1 := key ℓ
  rw [hN, Matrix.one_mulVec] at h1
  by_contra hne
  have h2 : (ζ ^ ℓ - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact hne (sub_eq_zero.mp h3)
  · exact hv h3

theorem isRoot_charpoly_iff_exists_mulVec_eq_smul {K : Type*} [Field K] {n : Type*}
    [Fintype n] [DecidableEq n] (N : Matrix n n K) (ζ : K) :
    N.charpoly.IsRoot ζ ↔ ∃ v : n → K, v ≠ 0 ∧ N *ᵥ v = ζ • v := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, sub_eq_zero, eq_comm, Matrix.scalar_apply]
  simp

theorem pow_char_pow_eq_one_of_isRoot_charpoly {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (N : Matrix (Fin 3) (Fin 3) K) {a : ℕ} (ha : 3 ≤ p ^ a)
    (hroots : ∀ ζ, N.charpoly.IsRoot ζ → ζ = 1) : N ^ (p ^ a) = 1 := by
  have hmon := N.charpoly_monic
  have hdeg : N.charpoly.natDegree = 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : Multiset.card N.charpoly.roots = N.charpoly.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hrep : N.charpoly.roots = Multiset.replicate 3 1 :=
    Multiset.eq_replicate.mpr
      ⟨hcard.trans hdeg, fun b hb => hroots b ((mem_roots hmon.ne_zero).mp hb)⟩
  have hχ : N.charpoly = (X - C 1) ^ 3 := by
    conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard, hrep,
      Multiset.map_replicate, Multiset.prod_replicate]
  have hdvd : N.charpoly ∣ X ^ (p ^ a) - 1 := by
    rw [hχ]
    have h1 : (X - C (1 : K)) ^ (p ^ a) = X ^ (p ^ a) - 1 := by
      rw [sub_pow_char_pow, ← C_pow, one_pow, C_1]
    rw [← h1]
    exact pow_dvd_pow _ ha
  have h2 := aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (Matrix.aeval_self_charpoly N)
  simpa [sub_eq_zero] using h2

theorem false_of_pow_closed {K : Type*} [Field K] [DecidableEq K] {S : Finset K}
    (hS : S.card ≤ 3) {ℓ r : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ r * r + 1)
    (hclosed : ∀ x ∈ S, x ^ r ∈ S) {ζ : K} (hζS : ζ ∈ S) (hζℓ : ζ ^ ℓ = 1) (hζ1 : ζ ≠ 1) :
    False := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hord : orderOf ζ = ℓ := orderOf_eq_prime hζℓ hζ1
  have hmem : ∀ i, ζ ^ (r ^ i) ∈ S := by
    intro i
    induction i with
    | zero => simpa using hζS
    | succ i ih => rw [pow_succ, pow_mul]; exact hclosed _ ih
  have hx2 : (r : ZMod ℓ) * r + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (r * r + 1) ℓ).mpr hdvd
    push_cast at this
    exact this
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h')
  have hfin : IsOfFinOrder ζ := orderOf_pos_iff.mp (hord ▸ hℓ.pos)
  have hinj : ∀ i < 4, ∀ j < 4, ζ ^ (r ^ i) = ζ ^ (r ^ j) → i = j := by
    intro i hi j hj hij
    rw [hfin.pow_eq_pow_iff_modEq, hord, ← ZMod.natCast_eq_natCast_iff] at hij
    push_cast at hij
    interval_cases i <;> interval_cases j <;> first | rfl | (exfalso; grind)
  have := Finset.le_card_of_inj_on_range (fun i => ζ ^ (r ^ i)) (fun i _ => hmem i) hinj
  omega

theorem no_ell_element_commuting_field {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hFc : Nat.card F = p ^ f) (hfe : Even f) (hf0 : f ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hdvd : ℓ ∣ p ^ f + 1) (M : Matrix (Fin 3) (Fin 3) F) (hMℓ : M ^ ℓ = 1) (hM1 : M ≠ 1)
    (A : Matrix (Fin 3) (Fin 3) F) (hA : IsUnit A) (c : F) (hc : c ^ 3 = 1)
    (h : A * M.map (fun a => a ^ (p ^ (f / 2))) = c • (M * A)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hFc hf0
  set r := p ^ (f / 2) with hr_def
  have hrr : r * r = p ^ f := by
    rw [hr_def, ← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := hfe
    omega
  have hdvd' : ℓ ∣ r * r + 1 := hrr ▸ hdvd
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  set ι : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  set Φ : AlgebraicClosure F →+* AlgebraicClosure F := iterateFrobenius _ p (f / 2)
  have hΦ : ∀ x, Φ x = x ^ r := fun x => iterateFrobenius_def p (f / 2) x
  set N : Matrix (Fin 3) (Fin 3) (AlgebraicClosure F) := M.map ι with hN_def
  have hNℓ : N ^ ℓ = 1 := by
    rw [hN_def, ← Matrix.map_pow, hMℓ, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hN' : (M.map (fun a => a ^ r)).map ι = N.map Φ := by
    ext i j
    simp [hN_def, hΦ, map_pow]
  have hAN : A.map ι * N.map Φ = ι c • (N * A.map ι) := by
    have h' := congrArg (fun X => X.map ι) h
    rw [Matrix.map_mul, hN'] at h'
    rw [h', hN_def, ← Matrix.map_mul (f := ι)]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  obtain ⟨B, hB⟩ := hA.exists_left_inv
  have hBA : B.map ι * A.map ι = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hc3 : ι c ^ 3 = 1 := by rw [← map_pow, hc, map_one]
  have hc0 : ι c ≠ 0 := by
    rintro h0
    rw [h0, zero_pow three_ne_zero] at hc3
    exact zero_ne_one hc3
  have step2 : ∀ ζ, N.charpoly.IsRoot ζ → N.charpoly.IsRoot ((ι c)⁻¹ * ζ ^ r) := by
    intro ζ hζ
    rw [isRoot_charpoly_iff_exists_mulVec_eq_smul] at hζ ⊢
    obtain ⟨v, hv, hNv⟩ := hζ
    refine ⟨A.map ι *ᵥ (Φ ∘ v), ?_, ?_⟩
    · intro h0
      apply hv
      have hw : B.map ι *ᵥ (A.map ι *ᵥ (Φ ∘ v)) = Φ ∘ v := by
        rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at hw
      funext i
      have hi := congrFun hw i
      simp only [Pi.zero_apply, Function.comp_apply] at hi
      exact (map_eq_zero Φ).mp hi.symm
    · have hw : N.map Φ *ᵥ (Φ ∘ v) = Φ ζ • (Φ ∘ v) := by
        funext i
        rw [← RingHom.map_mulVec, hNv]
        simp
      have h1 : ι c • (N *ᵥ (A.map ι *ᵥ (Φ ∘ v))) = Φ ζ • (A.map ι *ᵥ (Φ ∘ v)) := by
        rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← hAN, ← Matrix.mulVec_mulVec, hw,
          Matrix.mulVec_smul]
      rw [hΦ] at h1
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hrootℓ : ∀ ξ, N.charpoly.IsRoot ξ → ξ ^ ℓ = 1 := by
    intro ξ hξ
    obtain ⟨v, hv, hNv⟩ := (isRoot_charpoly_iff_exists_mulVec_eq_smul N ξ).mp hξ
    exact pow_eq_one_of_mulVec_eq_smul hNℓ hv hNv
  have hr2 : 2 ≤ r := by
    have h1 : 1 ≤ f / 2 := by
      obtain ⟨k, hk⟩ := hfe
      omega
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ r := Nat.pow_le_pow_right hp.pos h1
  have hq3 : 3 ≤ p ^ f := by
    rw [← hrr]
    nlinarith
  have hcop : Nat.Coprime ℓ (p ^ f) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_primes hℓ hp]
    rintro rfl
    have h1 : ℓ ∣ 1 := (Nat.dvd_add_right (dvd_pow_self ℓ hf0)).mp hdvd
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨ζ, hζroot, hζ1⟩ : ∃ ζ, N.charpoly.IsRoot ζ ∧ ζ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hNq : N ^ (p ^ f) = 1 := pow_char_pow_eq_one_of_isRoot_charpoly N hq3 hcon
    have hN1 : N ^ (Nat.gcd ℓ (p ^ f)) = 1 := pow_gcd_eq_one.mpr ⟨hNℓ, hNq⟩
    rw [hcop.gcd_eq_one, pow_one, hN_def,
      ← Matrix.map_one (n := Fin 3) ι (map_zero ι) (map_one ι)] at hN1
    exact hM1 (Matrix.map_injective ι.injective hN1)
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h3 := (ZMod.natCast_eq_zero_iff (r * r + 1) 3).mpr hdvd'
    push_cast at h3
    generalize (r : ZMod 3) = x at h3
    revert x
    decide
  have hc1 : ι c = 1 := by
    have h1 := hrootℓ _ (step2 ζ hζroot)
    rw [mul_pow, ← pow_mul, mul_comm r ℓ, pow_mul, hrootℓ ζ hζroot, one_pow, mul_one, inv_pow,
      inv_eq_one] at h1
    have h2 := pow_gcd_eq_one.mpr ⟨h1, hc3⟩
    rwa [((Nat.coprime_primes hℓ Nat.prime_three).mpr hℓ3).gcd_eq_one, pow_one] at h2
  have hne : N.charpoly ≠ 0 := N.charpoly_monic.ne_zero
  have hS : N.charpoly.roots.toFinset.card ≤ 3 := by
    calc N.charpoly.roots.toFinset.card ≤ Multiset.card N.charpoly.roots :=
          Multiset.toFinset_card_le _
      _ ≤ N.charpoly.natDegree := Polynomial.card_roots' _
      _ = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  refine false_of_pow_closed hS hℓ hℓ2 hdvd' (fun x hx => ?_) ?_ (hrootℓ ζ hζroot) hζ1
  · rw [Multiset.mem_toFinset, mem_roots hne] at hx ⊢
    have h1 := step2 x hx
    rwa [hc1, inv_one, one_mul] at h1
  · rw [Multiset.mem_toFinset, mem_roots hne]
    exact hζroot

end CFSG.GH74.GLS.IVK.GHInv
