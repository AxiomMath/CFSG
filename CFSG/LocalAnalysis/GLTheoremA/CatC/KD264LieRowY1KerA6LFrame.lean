module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LIdem
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix

variable {K : Type} [Field K]

theorem sum6_blocks {M : Type} [AddCommMonoid M] (F : Fin 6 → M) :
    ∑ j, F j = ∑ a : Fin 4, F (ia a) + ∑ b : Fin 2, F (ib b) := by
  rw [← e6.sum_comp F, Fintype.sum_sum_type]
  rfl

@[expose] def ext6 (v : Fin 4 → K) : Fin 6 → K := fun j =>
  if h : j.val < 4 then v ⟨j.val, h⟩ else 0

theorem ext6_ia (v : Fin 4 → K) (a : Fin 4) : ext6 v (ia a) = v a := by
  unfold ext6 ia
  simp

theorem ext6_ib (v : Fin 4 → K) (b : Fin 2) : ext6 v (ib b) = 0 := by
  unfold ext6 ib
  simp

theorem blk6_mulVec_ext (M : Matrix (Fin 4) (Fin 4) K) (N : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 4 → K) : blk6 M N *ᵥ ext6 v = ext6 (M *ᵥ v) := by
  funext i
  obtain ⟨x, rfl⟩ := e6.surjective i
  rcases x with a | b
  · show (blk6 M N *ᵥ ext6 v) (ia a) = ext6 (M *ᵥ v) (ia a)
    rw [ext6_ia]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum6_blocks]
    simp [ext6_ia, ext6_ib, blk6_ia_ia, blk6_ia_ib, Matrix.mulVec, dotProduct]
  · show (blk6 M N *ᵥ ext6 v) (ib b) = ext6 (M *ᵥ v) (ib b)
    rw [ext6_ib]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum6_blocks]
    simp [ext6_ia, ext6_ib, blk6_ib_ia, blk6_ib_ib]

theorem diag_fix_ext (v : Fin 4 → K) :
    Matrix.diagonal (fun i : Fin 6 => if (i : ℕ) < 4 then (1 : K) else 0) *ᵥ ext6 v = ext6 v := by
  funext j
  simp only [Matrix.mulVec_diagonal]
  unfold ext6
  split_ifs <;> simp

theorem quad_of_cube {T : Matrix (Fin 4) (Fin 4) K} (h3 : T ^ 3 = 1)
    (hfix : ∀ v : Fin 4 → K, T *ᵥ v = v → v = 0) : T * T + T + 1 = 0 := by
  have hprod : (T - 1) * (T * T + T + 1) = 0 := by
    have h : (T - 1) * (T * T + T + 1) = T ^ 3 - 1 := by
      rw [pow_three']
      noncomm_ring
    rw [h, h3, sub_self]
  have hzero : ∀ y : Fin 4 → K, (T * T + T + 1) *ᵥ y = 0 := by
    intro y
    have hx : (T - 1) *ᵥ ((T * T + T + 1) *ᵥ y) = 0 := by
      rw [Matrix.mulVec_mulVec, hprod, Matrix.zero_mulVec]
    have hTx : T *ᵥ ((T * T + T + 1) *ᵥ y) = (T * T + T + 1) *ᵥ y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hx
      exact sub_eq_zero.mp hx
    exact hfix _ hTx
  ext i j
  have h := congrFun (hzero (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using h

theorem blk6_pow3 (M : Matrix (Fin 4) (Fin 4) K) (N : Matrix (Fin 2) (Fin 2) K) :
    (blk6 M N) ^ 3 = blk6 (M ^ 3) (N ^ 3) := by
  rw [pow_three', pow_three', pow_three', blk6_mul, blk6_mul]

theorem blk6_fst_inj {M M' : Matrix (Fin 4) (Fin 4) K} {N N' : Matrix (Fin 2) (Fin 2) K}
    (h : blk6 M N = blk6 M' N') : M = M' := by
  ext a b
  have := congrFun (congrFun h (ia a)) (ia b)
  rwa [blk6_ia_ia, blk6_ia_ia] at this

theorem ia_inj' (a b : Fin 4) : ia a = ia b ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (by simpa [ia] using congrArg Fin.val h)
  · intro h; rw [h]

theorem ib_inj' (a b : Fin 2) : ib a = ib b ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (by simpa [ib] using congrArg Fin.val h)
  · intro h; rw [h]

theorem diag_eq_blk6 :
    Matrix.diagonal (fun i : Fin 6 => if (i : ℕ) < 4 then (1 : K) else 0) =
      blk6 (1 : Matrix (Fin 4) (Fin 4) K) (0 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  obtain ⟨x, rfl⟩ := e6.surjective i
  obtain ⟨y, rfl⟩ := e6.surjective j
  rcases x with a | a <;> rcases y with b | b
  · rw [show e6 (Sum.inl a) = ia a from rfl, show e6 (Sum.inl b) = ia b from rfl, blk6_ia_ia,
      Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp [ia]
    · have h' : ia a ≠ ia b := fun h2 => h ((ia_inj' a b).mp h2)
      rw [Matrix.diagonal_apply_ne _ h', if_neg h]
  · rw [show e6 (Sum.inl a) = ia a from rfl, show e6 (Sum.inr b) = ib b from rfl, blk6_ia_ib]
    have h' : ia a ≠ ib b := by
      intro h2
      have := congrArg Fin.val h2
      simp [ia, ib] at this
      omega
    rw [Matrix.diagonal_apply_ne _ h']
  · rw [show e6 (Sum.inr a) = ib a from rfl, show e6 (Sum.inl b) = ia b from rfl, blk6_ib_ia]
    have h' : ib a ≠ ia b := by
      intro h2
      have := congrArg Fin.val h2
      simp [ia, ib] at this
      omega
    rw [Matrix.diagonal_apply_ne _ h']
  · rw [show e6 (Sum.inr a) = ib a from rfl, show e6 (Sum.inr b) = ib b from rfl, blk6_ib_ib]
    have h' : ib a ≠ ib b ∨ a = b := by
      by_cases h : a = b
      · exact Or.inr h
      · exact Or.inl (fun h2 => h ((ib_inj' a b).mp h2))
    rcases h' with h' | h'
    · rw [Matrix.diagonal_apply_ne _ (fun h2 => h' h2)]
      simp [ib]
    · subst h'
      simp [ib]

theorem frame6 (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) (g t e : Matrix (Fin 6) (Fin 6) K)
    (he : e * e = e) (her : e.rank = 4) (hge : g * e = e) (heg : e * g = e)
    (hte : t * e = e * t) (ht3 : t ^ 3 = 1)
    (hfix : ∀ v : Fin 6 → K, e *ᵥ v = v → t *ᵥ v = v → v = 0) :
    ∃ S : Matrix.GeneralLinearGroup (Fin 6) K, ∃ G T2 : Matrix (Fin 2) (Fin 2) K,
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * g *
        (S : Matrix (Fin 6) (Fin 6) K) = blk6 1 G ∧
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * t *
        (S : Matrix (Fin 6) (Fin 6) K) = blk6 (D4 K) T2 ∧
      ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * e *
        (S : Matrix (Fin 6) (Fin 6) K) = blk6 1 0 := by
  classical
  obtain ⟨A, hA⟩ := exists_idem_normal e he her
  obtain ⟨a, ha⟩ : ∃ a : Matrix (Fin 6) (Fin 6) K, a = (A : Matrix (Fin 6) (Fin 6) K) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : Matrix (Fin 6) (Fin 6) K,
      a' = ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := ⟨_, rfl⟩
  have haa' : a * a' = 1 := by rw [ha, ha']; exact Units.mul_inv A
  have ha'a : a' * a = 1 := by rw [ha, ha']; exact Units.inv_mul A
  obtain ⟨E0, hE0⟩ : ∃ E0 : Matrix (Fin 6) (Fin 6) K,
      E0 = Matrix.diagonal (fun i : Fin 6 => if (i : ℕ) < 4 then (1 : K) else 0) := ⟨_, rfl⟩
  have hconjE : a * e * a' = E0 := by rw [ha, ha', hE0]; exact hA
  have hconj : ∀ x y : Matrix (Fin 6) (Fin 6) K,
      (a * x * a') * (a * y * a') = a * (x * y) * a' := by
    intro x y
    rw [show (a * x * a') * (a * y * a') = a * x * (a' * a) * y * a' by
      simp only [Matrix.mul_assoc], ha'a]
    simp only [Matrix.mul_assoc, Matrix.mul_one]
  have he_eq : e = a' * E0 * a := by
    rw [← hconjE]
    rw [show a' * (a * e * a') * a = (a' * a) * e * (a' * a) by simp only [Matrix.mul_assoc],
      ha'a, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨g0, hg0⟩ : ∃ g0 : Matrix (Fin 6) (Fin 6) K, g0 = a * g * a' := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0 : Matrix (Fin 6) (Fin 6) K, t0 = a * t * a' := ⟨_, rfl⟩
  have ht_eq : t = a' * t0 * a := by
    rw [ht0, show a' * (a * t * a') * a = (a' * a) * t * (a' * a) by simp only [Matrix.mul_assoc],
      ha'a, Matrix.one_mul, Matrix.mul_one]
  have hg0E : g0 * E0 = E0 := by rw [← hconjE, hg0, hconj, hge]
  have hE0g : E0 * g0 = E0 := by rw [← hconjE, hg0, hconj, heg]
  have ht0E : t0 * E0 = E0 * t0 := by rw [← hconjE, ht0, hconj, hconj, hte]
  have hfix0 : ∀ w : Fin 6 → K, E0 *ᵥ w = w → t0 *ᵥ w = w → w = 0 := by
    intro w hEw htw
    have hv : ∀ x : Fin 6 → K, a *ᵥ (a' *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
    have hev : e *ᵥ (a' *ᵥ w) = a' *ᵥ w := by
      rw [he_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, hEw]
    have htv : t *ᵥ (a' *ᵥ w) = a' *ᵥ w := by
      rw [ht_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, htw]
    have h0 := hfix (a' *ᵥ w) hev htv
    have hw : w = a *ᵥ (a' *ᵥ w) := (hv w).symm
    rw [hw, h0, Matrix.mulVec_zero]
  have ht0cube : t0 ^ 3 = 1 := by
    rw [ht0, pow_three', hconj, hconj, ← pow_three', ht3, mul_one]
    exact haa'
  have hL : ∀ M : Matrix (Fin 6) (Fin 6) K,
      E0 * M = fun (i j : Fin 6) => (if (i : ℕ) < 4 then (1 : K) else 0) * M i j := by
    intro M
    ext i j
    rw [hE0]
    simp [Matrix.diagonal_mul]
  have hR : ∀ M : Matrix (Fin 6) (Fin 6) K,
      M * E0 = fun (i j : Fin 6) => M i j * (if (j : ℕ) < 4 then (1 : K) else 0) := by
    intro M
    ext i j
    rw [hE0]
    simp [Matrix.mul_diagonal]
  have E0_entry : ∀ i j : Fin 6, E0 i j = if i = j then (if (i : ℕ) < 4 then (1 : K) else 0)
      else 0 := by
    intro i j
    rw [hE0, Matrix.diagonal_apply]
  have hne_ia_ib : ∀ (a : Fin 4) (b : Fin 2), ia a ≠ ib b := by
    intro a b h
    have := congrArg Fin.val h
    simp [ia, ib] at this
    omega
  have hne_ib_ia : ∀ (a : Fin 2) (b : Fin 4), ib a ≠ ia b := fun a b h => (hne_ia_ib b a).symm h
  have ia_inj : ∀ a b : Fin 4, ia a = ia b ↔ a = b := by
    intro a b
    constructor
    · intro h
      have := congrArg Fin.val h
      exact Fin.ext (by simpa [ia] using this)
    · intro h; rw [h]
  have hg_off1 : ∀ (a : Fin 4) (b : Fin 2), g0 (ia a) (ib b) = 0 := by
    intro a b
    have h : E0 * g0 = E0 := hE0g
    rw [hL g0] at h
    have h2 := congrFun (congrFun h (ia a)) (ib b)
    rw [E0_entry, if_neg (hne_ia_ib a b)] at h2
    simpa [ia] using h2
  have hg_off2 : ∀ (a : Fin 2) (b : Fin 4), g0 (ib a) (ia b) = 0 := by
    intro a b
    have h : g0 * E0 = E0 := hg0E
    rw [hR g0] at h
    have h2 := congrFun (congrFun h (ib a)) (ia b)
    rw [E0_entry, if_neg (hne_ib_ia a b)] at h2
    simpa [ia] using h2
  have ht_off1 : ∀ (a : Fin 4) (b : Fin 2), t0 (ia a) (ib b) = 0 := by
    intro a b
    have h : t0 * E0 = E0 * t0 := ht0E
    rw [hR t0, hL t0] at h
    have h2 := congrFun (congrFun h (ia a)) (ib b)
    simp [ia, ib] at h2
    exact h2.symm
  have ht_off2 : ∀ (a : Fin 2) (b : Fin 4), t0 (ib a) (ia b) = 0 := by
    intro a b
    have h : t0 * E0 = E0 * t0 := ht0E
    rw [hR t0, hL t0] at h
    have h2 := congrFun (congrFun h (ib a)) (ia b)
    simp [ia, ib] at h2
    exact h2
  have hg_TL : ∀ a b : Fin 4, g0 (ia a) (ia b) = if a = b then 1 else 0 := by
    intro a b
    have h : g0 * E0 = E0 := hg0E
    rw [hR g0] at h
    have h2 := congrFun (congrFun h (ia a)) (ia b)
    rw [E0_entry] at h2
    simp only [ia_inj] at h2
    simpa [ia] using h2
  have hg_blk : g0 = blk6 1 (Matrix.of fun a b => g0 (ib a) (ib b)) := by
    have h := eq_blk6_of_offblock g0 hg_off1 hg_off2
    have hTL : (Matrix.of fun a b => g0 (ia a) (ia b)) = (1 : Matrix (Fin 4) (Fin 4) K) := by
      ext a b
      rw [Matrix.of_apply, hg_TL, Matrix.one_apply]
    rw [hTL] at h
    exact h
  obtain ⟨T1, hT1⟩ : ∃ T1 : Matrix (Fin 4) (Fin 4) K,
      T1 = Matrix.of fun a b => t0 (ia a) (ia b) := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T2 : Matrix (Fin 2) (Fin 2) K,
      T2 = Matrix.of fun a b => t0 (ib a) (ib b) := ⟨_, rfl⟩
  have ht_blk : t0 = blk6 T1 T2 := by
    rw [hT1, hT2]
    exact eq_blk6_of_offblock t0 ht_off1 ht_off2
  have hT1cube : T1 ^ 3 = 1 := by
    apply blk6_fst_inj (N := T2 ^ 3) (N' := 1)
    rw [blk6_one, ← blk6_pow3, ← ht_blk, ht0cube]
  have hfixT : ∀ v : Fin 4 → K, T1 *ᵥ v = v → v = 0 := by
    intro v hv
    have h1 : t0 *ᵥ ext6 v = ext6 v := by rw [ht_blk, blk6_mulVec_ext, hv]
    have h2 : E0 *ᵥ ext6 v = ext6 v := by rw [hE0]; exact diag_fix_ext v
    have h3 := hfix0 (ext6 v) h2 h1
    funext a
    have := congrFun h3 (ia a)
    rw [ext6_ia] at this
    simpa using this
  have hT1q : T1 * T1 + T1 + 1 = 0 := quad_of_cube hT1cube hfixT
  obtain ⟨S1, hS1⟩ := basis4 hnr T1 hT1q hfixT
  obtain ⟨S1m, hS1m⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
      M = (S1 : Matrix (Fin 4) (Fin 4) K) := ⟨_, rfl⟩
  obtain ⟨S1i, hS1i⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
      M = ((S1⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := ⟨_, rfl⟩
  have hS1ii : S1m * S1i = 1 := by rw [hS1m, hS1i]; exact Units.mul_inv S1
  have hS1ii' : S1i * S1m = 1 := by rw [hS1m, hS1i]; exact Units.inv_mul S1
  rw [← hS1m] at hS1
  have hS1D : S1i * T1 * S1m = D4 K := by
    rw [mul_assoc, hS1, ← mul_assoc, hS1ii', one_mul]
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 6) (Fin 6) K, Q = blk6 S1m 1 := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Matrix (Fin 6) (Fin 6) K, Q' = blk6 S1i 1 := ⟨_, rfl⟩
  have hQQ : Q * Q' = 1 := by
    rw [hQ, hQ', ← blk6_mul, hS1ii, Matrix.mul_one, blk6_one]
  have hQ'Q : Q' * Q = 1 := by
    rw [hQ, hQ', ← blk6_mul, hS1ii', Matrix.mul_one, blk6_one]
  have hMS : (a' * Q) * (Q' * a) = 1 := by
    rw [show a' * Q * (Q' * a) = a' * (Q * Q') * a by simp only [Matrix.mul_assoc], hQQ,
      Matrix.mul_one, ha'a]
  have hMS' : (Q' * a) * (a' * Q) = 1 := by
    rw [show Q' * a * (a' * Q) = Q' * (a * a') * Q by simp only [Matrix.mul_assoc], haa',
      Matrix.mul_one, hQ'Q]
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin 2) (Fin 2) K,
      G = Matrix.of fun a b => g0 (ib a) (ib b) := ⟨_, rfl⟩
  obtain ⟨T2', hT2'⟩ : ∃ T2' : Matrix (Fin 2) (Fin 2) K, T2' = T2 := ⟨_, rfl⟩
  have hg_blk' : g0 = blk6 1 G := by rw [hG]; exact hg_blk
  refine ⟨⟨a' * Q, Q' * a, hMS, hMS'⟩, G, T2, ?_, ?_, ?_⟩
  · show (Q' * a) * g * (a' * Q) = blk6 1 G
    calc (Q' * a) * g * (a' * Q) = Q' * (a * g * a') * Q := by simp only [Matrix.mul_assoc]
      _ = Q' * g0 * Q := by rw [hg0]
      _ = Q' * blk6 1 G * Q := by rw [hg_blk']
      _ = blk6 1 G := by
        rw [hQ, hQ', ← blk6_mul, ← blk6_mul]
        simp only [Matrix.mul_one, Matrix.one_mul]
        rw [hS1ii']
  · show (Q' * a) * t * (a' * Q) = blk6 (D4 K) T2
    calc (Q' * a) * t * (a' * Q) = Q' * (a * t * a') * Q := by simp only [Matrix.mul_assoc]
      _ = Q' * t0 * Q := by rw [ht0]
      _ = Q' * blk6 T1 T2 * Q := by rw [ht_blk]
      _ = blk6 (D4 K) T2 := by
        rw [hQ, hQ', ← blk6_mul, ← blk6_mul]
        simp only [Matrix.mul_one, Matrix.one_mul]
        rw [hS1D]

  · show (Q' * a) * e * (a' * Q) = blk6 1 0
    calc (Q' * a) * e * (a' * Q) = Q' * (a * e * a') * Q := by simp only [Matrix.mul_assoc]
      _ = Q' * E0 * Q := by rw [hconjE]
      _ = Q' * blk6 1 0 * Q := by rw [hE0, diag_eq_blk6]
      _ = blk6 1 0 := by
        rw [hQ, hQ', ← blk6_mul, ← blk6_mul]
        simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
        rw [hS1ii']

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
