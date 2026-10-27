module

public import Certificates.Data.Kernel.ThCent.Outer
public import CFSG.Certificates.Kernel.ThCent.Model

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Th.Spec.Dce CFSG.KC.Loop

theorem normMu_spec {MU X : ℕ} (h : normMu MU X = true) :
    ∃ k : ℕ, toMat X * toMat MU = toMat MU ^ k * toMat X := by
  unfold normMu at h
  rcases orB_iff.1 h with h1 | h1
  · refine ⟨1, ?_⟩
    rw [pow_one, ← toMat_mul24, ← toMat_mul24, Nat.eq_of_beq_eq_true h1]
  · rcases orB_iff.1 h1 with h2 | h2
    · refine ⟨2, ?_⟩
      rw [← toMat_mul24, ← toMat_pw24, ← toMat_mul24, Nat.eq_of_beq_eq_true h2]
    · refine ⟨4, ?_⟩
      rw [← toMat_mul24, ← toMat_pw24, ← toMat_mul24, Nat.eq_of_beq_eq_true h2]

theorem muOK_spec {MU LT : ℕ} (h : muOK MU LT = true) :
    toMat MU ^ 7 = 1 ∧ ∀ c < 14, ∃ k : ℕ, toMat (let24 LT c) * toMat MU =
      toMat MU ^ k * toMat (let24 LT c) := by
  unfold muOK at h
  refine ⟨?_, fun c hc => normMu_spec (allBelow_spec (Gen.andB_right h) (by norm_num) c hc)⟩
  rw [← toMat_pw24, Nat.eq_of_beq_eq_true (Gen.andB_left h), toMat_ident24]

theorem jv2_iff {MU X : ℕ} : jv2 MU X = true ↔ toMat X * toMat MU = toMat MU ^ 2 * toMat X := by
  unfold jv2
  constructor
  · intro h
    rw [← toMat_mul24, ← toMat_pw24, ← toMat_mul24, Nat.eq_of_beq_eq_true h]
  · intro h
    have e : mul24 X MU = mul24 (pw24 MU 2) X := by
      refine eq_of_toMat_eq (mul24_lt _ _) (mul24_lt _ _) ?_
      rw [toMat_mul24, toMat_mul24, toMat_pw24, h]
    rw [e]
    exact Nat.beq_refl _

theorem mat_mu_pow {X U : Mat24} {k : ℕ} (h : X * U = U ^ k * X) :
    ∀ e : ℕ, X * U ^ e = U ^ (k * e) * X
  | 0 => by rw [pow_zero, Nat.mul_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
  | e + 1 => by
    rw [pow_succ, ← Matrix.mul_assoc, mat_mu_pow h e, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
      ← pow_add, Nat.mul_succ]

section Conj

variable {Mg : Subgroup Mat24ˣ} {LT : ℕ} {Lu : ℕ → Mat24ˣ}

theorem mu_conj {MU : ℕ} (hmu : muOK MU LT = true)
    (hgen : Mg = Subgroup.closure (Lu '' {g | g < 7}))
    (hL : ∀ g < 7, ((Lu g : Mat24ˣ) : Mat24) = toMat (let24 LT (2 * g)))
    (hLi : ∀ g < 7, (((Lu g)⁻¹ : Mat24ˣ) : Mat24) = toMat (let24 LT (2 * g + 1))) :
    ∀ m ∈ Mg, ∃ e : ℕ, ((m : Mat24ˣ) : Mat24) * toMat MU * (((m⁻¹ : Mat24ˣ)) : Mat24) =
      toMat MU ^ e := by
  obtain ⟨-, hc⟩ := muOK_spec hmu
  have hlet : ∀ (u : Mat24ˣ) (c : ℕ), c < 14 → ((u : Mat24ˣ) : Mat24) = toMat (let24 LT c) →
      ∃ e : ℕ, ((u : Mat24ˣ) : Mat24) * toMat MU * (((u⁻¹ : Mat24ˣ)) : Mat24) = toMat MU ^ e := by
    intro u c hc14 hu
    obtain ⟨k, hk⟩ := hc c hc14
    refine ⟨k, ?_⟩
    rw [hu, hk, Matrix.mul_assoc, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  intro m hm
  rw [hgen] at hm
  induction hm using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hlet _ (2 * g) (by simp only [Set.mem_setOf_eq] at hg; omega) (hL g hg)
  | inv_mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hlet _ (2 * g + 1) (by simp only [Set.mem_setOf_eq] at hg; omega) (hLi g hg)
  | one => exact ⟨1, by rw [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, pow_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e1, h1⟩ := hx
    obtain ⟨e2, h2⟩ := hy
    refine ⟨e1 * e2, ?_⟩
    have key : ∀ n : ℕ, ((x : Mat24ˣ) : Mat24) * toMat MU ^ n * (((x⁻¹ : Mat24ˣ)) : Mat24) =
        toMat MU ^ (e1 * n) := by
      intro n
      induction n with
      | zero =>
        rw [pow_zero, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Nat.mul_zero,
          pow_zero]
      | succ n ih =>
        have e : ((x : Mat24ˣ) : Mat24) * toMat MU ^ (n + 1) * (((x⁻¹ : Mat24ˣ)) : Mat24) =
            (((x : Mat24ˣ) : Mat24) * toMat MU ^ n * (((x⁻¹ : Mat24ˣ)) : Mat24)) *
              (((x : Mat24ˣ) : Mat24) * toMat MU * (((x⁻¹ : Mat24ˣ)) : Mat24)) := by
          have hxx : (((x⁻¹ : Mat24ˣ)) : Mat24) * ((x : Mat24ˣ) : Mat24) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          rw [pow_succ]
          calc ((x : Mat24ˣ) : Mat24) * (toMat MU ^ n * toMat MU) * (((x⁻¹ : Mat24ˣ)) : Mat24)
              = ((x : Mat24ˣ) : Mat24) * toMat MU ^ n * 1 * toMat MU *
                  (((x⁻¹ : Mat24ˣ)) : Mat24) := by simp only [Matrix.mul_one, Matrix.mul_assoc]
            _ = _ := by rw [← hxx]; simp only [Matrix.mul_assoc]
        rw [e, ih, h1, ← pow_add, Nat.mul_succ]
    calc (((x * y : Mat24ˣ)) : Mat24) * toMat MU * ((((x * y)⁻¹ : Mat24ˣ)) : Mat24)
        = ((x : Mat24ˣ) : Mat24) * (((y : Mat24ˣ) : Mat24) * toMat MU *
            (((y⁻¹ : Mat24ˣ)) : Mat24)) * (((x⁻¹ : Mat24ˣ)) : Mat24) := by
          rw [mul_inv_rev, Units.val_mul, Units.val_mul]
          simp only [Matrix.mul_assoc]
      _ = toMat MU ^ (e1 * e2) := by rw [h2, key]

theorem jv2_conj {MU : ℕ} (hmu : muOK MU LT = true)
    (hgen : Mg = Subgroup.closure (Lu '' {g | g < 7}))
    (hL : ∀ g < 7, ((Lu g : Mat24ˣ) : Mat24) = toMat (let24 LT (2 * g)))
    (hLi : ∀ g < 7, (((Lu g)⁻¹ : Mat24ˣ) : Mat24) = toMat (let24 LT (2 * g + 1)))
    {X Y : ℕ} (m : Mg) (hY : toMat Y = ((m : Mat24ˣ) : Mat24) * toMat X *
      (((m⁻¹ : Mg) : Mat24ˣ) : Mat24)) (hX : jv2 MU X = true) : jv2 MU Y = true := by
  obtain ⟨e, he⟩ := mu_conj hmu hgen hL hLi (m⁻¹ : Mg) (m⁻¹ : Mg).2
  rw [Subgroup.coe_inv, inv_inv] at he
  set Q := ((m : Mat24ˣ) : Mat24)
  set P := ((((m⁻¹ : Mg)) : Mat24ˣ) : Mat24)
  set U := toMat MU
  have hQP : Q * P = 1 := by
    change ((m : Mat24ˣ) : Mat24) * (((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPQ : P * Q = 1 := by
    change (((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24) * ((m : Mat24ˣ) : Mat24) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have he' : P * U * Q = U ^ e := he
  have hU : Q * U ^ e * P = U := by
    rw [← he']
    calc Q * (P * U * Q) * P = (Q * P) * U * (Q * P) := by simp only [Matrix.mul_assoc]
      _ = U := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  have hX' := jv2_iff.1 hX
  have hpow := mat_mu_pow hX' e
  rw [jv2_iff, hY]
  calc Q * toMat X * P * U = Q * toMat X * (P * U * Q) * P := by
        rw [show Q * toMat X * (P * U * Q) * P = Q * toMat X * P * U * (Q * P) by
          simp only [Matrix.mul_assoc], hQP, Matrix.mul_one]
    _ = Q * (toMat X * U ^ e) * P := by rw [he']; simp only [Matrix.mul_assoc]
    _ = Q * (U ^ (2 * e) * toMat X) * P := by rw [hpow]
    _ = (Q * U ^ e * P) ^ 2 * (Q * toMat X * P) := by
        symm
        calc (Q * U ^ e * P) ^ 2 * (Q * toMat X * P)
            = Q * U ^ e * (P * Q) * U ^ e * (P * Q) * toMat X * P := by
              rw [sq]
              simp only [Matrix.mul_assoc]
          _ = Q * (U ^ e * U ^ e) * toMat X * P := by
              rw [hPQ, Matrix.mul_one, Matrix.mul_one]
              simp only [Matrix.mul_assoc]
          _ = Q * (U ^ (2 * e) * toMat X) * P := by
              rw [← pow_add, ← two_mul]
              simp only [Matrix.mul_assoc]
    _ = U ^ 2 * (Q * toMat X * P) := by rw [hU]

end Conj

theorem markOK_spec {EB CB : ℕ → ℕ} {MU o r n : ℕ} : ∀ (MK : List ℕ) (lb : ℕ),
    markOK EB CB MU o r n MK lb = true → ∃ S : Finset ℕ, S.card = MK.length ∧
      ∀ j ∈ S, lb ≤ j ∧ j < n ∧ ordRank o r (DceS.mat EB j) = true ∧
        jv2 MU (DceS.mat EB j) = true ∧ ∃ k < 819, commB (DceS.mat CB k) (DceS.mat EB j) = true
  | [], _, _ => ⟨∅, rfl, fun _ hj => absurd hj (Finset.notMem_empty _)⟩
  | e :: MK, lb, h => by
    change andB (andB (Nat.ble lb (Nat.land e 65535)) (Nat.blt (Nat.land e 65535) n))
      (andB (andB (ordRank o r (DceS.mat EB (Nat.land e 65535)))
        (jv2 MU (DceS.mat EB (Nat.land e 65535))))
        (andB (andB (Nat.blt (Nat.shiftRight e 16) 819)
          (commB (DceS.mat CB (Nat.shiftRight e 16)) (DceS.mat EB (Nat.land e 65535))))
          (markOK EB CB MU o r n MK (Nat.succ (Nat.land e 65535))))) = true at h
    set j := Nat.land e 65535
    obtain ⟨S, hS, hSj⟩ := markOK_spec MK (Nat.succ j) (Gen.andB_right (Gen.andB_right
      (Gen.andB_right h)))
    have h1 := Gen.andB_left h
    have h2 := Gen.andB_left (Gen.andB_right h)
    have h3 := Gen.andB_left (Gen.andB_right (Gen.andB_right h))
    have hjS : j ∉ S := fun hj => by
      have := (hSj j hj).1
      change j + 1 ≤ j at this
      omega
    refine ⟨insert j S, by rw [Finset.card_insert_of_notMem hjS, hS, List.length_cons], ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨Nat.ble_eq.mp (Gen.andB_left h1), Nat.blt_eq.mp (Gen.andB_right h1),
        Gen.andB_left h2, Gen.andB_right h2, _, Nat.blt_eq.mp (Gen.andB_left h3),
        Gen.andB_right h3⟩
    · obtain ⟨h4, h5⟩ := hSj i hi
      have hlb : lb ≤ j := Nat.ble_eq.mp (Gen.andB_left h1)
      exact ⟨by change j + 1 ≤ i at h4; omega, h5⟩

theorem ojAt_shift (EB : ℕ → ℕ) (MU o r lo j : ℕ) :
    ojAt EB MU o r lo j = ojAt EB MU o r 0 (lo + j) := by
  unfold ojAt
  rw [show Nat.add 0 (lo + j) = Nat.add lo j from Nat.zero_add _]

theorem countOJ_eq (EB : ℕ → ℕ) {MU o r lo n hi : ℕ} (hn : n ≤ 64 * hi) :
    countOJ EB MU o r lo n hi = ((Finset.range n).filter fun i => ojAt EB MU o r lo i = true).card :=
  countGen (ojAt EB MU o r lo) hn

theorem oj_card_le {EB : ℕ → ℕ} {n MU o r : ℕ} {OJ : List ℕ} {nc : ℕ} (hn : n ≤ 2048 * nc)
    (h : ∀ i < nc, ojChunk EB n MU o r OJ i = true) :
    ((Finset.range n).filter fun j => ojAt EB MU o r 0 j = true).card ≤ sumN OJ := by
  rw [card_chunks (ojAt EB MU o r 0) hn (getN OJ) fun i hi => ?_]
  · exact sum_getN_le OJ nc
  · have e := Nat.eq_of_beq_eq_true (h i hi)
    rw [countOJ_eq EB (cLen_le n i)] at e
    rw [← e]
    simp only [ojAt_shift EB MU o r (Nat.mul 2048 i)]
    rfl

end CFSG.KC.ThCent

end
