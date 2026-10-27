module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSplit

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Matrices

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem mul_self_of_sq_eq_one {M : GL ι K} (hM : M ^ 2 = 1) :
    (M : Matrix ι ι K) * M = 1 := by
  have h := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hM
  simpa [sq] using h

theorem sub_one_mul_self [CharP K 2] {M : GL ι K} (hM : M ^ 2 = 1) :
    ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := by
  have h := mul_self_of_sq_eq_one hM
  calc ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) =
      (2 : K) • (1 - (M : Matrix ι ι K)) := by
        rw [sub_mul, mul_sub, mul_sub, h, mul_one, one_mul, one_mul, two_smul]
        abel
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]

theorem sub_one_ne_zero {M : GL ι K} (hM : M ≠ 1) : (M : Matrix ι ι K) - 1 ≠ 0 := by
  intro h
  exact hM (Units.ext (sub_eq_zero.mp h))

omit [Fintype ι] [DecidableEq ι] in
theorem matrix_add_self [CharP K 2] (X : Matrix ι ι K) : X + X = 0 := by
  rw [← two_smul K X, CharTwo.two_eq_zero, zero_smul]

end Matrices

section Alpha

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem exists_alphaHom [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {x : G} {M : GL ι K}
    (hxM : Represents e x M) (hM2 : orderOf M = 2)
    (hE : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0)
    (hH : ∀ a : K, unipGL ((M : Matrix ι ι K) - 1) hE a ∈ H) :
    ∃ φ : Multiplicative K →* G, Function.Injective φ ∧ φ.range = alphaGroup e x ∧
      ∀ a : K, φ (Multiplicative.ofAdd a) ^ 2 = 1 ∧
        Represents e (φ (Multiplicative.ofAdd a)) (unipGL ((M : Matrix ι ι K) - 1) hE a) := by
  classical
  set E : Matrix ι ι K := (M : Matrix ι ι K) - 1 with hEdef
  have hM1 : M ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hM2
    omega
  have hE0 : E ≠ 0 := sub_one_ne_zero hM1
  choose f hι2 hι using fun a : K =>
    exists_represents_sq_eq_one (e := e) hZ (hH a) (unipGL_sq hE a)
  have hι2' : ∀ a, f a ^ 2 ^ 1 = 1 := fun a => by rw [pow_one]; exact hι2 a
  have hι0 : f 0 = 1 := eq_of_represents hZ (hι 0)
    (by rw [unipGL_zero]; exact represents_one) (hι2' 0) (k' := 0) (by simp)
  have hcomm : ∀ a b, f a * f b = f b * f a := fun a b =>
    commute_of_represents hZ (hι a) (hι b) (hι2 b) (by rw [unipGL_mul, unipGL_mul, add_comm])
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    have hrep : Represents e (f a * f b) (unipGL E hE (a + b)) := by
      rw [← unipGL_mul]
      exact (hι a).mul (hι b)
    have hsq : (f a * f b) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (f a) (f b) from hcomm a b).mul_pow, hι2, hι2, one_mul]
    exact eq_of_represents hZ (hι (a + b)) hrep (hι2' _) hsq
  let φ : Multiplicative K →* G :=
    { toFun := fun d => f d.toAdd
      map_one' := hι0
      map_mul' := fun a b => hadd a.toAdd b.toAdd }
  have hφ : ∀ d, φ d = f d.toAdd := fun d => rfl
  have hinj : ∀ a, f a = 1 → a = 0 := by
    intro a ha
    have hrep : Represents e (1 : G) (unipGL E hE a) := ha ▸ hι a
    obtain ⟨c, hc⟩ := represents_one.exists_scalar hrep
    have hc' : (1 : Matrix ι ι K) + a • E = (c : K) • 1 := by
      have h := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hc
      simp only [coe_unipGL, one_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
      rw [h, Matrix.smul_one_eq_diagonal]
      rfl
    exact eq_zero_of_unip_eq_scalar hE hE0 hc'
  refine ⟨φ, (injective_iff_map_eq_one φ).mpr fun d hd => ?_, ?_, fun a => ⟨hι2 a, hι a⟩⟩
  · have h0 := hinj d.toAdd hd
    exact h0
  · apply le_antisymm
    · rintro _ ⟨d, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨⟨1, hι2' d.toAdd⟩, M, unipGL E hE d.toAdd, hxM, hM2, hι d.toAdd, d.toAdd, ?_⟩
      rw [coe_unipGL, add_sub_cancel_left]
    · rw [alphaGroup, closure_le]
      rintro y ⟨⟨k, hk⟩, M', N, hM', hM'2, hyN, a, ha⟩
      obtain rfl := hxM.eq_of_orderOf_eq_two hM' hM2 hM'2
      have hN : N = unipGL E hE a := by
        apply Units.ext
        rw [coe_unipGL, ← ha, add_sub_cancel]
      rw [hN] at hyN
      exact ⟨Multiplicative.ofAdd a, eq_of_represents hZ (hι a) hyN (hι2' a) hk⟩

theorem card_alphaGroup [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {x : G} {M : GL ι K}
    (hxM : Represents e x M) (hM2 : orderOf M = 2)
    (hE : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0)
    (hH : ∀ a : K, unipGL ((M : Matrix ι ι K) - 1) hE a ∈ H) :
    Nat.card (alphaGroup e x) = Nat.card K := by
  obtain ⟨φ, hinj, hrange, -⟩ := exists_alphaHom hZ hxM hM2 hE hH
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  rfl

theorem exists_of_mem_alphaGroup [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {x : G}
    {M : GL ι K} (hxM : Represents e x M) (hM2 : orderOf M = 2)
    (hE : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0)
    (hH : ∀ a : K, unipGL ((M : Matrix ι ι K) - 1) hE a ∈ H) {y : G}
    (hy : y ∈ alphaGroup e x) (hy1 : y ≠ 1) :
    ∃ a : K, a ≠ 0 ∧ y ^ 2 = 1 ∧ Represents e y (unipGL ((M : Matrix ι ι K) - 1) hE a) := by
  obtain ⟨φ, -, hrange, hφ⟩ := exists_alphaHom hZ hxM hM2 hE hH
  rw [← hrange] at hy
  obtain ⟨d, rfl⟩ := hy
  refine ⟨d.toAdd, fun h => hy1 ?_, (hφ d.toAdd).1, (hφ d.toAdd).2⟩
  have hd : d = 1 := by
    rw [← ofAdd_toAdd d, h, ofAdd_zero]
  rw [hd, map_one]

end Alpha

section Symplectic

variable {K : Type} [Field K] {n : ℕ}

theorem sympForm_self (v : Fin n ⊕ Fin n → K) : sympForm n K v v = 0 := by
  simp only [sympForm, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add,
    add_zero, Matrix.neg_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem gram_of_mem_statedSp {N : GL (Fin n ⊕ Fin n) K} (hN : N ∈ StatedSp n K) :
    (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks 0 1 (-1) 0
  let S : Subgroup (GL (Fin n ⊕ Fin n) K) :=
    { carrier := {X | (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
        (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [Units.val_mul, Matrix.transpose_mul]
        calc (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
              (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
              ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * b) =
            (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
              ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
                (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *
              (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by noncomm_ring
          _ = J := by rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have h1 : (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
            ((a⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 :=
          Units.mul_inv a
        calc ((a⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
              ((a⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
            ((a⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
              ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
                (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *
              ((a⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
              rw [ha]
          _ = ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
                ((a⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))ᵀ * J *
              ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
                ((a⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) := by
            rw [Matrix.transpose_mul]; noncomm_ring
          _ = J := by rw [h1, Matrix.transpose_one, one_mul, mul_one] }
  have hle : StatedSp n K ≤ S := (Subgroup.closure_le _).mpr fun X hX => hX
  exact hle hN

theorem unipGL_mem_statedSp [CharP K 2] {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : M ^ 2 = 1)
    (hE : ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *
      ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) = 0) (a : K) :
    unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE a ∈ StatedSp n K := by
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks 0 1 (-1) 0 with hJ
  set X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hX
  have hgram : Xᵀ * J * X = J := gram_of_mem_statedSp hM
  have hXX : X * X = 1 := mul_self_of_sq_eq_one hM2
  have hXJ : Xᵀ * J = J * X := by
    calc Xᵀ * J = Xᵀ * J * (X * X) := by rw [hXX, mul_one]
      _ = (Xᵀ * J * X) * X := by noncomm_ring
      _ = J * X := by rw [hgram]
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := X - 1 with hN
  have h1 : Nᵀ * J + J * N = 0 := by
    calc Nᵀ * J + J * N = (J * X - J) + (J * X - J) := by
          rw [hN, Matrix.transpose_sub, Matrix.transpose_one, sub_mul, one_mul, hXJ, mul_sub,
            mul_one]
      _ = 0 := matrix_add_self _
  have h2 : Nᵀ * J * N = 0 := by
    calc Nᵀ * J * N = (J - J * X) + (J - J * X) := by
          rw [hN, Matrix.transpose_sub, Matrix.transpose_one, sub_mul, one_mul, hXJ, mul_sub,
            mul_one, sub_mul, mul_assoc, hXX, mul_one]
          abel
      _ = 0 := matrix_add_self _
  apply Subgroup.subset_closure
  show ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) + a • N)ᵀ * J * (1 + a • N) = J
  have e : ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) + a • N)ᵀ * J * (1 + a • N) =
      J + a • (Nᵀ * J + J * N) + (a * a) • (Nᵀ * J * N) := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
    abel
  rw [e, h1, h2, smul_zero, smul_zero, add_zero, add_zero]

theorem sympForm_unipGL {M : GL (Fin n ⊕ Fin n) K}
    (hE : ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *
      ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) = 0) (a : K)
    (v : Fin n ⊕ Fin n → K) :
    sympForm n K v (((unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE a :
      GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) =
      a * sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) := by
  have hself := sympForm_self (K := K) v
  simp only [sympForm] at hself ⊢
  rw [coe_unipGL, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_add,
    dotProduct_smul, dotProduct_sub, hself, sub_zero, zero_add, smul_eq_mul]

end Symplectic

namespace ClassicalModel

variable {G : Type} [Group G] {A : Subgroup G}

theorem suzukiType_of_mem_alpha (D : ClassicalModel A) (hfam : D.family = .symplectic)
    (hZ : Odd (Nat.card (center ↥A))) {x : G} {L : Letter} {ℓ : ℕ} (hx : D.SuzukiType x L ℓ)
    {y : G} (hy : y ∈ D.alpha x) (hy1 : y ≠ 1) : D.SuzukiType y L ℓ := by
  cases D with
  | linear => exact hx.elim
  | unitary => exact hx.elim
  | orthPlus => simp [family] at hfam
  | orthMinus => simp [family] at hfam
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hxM, hM2, hrk, hlet⟩ := hx
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hE := sub_one_mul_self hMsq
    have hH : ∀ a : K, unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE a ∈
        StatedSp n K := fun a => unipGL_mem_statedSp hxM.2.1 hMsq hE a
    obtain ⟨a, ha, hy2, hyN⟩ := exists_of_mem_alphaGroup hZ hxM hM2 hE hH hy hy1
    refine ⟨orderOf_eq_prime hy2 hy1, _, hyN, orderOf_unipGL hE ha (sub_one_ne_zero ?_), ?_, ?_⟩
    · intro h
      rw [h, orderOf_one] at hM2
      omega
    · rw [commRank_unipGL hE ha]
      exact hrk
    · have hφ : (fun v => sympForm n K v (((unipGL _ hE a : GL (Fin n ⊕ Fin n) K) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) =
          fun v => a * sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) :=
        funext fun v => sympForm_unipGL hE a v
      show LetterHolds L ℓ (fun v => sympForm n K v (((unipGL _ hE a : GL (Fin n ⊕ Fin n) K) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v))
      rw [hφ]
      cases L with
      | a =>
        refine ⟨hlet.1, fun v => ?_⟩
        have h : sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0 :=
          hlet.2 v
        show a * _ = 0
        rw [h, mul_zero]
      | b => exact hlet
      | c =>
        obtain ⟨hev, v, hv⟩ := hlet
        exact ⟨hev, v, mul_ne_zero ha hv⟩

theorem card_alpha_symplectic (D : ClassicalModel A) (hfam : D.family = .symplectic)
    (hZ : Odd (Nat.card (center ↥A))) {x : G} (hx : x ∈ A) (hx2 : orderOf x = 2) :
    Nat.card (D.alpha x) = D.q := by
  have hxZ := not_mem_center_of_orderOf_eq_two hZ hx hx2
  have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  cases D with
  | linear => simp [family] at hfam
  | unitary => simp [family] at hfam
  | orthPlus => simp [family] at hfam
  | orthMinus => simp [family] at hfam
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hxM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hE := sub_one_mul_self hMsq
    have hH : ∀ a : K, unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE a ∈
        StatedSp n K := fun a => unipGL_mem_statedSp hxM.2.1 hMsq hE a
    rw [alpha, card_alphaGroup hZ hxM hM2 hE hH, hK]
    rfl

end ClassicalModel

end CFSG.ComponentClassification.RankTwoClassical
