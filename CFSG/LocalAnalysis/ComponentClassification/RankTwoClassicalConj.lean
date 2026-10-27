module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSec72

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Matrices

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

omit [DecidableEq ι] in
theorem eq_zero_of_rank_eq_zero {M : Matrix ι ι K} (h : M.rank = 0) : M = 0 := by
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero, Submodule.span_eq_bot] at h
  ext i j
  exact congrFun (h _ ⟨j, rfl⟩) i

theorem val_conj_sub_one (M N : GL ι K) :
    ((N * M * N⁻¹ : GL ι K) : Matrix ι ι K) - 1 =
      (N : Matrix ι ι K) * ((M : Matrix ι ι K) - 1) * ((N⁻¹ : GL ι K) : Matrix ι ι K) := by
  rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]

theorem commRank_conj (M N : GL ι K) : commRank (N * M * N⁻¹) = commRank M := by
  unfold commRank
  rw [val_conj_sub_one, Matrix.rank_mul_eq_left_of_isUnit_det,
    Matrix.rank_mul_eq_right_of_isUnit_det]
  all_goals exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)

theorem commRank_ne_zero {M : GL ι K} (h2 : orderOf M = 2) : commRank M ≠ 0 := by
  intro h0
  have h1 : (M : Matrix ι ι K) - 1 = 0 := eq_zero_of_rank_eq_zero h0
  have hM : M = 1 := Units.ext (sub_eq_zero.mp h1)
  rw [hM, orderOf_one] at h2
  omega

theorem statedOmega_isometry {Q : (ι → K) → K} {N : GL ι K}
    (hN : N ∈ Assembly.LowTwoRank.StatedOmega Q) (v : ι → K) :
    Q ((N : Matrix ι ι K) *ᵥ v) = Q v := by
  let S : Subgroup (GL ι K) :=
    { carrier := {N | ∀ v, Q ((N : Matrix ι ι K) *ᵥ v) = Q v}
      mul_mem' := fun {a b} ha hb v => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
      one_mem' := fun v => by simp
      inv_mem' := fun {a} ha v => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [← ha ((↑a⁻¹ : Matrix ι ι K) *ᵥ v), Matrix.mulVec_mulVec, Units.mul_inv,
          Matrix.one_mulVec] }
  have hC : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤ S :=
    (Subgroup.closure_le _).mpr fun A hA => hA
  have hle : Assembly.LowTwoRank.StatedOmega Q ≤ S := by
    unfold Assembly.LowTwoRank.StatedOmega
    refine Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hC h₁) (hC h₂)) (inv_mem (hC h₁))) (inv_mem (hC h₂))
  exact hle hN v

theorem isometry_of_mem_closure (J : Matrix ι ι K) {N : GL ι K}
    (hN : N ∈ Subgroup.closure {A : GL ι K | (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J})
    (v w : ι → K) :
    ((N : Matrix ι ι K) *ᵥ v) ⬝ᵥ (J *ᵥ ((N : Matrix ι ι K) *ᵥ w)) = v ⬝ᵥ (J *ᵥ w) := by
  let S : Subgroup (GL ι K) :=
    { carrier := {A : GL ι K | (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [Units.val_mul, Matrix.transpose_mul]
        calc (b : Matrix ι ι K)ᵀ * (a : Matrix ι ι K)ᵀ * J * ((a : Matrix ι ι K) * b) =
            (b : Matrix ι ι K)ᵀ * ((a : Matrix ι ι K)ᵀ * J * (a : Matrix ι ι K)) *
              (b : Matrix ι ι K) := by noncomm_ring
          _ = J := by rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have h1 : (a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K) = 1 := Units.mul_inv a
        calc ((a⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((a⁻¹ : GL ι K) : Matrix ι ι K) =
            ((a⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((a : Matrix ι ι K)ᵀ * J * (a : Matrix ι ι K)) *
              ((a⁻¹ : GL ι K) : Matrix ι ι K) := by rw [ha]
          _ = ((a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * J *
              ((a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K)) := by
            rw [Matrix.transpose_mul]; noncomm_ring
          _ = J := by rw [h1, Matrix.transpose_one, one_mul, mul_one] }
  have hle : Subgroup.closure {A : GL ι K | (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J} ≤
      S := (Subgroup.closure_le _).mpr fun A hA => hA
  have hNJ : (N : Matrix ι ι K)ᵀ * J * (N : Matrix ι ι K) = J := hle hN
  have key : ∀ u : ι → K,
      ((N : Matrix ι ι K) *ᵥ v) ⬝ᵥ u = v ⬝ᵥ ((N : Matrix ι ι K)ᵀ *ᵥ u) := by
    intro u
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hNJ]

theorem statedSp_isometry {n : ℕ} {N : GL (Fin n ⊕ Fin n) K}
    (hN : N ∈ Assembly.LowTwoRank.StatedSp n K) (v w : Fin n ⊕ Fin n → K) :
    sympForm n K ((N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)
      ((N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w) = sympForm n K v w :=
  isometry_of_mem_closure _ hN v w

theorem sympForm_conj {n : ℕ} {M N : GL (Fin n ⊕ Fin n) K}
    (hN : N ∈ Assembly.LowTwoRank.StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    sympForm n K v (((N * M * N⁻¹ : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) =
      sympForm n K (((N⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        *ᵥ v) ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
          (((N⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) := by
  have e1 : (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      (((N⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have e2 : (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
        (((N⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) =
      ((N * M * N⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul]
  have h := statedSp_isometry hN
    (((N⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)
    ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      (((N⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v))
  rw [e1, e2] at h
  exact h

theorem quad_conj {Q : (ι → K) → K} {M N : GL ι K}
    (hN : N ∈ Assembly.LowTwoRank.StatedOmega Q) (v : ι → K) :
    Q ((((N * M * N⁻¹ : GL ι K) : Matrix ι ι K) - 1) *ᵥ v) =
      Q (((M : Matrix ι ι K) - 1) *ᵥ (((N⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)) := by
  rw [val_conj_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, statedOmega_isometry hN]

end Matrices

section Represents

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)}

theorem exists_represents (e : rankTwoQuot A ≃* Assembly.LowTwoRank.StatedProj H) {b : G}
    (hb : b ∈ A) : ∃ N : GL ι K, Represents e b N := by
  obtain ⟨N, hN⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk ⟨b, hb⟩))
  exact ⟨N, hb, N.2, hN.symm⟩

theorem Represents.conj {e : rankTwoQuot A ≃* Assembly.LowTwoRank.StatedProj H} {x b : G}
    {M N : GL ι K} (hM : Represents e x M) (hN : Represents e b N) :
    Represents e (b * x * b⁻¹) (N * M * N⁻¹) := by
  obtain ⟨hx, hMH, he⟩ := hM
  obtain ⟨hb, hNH, hf⟩ := hN
  refine ⟨mul_mem (mul_mem hb hx) (inv_mem hb), mul_mem (mul_mem hNH hMH) (inv_mem hNH), ?_⟩
  have h1 : (⟨b * x * b⁻¹, mul_mem (mul_mem hb hx) (inv_mem hb)⟩ : ↥A) =
      ⟨b, hb⟩ * ⟨x, hx⟩ * (⟨b, hb⟩ : ↥A)⁻¹ := rfl
  have h2 : (⟨N * M * N⁻¹, mul_mem (mul_mem hNH hMH) (inv_mem hNH)⟩ : ↥H) =
      ⟨N, hNH⟩ * ⟨M, hMH⟩ * (⟨N, hNH⟩ : ↥H)⁻¹ := rfl
  rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv,
    he, hf]

omit [Fintype ι] [DecidableEq ι] in
theorem orderOf_conj' {M : Type*} [Group M] (x b : M) : orderOf (b * x * b⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem IsInvolutionOfRank.conj {e : rankTwoQuot A ≃* Assembly.LowTwoRank.StatedProj H}
    {x b : G} {ℓ : ℕ} (h : IsInvolutionOfRank e x ℓ) (hb : b ∈ A) :
    IsInvolutionOfRank e (b * x * b⁻¹) ℓ := by
  obtain ⟨h2, M, hM, hM2, hr⟩ := h
  obtain ⟨N, hN⟩ := exists_represents e hb
  exact ⟨by rw [orderOf_conj', h2], N * M * N⁻¹, hM.conj hN, by rw [orderOf_conj', hM2],
    by rw [commRank_conj, hr]⟩

theorem IsSingularRankTwo.conj {Q : (ι → K) → K}
    {e : rankTwoQuot A ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedOmega Q)}
    {x b : G} (h : IsSingularRankTwo e Q x) (hb : b ∈ A) :
    IsSingularRankTwo e Q (b * x * b⁻¹) := by
  obtain ⟨h2, M, hM, hM2, hr, hQ⟩ := h
  obtain ⟨N, hN⟩ := exists_represents e hb
  refine ⟨by rw [orderOf_conj', h2], N * M * N⁻¹, hM.conj hN, by rw [orderOf_conj', hM2],
    by rw [commRank_conj, hr], fun v => ?_⟩
  obtain ⟨-, hNH, -⟩ := hN
  rw [val_conj_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    statedOmega_isometry hNH]
  exact hQ _

omit [Fintype ι] [DecidableEq ι] in
theorem letterHolds_comp {L : Letter} {ℓ : ℕ} {φ : (ι → K) → K} {f : (ι → K) → ι → K}
    (hf : Function.Surjective f) : LetterHolds L ℓ (φ ∘ f) ↔ LetterHolds L ℓ φ := by
  cases L with
  | a =>
    constructor
    · rintro ⟨hℓ, h0⟩
      refine ⟨hℓ, fun w => ?_⟩
      obtain ⟨v, rfl⟩ := hf w
      exact h0 v
    · rintro ⟨hℓ, h0⟩
      exact ⟨hℓ, fun v => h0 (f v)⟩
  | b => exact Iff.rfl
  | c =>
    constructor
    · rintro ⟨hℓ, v, hv⟩
      exact ⟨hℓ, f v, hv⟩
    · rintro ⟨hℓ, w, hw⟩
      obtain ⟨v, rfl⟩ := hf w
      exact ⟨hℓ, v, hw⟩

theorem HasSuzukiType.conj {e : rankTwoQuot A ≃* Assembly.LowTwoRank.StatedProj H}
    {Φ : GL ι K → (ι → K) → K}
    (hΦ : ∀ M N : GL ι K, N ∈ H → ∀ v, Φ (N * M * N⁻¹) v = Φ M (((N⁻¹ : GL ι K) :
      Matrix ι ι K) *ᵥ v))
    {x b : G} {L : Letter} {ℓ : ℕ} (h : HasSuzukiType e Φ x L ℓ) (hb : b ∈ A) :
    HasSuzukiType e Φ (b * x * b⁻¹) L ℓ := by
  obtain ⟨h2, M, hM, hM2, hr, hL⟩ := h
  obtain ⟨N, hN⟩ := exists_represents e hb
  obtain ⟨-, hNH, -⟩ := id hN
  refine ⟨by rw [orderOf_conj', h2], N * M * N⁻¹, hM.conj hN, by rw [orderOf_conj', hM2],
    by rw [commRank_conj, hr], ?_⟩
  have hfun : Φ (N * M * N⁻¹) = Φ M ∘ fun v => ((N⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v :=
    funext fun v => hΦ M N hNH v
  rw [hfun, letterHolds_comp]
  · exact hL
  · intro w
    refine ⟨(N : Matrix ι ι K) *ᵥ w, ?_⟩
    simp only
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

end Represents

namespace ClassicalModel

variable {G : Type} [Group G] {A : Subgroup G}

theorem isPrimary_conj (D : ClassicalModel A) {x b : G} (hx : D.IsPrimary x) (hb : b ∈ A) :
    D.IsPrimary (b * x * b⁻¹) := by
  cases D with
  | linear => exact IsInvolutionOfRank.conj hx hb
  | unitary => exact IsInvolutionOfRank.conj hx hb
  | symplectic => exact IsInvolutionOfRank.conj hx hb
  | orthPlus => exact IsSingularRankTwo.conj hx hb
  | orthMinus => exact IsSingularRankTwo.conj hx hb

theorem suzukiType_conj (D : ClassicalModel A) {x b : G} {L : Letter} {ℓ : ℕ}
    (h : D.SuzukiType x L ℓ) (hb : b ∈ A) : D.SuzukiType (b * x * b⁻¹) L ℓ := by
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic n m hn hm hnm K hK e =>
    exact HasSuzukiType.conj (fun M N hN v => sympForm_conj hN v) h hb
  | orthPlus n m hn hm K hK e =>
    exact HasSuzukiType.conj (fun M N hN v => quad_conj hN v) h hb
  | orthMinus n m hn hm K hK b c hbc e =>
    exact HasSuzukiType.conj (fun M N hN v => quad_conj hN v) h hb

theorem hasRank_of_isPrimary (D : ClassicalModel A) {x : G} (hx : D.IsPrimary x) :
    D.HasRank x 1 ∨ D.HasRank x 2 := by
  cases D with
  | linear => exact Or.inl hx
  | unitary => exact Or.inl hx
  | symplectic => exact Or.inl hx
  | orthPlus =>
    obtain ⟨h2, M, hM, hM2, hr, -⟩ := hx
    exact Or.inr ⟨h2, M, hM, hM2, hr⟩
  | orthMinus =>
    obtain ⟨h2, M, hM, hM2, hr, -⟩ := hx
    exact Or.inr ⟨h2, M, hM, hM2, hr⟩

theorem hasRank_of_suzukiType (D : ClassicalModel A) {x : G} {L : Letter} {ℓ : ℕ}
    (h : D.SuzukiType x L ℓ) : D.HasRank x ℓ := by
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic =>
    obtain ⟨h2, M, hM, hM2, hr, -⟩ := h
    exact ⟨h2, M, hM, hM2, hr⟩
  | orthPlus =>
    obtain ⟨h2, M, hM, hM2, hr, -⟩ := h
    exact ⟨h2, M, hM, hM2, hr⟩
  | orthMinus =>
    obtain ⟨h2, M, hM, hM2, hr, -⟩ := h
    exact ⟨h2, M, hM, hM2, hr⟩

theorem isPrimary_of_suzukiType_a_two (D : ClassicalModel A)
    (hD : D.family = .orthPlus ∨ D.family = .orthMinus) {x : G}
    (h : D.SuzukiType x .a 2) : D.IsPrimary x := by
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic => simp [family] at hD
  | orthPlus =>
    obtain ⟨h2, M, hM, hM2, hr, -, hQ⟩ := h
    exact ⟨h2, M, hM, hM2, hr, hQ⟩
  | orthMinus =>
    obtain ⟨h2, M, hM, hM2, hr, -, hQ⟩ := h
    exact ⟨h2, M, hM, hM2, hr, hQ⟩

theorem pos_of_hasRank (D : ClassicalModel A) {x : G} {ℓ : ℕ} (h : D.HasRank x ℓ) : 0 < ℓ := by
  cases D with
  | linear =>
    obtain ⟨-, M, -, hM2, rfl⟩ := h
    exact Nat.pos_of_ne_zero (commRank_ne_zero hM2)
  | unitary =>
    obtain ⟨-, M, -, hM2, rfl⟩ := h
    exact Nat.pos_of_ne_zero (commRank_ne_zero hM2)
  | symplectic =>
    obtain ⟨-, M, -, hM2, rfl⟩ := h
    exact Nat.pos_of_ne_zero (commRank_ne_zero hM2)
  | orthPlus =>
    obtain ⟨-, M, -, hM2, rfl⟩ := h
    exact Nat.pos_of_ne_zero (commRank_ne_zero hM2)
  | orthMinus =>
    obtain ⟨-, M, -, hM2, rfl⟩ := h
    exact Nat.pos_of_ne_zero (commRank_ne_zero hM2)

theorem exists_hasRank (D : ClassicalModel A) (hZ : Odd (Nat.card (center ↥A))) {x : G}
    (hx : x ∈ A) (hx2 : orderOf x = 2) : ∃ ℓ : ℕ, D.HasRank x ℓ := by
  have hxZ := not_mem_center_of_orderOf_eq_two hZ hx hx2
  have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    exact ⟨_, hx2, M, hM, hM2, rfl⟩
  | unitary n m hn hm K hK e =>
    have := charP_two_of_card (k := 2 * m) (by rw [hK, ← pow_mul, mul_comm])
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    exact ⟨_, hx2, M, hM, hM2, rfl⟩
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    exact ⟨_, hx2, M, hM, hM2, rfl⟩
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    exact ⟨_, hx2, M, hM, hM2, rfl⟩
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    exact ⟨_, hx2, M, hM, hM2, rfl⟩

theorem hasRank_unique (D : ClassicalModel A) {x : G} {ℓ ℓ' : ℕ} (h : D.HasRank x ℓ)
    (h' : D.HasRank x ℓ') : ℓ = ℓ' := by
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, rfl⟩ := h
    obtain ⟨-, M', hM', hM'2, rfl⟩ := h'
    rw [hM.eq_of_orderOf_eq_two hM' hM2 hM'2]
  | unitary n m hn hm K hK e =>
    have := charP_two_of_card (k := 2 * m) (by rw [hK, ← pow_mul, mul_comm])
    obtain ⟨-, M, hM, hM2, rfl⟩ := h
    obtain ⟨-, M', hM', hM'2, rfl⟩ := h'
    rw [hM.eq_of_orderOf_eq_two hM' hM2 hM'2]
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, rfl⟩ := h
    obtain ⟨-, M', hM', hM'2, rfl⟩ := h'
    rw [hM.eq_of_orderOf_eq_two hM' hM2 hM'2]
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, rfl⟩ := h
    obtain ⟨-, M', hM', hM'2, rfl⟩ := h'
    rw [hM.eq_of_orderOf_eq_two hM' hM2 hM'2]
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, rfl⟩ := h
    obtain ⟨-, M', hM', hM'2, rfl⟩ := h'
    rw [hM.eq_of_orderOf_eq_two hM' hM2 hM'2]

theorem not_letterHolds_a_c {ι K : Type} [Field K] {ℓ ℓ' : ℕ} {φ : (ι → K) → K}
    (ha : LetterHolds .a ℓ φ) (hc : LetterHolds .c ℓ' φ) : False := by
  obtain ⟨-, h0⟩ := ha
  obtain ⟨-, v, hv⟩ := hc
  exact hv (h0 v)

theorem suzukiType_unique (D : ClassicalModel A) {x : G} {L L' : Letter} {ℓ ℓ' : ℕ}
    (h : D.SuzukiType x L ℓ) (h' : D.SuzukiType x L' ℓ') : L = L' ∧ ℓ = ℓ' := by
  have hℓ := D.hasRank_unique (D.hasRank_of_suzukiType h) (D.hasRank_of_suzukiType h')
  subst hℓ
  refine ⟨?_, rfl⟩
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, -, hL⟩ := h
    obtain ⟨-, M', hM', hM'2, -, hL'⟩ := h'
    obtain rfl := hM.eq_of_orderOf_eq_two hM' hM2 hM'2
    cases L <;> cases L' <;> first | rfl | (exfalso; first
      | exact not_letterHolds_a_c hL hL' | exact not_letterHolds_a_c hL' hL
      | exact (Nat.not_even_iff_odd.mpr hL.1 hL'.1) | exact (Nat.not_even_iff_odd.mpr hL'.1 hL.1)
      | exact (Nat.not_even_iff_odd.mpr hL hL'.1) | exact (Nat.not_even_iff_odd.mpr hL' hL.1))
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, -, hL⟩ := h
    obtain ⟨-, M', hM', hM'2, -, hL'⟩ := h'
    obtain rfl := hM.eq_of_orderOf_eq_two hM' hM2 hM'2
    cases L <;> cases L' <;> first | rfl | (exfalso; first
      | exact not_letterHolds_a_c hL hL' | exact not_letterHolds_a_c hL' hL
      | exact (Nat.not_even_iff_odd.mpr hL.1 hL'.1) | exact (Nat.not_even_iff_odd.mpr hL'.1 hL.1)
      | exact (Nat.not_even_iff_odd.mpr hL hL'.1) | exact (Nat.not_even_iff_odd.mpr hL' hL.1))
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, -, hL⟩ := h
    obtain ⟨-, M', hM', hM'2, -, hL'⟩ := h'
    obtain rfl := hM.eq_of_orderOf_eq_two hM' hM2 hM'2
    cases L <;> cases L' <;> first | rfl | (exfalso; first
      | exact not_letterHolds_a_c hL hL' | exact not_letterHolds_a_c hL' hL
      | exact (Nat.not_even_iff_odd.mpr hL.1 hL'.1) | exact (Nat.not_even_iff_odd.mpr hL'.1 hL.1)
      | exact (Nat.not_even_iff_odd.mpr hL hL'.1) | exact (Nat.not_even_iff_odd.mpr hL' hL.1))

@[expose] def HasMeasure (D : ClassicalModel A) (x : G) (n : ℕ) : Prop :=
  ∃ ℓ : ℕ, D.HasRank x ℓ ∧ ((D.IsPrimary x ∧ n = 3 * ℓ) ∨
    (¬ D.IsPrimary x ∧ (∃ k, D.SuzukiType x .c k) ∧ n = 3 * ℓ + 1) ∨
    (¬ D.IsPrimary x ∧ (¬ ∃ k, D.SuzukiType x .c k) ∧ n = 3 * ℓ + 2))

theorem exists_hasMeasure_le (D : ClassicalModel A) {x : G} {ℓ : ℕ} (h : D.HasRank x ℓ) :
    ∃ n ≤ 3 * ℓ + 2, D.HasMeasure x n := by
  by_cases hp : D.IsPrimary x
  · exact ⟨3 * ℓ, by omega, ℓ, h, Or.inl ⟨hp, rfl⟩⟩
  · by_cases hc : ∃ k, D.SuzukiType x .c k
    · exact ⟨3 * ℓ + 1, by omega, ℓ, h, Or.inr (Or.inl ⟨hp, hc, rfl⟩)⟩
    · exact ⟨3 * ℓ + 2, le_rfl, ℓ, h, Or.inr (Or.inr ⟨hp, hc, rfl⟩)⟩

theorem hasMeasure_of_isPrimary (D : ClassicalModel A) {x : G} {ℓ : ℕ} (h : D.HasRank x ℓ)
    (hp : D.IsPrimary x) : D.HasMeasure x (3 * ℓ) :=
  ⟨ℓ, h, Or.inl ⟨hp, rfl⟩⟩

theorem HasMeasure.ge_of_not_isPrimary {D : ClassicalModel A} {x : G} {n ℓ : ℕ}
    (h : D.HasMeasure x n) (hℓ : D.HasRank x ℓ) (hp : ¬ D.IsPrimary x) : 3 * ℓ + 1 ≤ n := by
  obtain ⟨k, hk, hn⟩ := h
  obtain rfl := D.hasRank_unique hk hℓ
  rcases hn with ⟨hp', -⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact absurd hp' hp
  · exact le_rfl
  · omega

theorem exists_hasMeasure (D : ClassicalModel A) (hZ : Odd (Nat.card (center ↥A))) {x : G}
    (hx : x ∈ A) (hx2 : orderOf x = 2) : ∃ n : ℕ, D.HasMeasure x n := by
  obtain ⟨ℓ, hℓ⟩ := D.exists_hasRank hZ hx hx2
  obtain ⟨n, -, hn⟩ := D.exists_hasMeasure_le hℓ
  exact ⟨n, hn⟩

theorem HasMeasure.unique {D : ClassicalModel A} {x : G} {n n' : ℕ} (h : D.HasMeasure x n)
    (h' : D.HasMeasure x n') : n = n' := by
  obtain ⟨ℓ, hℓ, hn⟩ := h
  obtain ⟨ℓ', hℓ', hn'⟩ := h'
  obtain rfl := D.hasRank_unique hℓ hℓ'
  rcases hn with ⟨hp, rfl⟩ | ⟨hp, hc, rfl⟩ | ⟨hp, hc, rfl⟩ <;>
    rcases hn' with ⟨hp', rfl⟩ | ⟨hp', hc', rfl⟩ | ⟨hp', hc', rfl⟩ <;>
    first | rfl | exact absurd hp hp' | exact absurd hp' hp | exact absurd hc hc' |
      exact absurd hc' hc

theorem HasMeasure.conj {D : ClassicalModel A} {x b : G} {n : ℕ} (h : D.HasMeasure x n)
    (hb : b ∈ A) : D.HasMeasure (b * x * b⁻¹) n := by
  obtain ⟨ℓ, hℓ, hn⟩ := h
  have hback : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
  have hp_iff : D.IsPrimary (b * x * b⁻¹) ↔ D.IsPrimary x := by
    refine ⟨fun hp => ?_, fun hp => D.isPrimary_conj hp hb⟩
    have h1 := D.isPrimary_conj hp (inv_mem hb)
    rwa [hback] at h1
  have hc_iff : (∃ k, D.SuzukiType (b * x * b⁻¹) .c k) ↔ ∃ k, D.SuzukiType x .c k := by
    refine ⟨fun ⟨k, hk⟩ => ⟨k, ?_⟩, fun ⟨k, hk⟩ => ⟨k, D.suzukiType_conj hk hb⟩⟩
    have h1 := D.suzukiType_conj hk (inv_mem hb)
    rwa [hback] at h1
  have hℓ' : D.HasRank (b * x * b⁻¹) ℓ := by
    cases D with
    | linear => exact IsInvolutionOfRank.conj hℓ hb
    | unitary => exact IsInvolutionOfRank.conj hℓ hb
    | symplectic => exact IsInvolutionOfRank.conj hℓ hb
    | orthPlus => exact IsInvolutionOfRank.conj hℓ hb
    | orthMinus => exact IsInvolutionOfRank.conj hℓ hb
  refine ⟨ℓ, hℓ', ?_⟩
  rw [hp_iff, hc_iff]
  exact hn

end ClassicalModel

end CFSG.ComponentClassification.RankTwoClassical
