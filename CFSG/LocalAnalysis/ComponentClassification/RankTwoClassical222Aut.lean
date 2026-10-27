module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitForm

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Square

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]

omit [CharP K 2] in
theorem even_commRank_sq (Q : QuadraticForm K (ι → K)) (hQ : Q.polarBilin.Nondegenerate)
    {M : GL ι K} (hM : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) : Even (commRank (M ^ 2)) := by
  set φ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)) with hφdef
  have hφ : ∀ (N : GL ι K) v, φ N v = (N : Matrix ι ι K) *ᵥ v := fun _ _ => rfl
  have hO : φ M ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [hφ]; exact hM v
  have hrange : ∀ N : GL ι K, commSpace (φ N) =
      LinearMap.range ((N : Matrix ι ι K) - 1).mulVecLin := fun N => by
    ext v
    simp [hφ]
  have h1 := natCast_finrank_commSpace_mul hQ hO hO
  rw [← map_mul, ← pow_two, CharTwo.add_self_eq_zero, hrange,
    ZMod.natCast_eq_zero_iff_even] at h1
  exact h1

theorem sq_mem_statedOmega [Finite K] (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {M : GL ι K}
    (hM : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) : M ^ 2 ∈ StatedOmega ⇑Q :=
  mem_statedOmega_of Q hQ hT (fun v => by
    rw [pow_two, Units.val_mul, ← mulVec_mulVec, hM, hM]) (even_commRank_sq Q hQ hM)

end Square

section Torus

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

theorem exists_isometry_conj_eq_smul (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K} (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v))
    (hQN : ∀ v, Q (N *ᵥ v) = 0) {l : K} (hl : l ≠ 0) :
    ∃ d : GL ι K, (∀ v, Q ((d : Matrix ι ι K) *ᵥ v) = Q v) ∧
      (d : Matrix ι ι K) * N * ((d⁻¹ : GL ι K) : Matrix ι ι K) = l • N := by
  obtain ⟨D, hDQ, -, hD⟩ := exists_torus Q hQ hN hadj hQN (k := 0) Fin.elim0
    (fun j => j.elim0) (linearIndependent_empty_type) (by
      rw [Set.range_eq_empty, Submodule.span_empty]
      exact disjoint_bot_right) hl
  refine ⟨D⁻¹, fun v => ?_, by rw [inv_inv]; exact hD⟩
  rw [← hDQ (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v), mulVec_mulVec, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mulVec]

end Torus

section Families

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem autAlpha_symplectic : AutAlpha .symplectic := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    have hp' : (∃ ℓ, HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .a ℓ) ∨
        HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
          sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) p .b 1 := hp
    obtain ⟨M, hpM, hM2⟩ : ∃ M : GL (Fin n ⊕ Fin n) K, Represents e p M ∧ orderOf M = 2 := by
      rcases hp' with ⟨ℓ, -, M, hpM, hM2, -⟩ | ⟨-, M, hpM, hM2, -⟩
      · exact ⟨M, hpM, hM2⟩
      · exact ⟨M, hpM, hM2⟩
    have hMsp : M ∈ StatedSp n K := hpM.2.1
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hE := sub_one_mul_self hMsq
    obtain ⟨φ, hinj, hrange, hφ⟩ := exists_alphaHom hZ hpM hM2 hE
      (fun a => unipGL_mem_statedSp hMsp hMsq hE a)
    obtain ⟨Q, hpol, hQN⟩ := exists_quadraticForm_sub_one hMsp hM2
    have hQ : Q.polarBilin.Nondegenerate := by
      rw [hpol]
      exact nondegenerate_polarBilin_quadPlus n K
    have hadj : ∀ u v,
        Q.polarBilin (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ u) v =
          Q.polarBilin u (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) := by
      rw [hpol]
      exact polarBilin_sub_one_adj (polarBilin_mulVec_of_mem_statedSp hMsp) hM2
    have h := regularOn_autCyclic_alpha_of (ιF := RingHom.id K) hZ hM2 hinj hrange hφ
      fun l hl => by
        obtain ⟨d, hdQ, hd⟩ := exists_isometry_conj_eq_smul Q hQ hE hadj hQN hl
        refine ⟨d, mem_statedSp_of_polarBilin fun v w => ?_, hd⟩
        rw [← hpol]
        exact polarBilin_mulVec_of_isometry Q hdQ v w
    show RegularOn A (alphaGroup e p) (nonidentity (alphaGroup e p)) ∧
      AutCyclic A (alphaGroup e p) (2 ^ m - 1)
    rwa [← hK]
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem regularOn_autCyclic_of_typeA_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K) (hq : ⇑Q = q)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} {ℓ : ℕ} (hp : HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) p .a ℓ) :
    RegularOn A (alphaGroup e p) (nonidentity (alphaGroup e p)) ∧
      AutCyclic A (alphaGroup e p) (Nat.card K - 1) := by
  subst hq
  obtain ⟨-, M, hpM, hM2, hr, hev, hsing⟩ := hp
  replace hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0 := hsing
  rw [← hr] at hev
  have hMQ : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v := statedOmega_isometry hpM.2.1
  have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hE := sub_one_mul_self hMsq
  have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_isometry Q hMQ) hM2
  have halt : ∀ v, Q.polarBilin v (((M : Matrix ι ι K) - 1) *ᵥ v) = 0 := fun v => by
    have h1 := hMQ v
    rw [show (M : Matrix ι ι K) *ᵥ v = v + ((M : Matrix ι ι K) - 1) *ᵥ v by
      rw [sub_mulVec, one_mulVec, add_sub_cancel], quad_add, hsing, add_zero] at h1
    exact add_eq_left.mp h1
  have hH : ∀ a : K, unipGL ((M : Matrix ι ι K) - 1) hE a ∈ StatedOmega ⇑Q := by
    intro a
    by_cases ha : a = 0
    · rw [ha, unipGL_zero]
      exact one_mem _
    · refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
      · rw [coe_unipGL, add_mulVec, one_mulVec, smul_mulVec, quad_add, QuadraticMap.map_smul,
          hsing, smul_zero, add_zero, map_smul, smul_eq_mul, halt, mul_zero, add_zero]
      · rw [commRank_unipGL hE ha]
        exact hev
  obtain ⟨φ, hinj, hrange, hφ⟩ := exists_alphaHom hZ hpM hM2 hE hH
  refine regularOn_autCyclic_alpha_of (ιF := RingHom.id K) hZ hM2 hinj hrange hφ fun l hl => ?_
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) l
  have hμ0 : μ ≠ 0 := fun h0 => hl (by rw [hμ, h0, mul_zero])
  obtain ⟨d, hdQ, hd⟩ := exists_isometry_conj_eq_smul Q hQ hE hadj hsing hμ0
  refine ⟨d ^ 2, sq_mem_statedOmega Q hQ hT hdQ, ?_⟩
  rw [RingHom.id_apply, hμ, pow_two, _root_.mul_inv_rev, Units.val_mul, Units.val_mul,
    show (d : Matrix ι ι K) * d * ((M : Matrix ι ι K) - 1) * (((d⁻¹ : GL ι K) : Matrix ι ι K) *
      ((d⁻¹ : GL ι K) : Matrix ι ι K)) = (d : Matrix ι ι K) * ((d : Matrix ι ι K) *
        ((M : Matrix ι ι K) - 1) * ((d⁻¹ : GL ι K) : Matrix ι ι K)) *
          ((d⁻¹ : GL ι K) : Matrix ι ι K) by simp only [Matrix.mul_assoc], hd, Matrix.mul_smul,
    Matrix.smul_mul, hd, smul_smul]

theorem autAlpha_orthPlus : AutAlpha .orthPlus := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, hpℓ⟩ := hp
    have h := regularOn_autCyclic_of_typeA_orth (quadPlus n K) (StatedQuadPlus n K)
      (coe_quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
      (exists_totallySingular_quadPlus (by omega) K) hZ hpℓ
    show RegularOn A (alphaGroup e p) (nonidentity (alphaGroup e p)) ∧
      AutCyclic A (alphaGroup e p) (2 ^ m - 1)
    rwa [← hK]
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem autAlpha_orthMinus : AutAlpha .orthMinus := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, hpℓ⟩ := hp
    have h := regularOn_autCyclic_of_typeA_orth (quadMinus n K b c) (StatedQuadMinus n K b c)
      (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c) hZ hpℓ
    show RegularOn A (alphaGroup e p) (nonidentity (alphaGroup e p)) ∧
      AutCyclic A (alphaGroup e p) (2 ^ m - 1)
    rwa [← hK]
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

end Families

end CFSG.ComponentClassification.RankTwoClassical
