module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Orth
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222PairTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222PairRoot

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)}

theorem even_rank_cTwoX (hQ : Q.polarBilin.Nondegenerate) (a b : ι → K) :
    Even (cTwoX Q a b).rank := by
  by_cases hli : LinearIndependent K ![a, b]
  · obtain ⟨w, hw⟩ := exists_polar_dual Q hQ ![a, b] hli
    have hb : b ≠ 0 := by simpa using hli.ne_zero 1
    rw [rank_cTwoX hb (p₁ := w 0) (p₂ := w 1) (by rw [polarBilin_comm]; simpa using hw 0 0)
      (by rw [polarBilin_comm]; simpa using hw 1 0) (by rw [polarBilin_comm]; simpa using hw 0 1)
      (by rw [polarBilin_comm]; simpa using hw 1 1)]
    exact even_two
  · have h0 : cTwoX Q a b = 0 := by
      rw [LinearIndependent.pair_iff] at hli
      push Not at hli
      obtain ⟨s, t, hst, hne⟩ := hli
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      rw [cTwoX_mulVec, zero_mulVec]
      by_cases hs : s = 0
      · rw [hs, zero_smul, zero_add] at hst
        rw [(smul_eq_zero.mp hst).resolve_left (hne hs), map_zero, smul_zero, zero_smul,
          add_zero]
      · have ha : a = (-(s⁻¹ * t)) • b := by
          have h1 : s⁻¹ • (s • a + t • b) = 0 := by rw [hst, smul_zero]
          rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul] at h1
          rw [neg_smul, eq_neg_iff_add_eq_zero]
          exact h1
        rw [ha, map_smul, smul_eq_mul]
        linear_combination (norm := module)
          CharTwo.two_eq_zero (R := K) • ((-(s⁻¹ * t) * Q.polarBilin v b) • b)
    rw [h0, Matrix.rank_zero]
    exact ⟨0, rfl⟩

end Linear

section Groups

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)}

theorem commute_of_pairOrbit_orth (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega ⇑Q)} (hZ : Odd (Nat.card (center ↥A)))
    {μ : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) {p : G} (hp2 : p ^ 2 = 1) {M : GL ι K}
    (hpM : Represents e p M) {u : G}
    (horb : ∀ a ∈ A ⊓ centralizer ({p} : Set G), a * u * a⁻¹ = u ∨ a * u * a⁻¹ = u * p)
    {U : GL ι K} (hU : Represents e u U) {E : Matrix ι ι K} (hE : E * E = 0)
    (hEM : E * M = M * E) (hEQ : ∀ (a : K) v, Q ((1 + a • E) *ᵥ v) = Q v) (hEr : Even E.rank) :
    (U : Matrix ι ι K) * E = E * U :=
  commute_of_pairOrbit hZ hμ0 hμ1 hp2 hpM horb hU hE hEM fun t =>
    mem_statedOmega_of Q hQ hT (fun v => by rw [coe_unipGL]; exact hEQ t v) (by
      by_cases ht : t = 0
      · rw [ht, unipGL_zero, commRank, Units.val_one, sub_self, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · rw [commRank_unipGL hE ht]
        exact hEr)

theorem noPairOrbit_typeA_orth (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K) (hq : ⇑Q = q)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : 3 ≤ Nat.card K) {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp2 : orderOf p = 2) {M : GL ι K}
    (hpM : Represents e p M) (hM2 : orderOf M = 2)
    (hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0) : NoPairOrbit A p := by
  subst hq
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hMQ := statedOmega_isometry hpM.2.1
  have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_isometry Q hMQ) hM2
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hM2'
  have hN0 : (M : Matrix ι ι K) - 1 ≠ 0 := sub_one_ne_zero fun h => by
    rw [h, orderOf_one] at hM2
    omega
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hadj hsing hN hN0
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0 := fun v => by
    have h1 := hMQ v
    rw [hMN, add_mulVec, one_mulVec, quad_add, hsing, add_zero] at h1
    exact add_eq_left.mp h1
  have hcomm : ∀ X : GL ι K, X * M = M * X → (X : Matrix ι ι K) * N = N * X := fun X hXM => by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one_of_three_le_card hK
  intro u hu hu2 horb
  obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
  have hUM : U * M = M * U := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hU.mul_comm_of_commute hpM hM2' (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2))
  have hUB := polarBilin_mulVec_of_isometry Q (statedOmega_isometry hU.2.1)
  have hroot : ∀ a b : ι → K, Q a = 0 → Q b = 0 → Q.polarBilin a b = 0 →
      cTwoX Q a b * N = N * cTwoX Q a b →
      (U : Matrix ι ι K) * cTwoX Q a b = cTwoX Q a b * U := fun a b ha hb hab hEN =>
    commute_of_pairOrbit_orth hQ hT hZ hμ0 hμ1 hp2' hpM horb hU (cTwoX_mul_self hab)
      (by rw [hMN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hEN])
      (fun t v => cTwoX_isometry ha hb hab t v) (even_rank_cTwoX hQ a b)
  have hXNN : ∀ x y, (U : Matrix ι ι K) * cTwoX Q (N *ᵥ x) (N *ᵥ y) =
      cTwoX Q (N *ᵥ x) (N *ᵥ y) * U := fun x y =>
    hroot _ _ (hsing x) (hsing y) (by rw [hadj, hNN, map_zero]) (by
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      simp only [← mulVec_mulVec, cTwoX_mulVec, mulVec_add, mulVec_smul, hNN, hadj v, map_zero,
        zero_smul, smul_zero, add_zero])
  have hτ : ∀ w, (U : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * U := by
    intro w
    by_cases hw : N *ᵥ w = 0
    · rw [hw, cTwoX_zero_left, Matrix.mul_zero, Matrix.zero_mul]
    obtain ⟨x, hx⟩ := exists_polarBilin_eq_one hQ hw
    have hwx : Q.polarBilin w (N *ᵥ x) = 1 := by rw [← hadj, hBs]; exact hx
    have hNw' : N *ᵥ (w + Q w • (N *ᵥ x)) = N *ᵥ w := by
      rw [mulVec_add, mulVec_smul, hNN, smul_zero, add_zero]
    have h1 := hroot (N *ᵥ (w + Q w • (N *ᵥ x))) (w + Q w • (N *ᵥ x)) (hsing _) (by
        rw [quad_add, QuadraticMap.map_smul, hsing, map_smul, smul_eq_mul, smul_eq_mul, hwx]
        rw [mul_zero, add_zero, mul_one, CharTwo.add_self_eq_zero]) (by rw [hBs]; exact halt _)
      (cTwoX_commute_typeA hN hadj _)
    rw [hNw', cTwoX_add_smul_right, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, hXNN w x] at h1
    exact add_right_cancel h1
  obtain ⟨c, hc⟩ := commutant_typeA hQ hN hadj halt hN0 hUB (hcomm U hUM) hτ
  refine central_of_commute_all hZ hpM hM2' hu2 hU fun X _ hXM => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM]

end Groups

end CFSG.ComponentClassification.RankTwoClassical
