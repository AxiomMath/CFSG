module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniTransPow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SemisimpleCentralizers.Held
open scoped commutatorElement

variable {K : Type} [Field K] {n d p : ℕ}

theorem commute_of_gu_of_not_shape (h : UnitaryFieldData 2 n K) [Finite K]
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    (hnd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1)
    {D B : GL (Fin d) K} (hD : D ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hB : B ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hDN : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hDp : D ^ p = 1) (hBp : B ^ p = 1)
    (hcomm : TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ =
      TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩) :
    D * B = B * D := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hbij : Function.Bijective h.bar :=
    ⟨fun x y hxy => by
        have h1 := congrArg h.bar hxy
        rwa [h.bar_bar, h.bar_bar] at h1,
      fun y => ⟨h.bar y, h.bar_bar y⟩⟩
  let τ : K ≃+* K := RingEquiv.ofBijective h.bar hbij
  have hτ : ∀ x, τ (τ x) = x := fun x => h.bar_bar x
  have hτq : ∀ x, τ x = x ^ 2 ^ n := fun x => h.bar_apply x
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 * n = n * 2 by omega, ← pow_mul]
  set X : GL (Fin d) K := D * B * D⁻¹ * B⁻¹ with hX
  have hXN : X ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hDN hBN) (Subgroup.inv_mem _ hDN)) (Subgroup.inv_mem _ hBN)
  have hXproj : TableB.projConj (unitarySU 2 n K d) ⟨X, hXN⟩ = 1 := by
    have heq : (⟨X, hXN⟩ : Subgroup.normalizer
          (unitarySU 2 n K d : Set (GL (Fin d) K))) =
        (⟨D, hDN⟩ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) *
          ⟨B, hBN⟩ * ⟨D, hDN⟩⁻¹ * ⟨B, hBN⟩⁻¹ := Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    change TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩ *
        (TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩)⁻¹ *
        (TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩)⁻¹ = 1
    group
  obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hd hdq hXN hXproj
  have hXc : Commute X B := by
    rw [← hc]
    exact (commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute c B)
  have hXp : X ^ p = 1 := by
    have hconj : (D * B * D⁻¹) ^ p = X ^ p * B ^ p := by
      have hDB : D * B * D⁻¹ = X * B := by rw [hX]; group
      rw [hDB, hXc.mul_pow]
    have hconj2 : (D * B * D⁻¹) ^ p = 1 := by
      have hk : ∀ k : ℕ, (D * B * D⁻¹) ^ k = D * B ^ k * D⁻¹ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, ih]; group
      rw [hk p, hBp, mul_one, mul_inv_cancel]
    rw [hconj2, hBp, mul_one] at hconj
    exact hconj.symm
  have hcq : (c : K) ^ (2 ^ n + 1) = 1 := by
    have hmem : X ∈ heldGU d K τ hτ := by
      have h : (⁅D, B⁆ : GL (Fin d) K) ∈ heldGU d K τ hτ :=
        commutatorElement_mem_heldGU hτ hτq hK hD hB
      rwa [commutatorElement_def, ← hX] at h
    rw [mem_heldGU] at hmem
    have hval : ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = (c : K) • (1 : Matrix (Fin d) (Fin d) K) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.val_scalar_gl' c
    have hmap2 : Matrix.transpose (((c : K) • (1 : Matrix (Fin d) (Fin d) K)).map τ) =
        (τ (c : K)) • (1 : Matrix (Fin d) (Fin d) K) := by
      ext i j
      rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.smul_apply, Matrix.one_apply]
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji, Ne.symm hji]
    rw [← hc, hval, hmap2, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hmem
    have h00 : (τ (c : K)) * (c : K) = 1 := by
      have h1 := congrFun (congrFun hmem (⟨0, by omega⟩ : Fin d)) (⟨0, by omega⟩ : Fin d)
      simpa using h1
    rw [hτq] at h00
    rw [pow_succ]
    exact h00
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin d) : Kˣ → GL (Fin d) K) := by
    intro a b hab
    have h1 : Matrix.scalar (Fin d) (a : K) = Matrix.scalar (Fin d) (b : K) := by
      simpa only [Matrix.GeneralLinearGroup.coe_scalar] using congrArg Units.val hab
    exact Units.ext (Matrix.scalar_inj.mp h1)
  have hcp : c ^ p = 1 := by
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin d) (c ^ p) = 1 := by
      rw [map_pow, hc]
      exact hXp
    exact hinj (by simpa using h2)
  have hcd : c ^ d = 1 := by
    have hdet : Matrix.GeneralLinearGroup.det X = 1 := by
      rw [hX, map_mul, map_mul, map_mul, map_inv, map_inv]
      simp [mul_comm, mul_left_comm, mul_assoc]
    have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) c) =
        Matrix.GeneralLinearGroup.det X := by rw [hc]
    rw [hdet, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
    exact h1
  have hc1 : c = 1 := by
    rcases hnd with hnd | hnd
    · have h1 : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.2 hcp
      have h2 : orderOf c ∣ d := orderOf_dvd_iff_pow_eq_one.2 hcd
      have h3 : orderOf c ∣ Nat.gcd p d := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one (hp.coprime_iff_not_dvd.2 hnd)] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    · have h1 : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.2 hcp
      have h2 : orderOf c ∣ 2 ^ n + 1 :=
        orderOf_dvd_iff_pow_eq_one.2 (Units.ext (by simpa using hcq))
      have h3 : orderOf c ∣ Nat.gcd p (2 ^ n + 1) := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one (hp.coprime_iff_not_dvd.2 hnd)] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hX1 : X = 1 := by rw [← hc, hc1, map_one]
  calc D * B = D * B * D⁻¹ * B⁻¹ * (B * D) := by group
    _ = X * (B * D) := by rw [hX]
    _ = B * D := by rw [hX1, one_mul]

theorem exists_commuting_pow_one_gu_lifts_of_not_shape (h : UnitaryFieldData 2 n K) [Finite K]
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    (hnd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1)
    {D B : GL (Fin d) K} (hD : D ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hB : B ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hDN : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hDp : (TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩) ^ p = 1)
    (hBp : (TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩) ^ p = 1)
    (hcomm : TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ =
      TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩) :
    ∃ (D' B' : GL (Fin d) K)
      (_ : D' ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
      (_ : B' ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
      (hD'N : D' ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
      (hB'N : B' ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      D' ^ p = 1 ∧ B' ^ p = 1 ∧ Commute D' B' ∧
        TableB.projConj (unitarySU 2 n K d) ⟨D', hD'N⟩ =
          TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩ ∧
        TableB.projConj (unitarySU 2 n K d) ⟨B', hB'N⟩ =
          TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ := by
  obtain ⟨D', hD'gu, hD'N, hD'p, hD'proj⟩ :=
    exists_pow_eq_one_of_projConj_pow_eq_one_of_not_shape h hd hdq hp hnd.symm hD hDN hDp
  obtain ⟨B', hB'gu, hB'N, hB'p, hB'proj⟩ :=
    exists_pow_eq_one_of_projConj_pow_eq_one_of_not_shape h hd hdq hp hnd.symm hB hBN hBp
  have hcomm' : TableB.projConj (unitarySU 2 n K d) ⟨D', hD'N⟩ *
      TableB.projConj (unitarySU 2 n K d) ⟨B', hB'N⟩ =
      TableB.projConj (unitarySU 2 n K d) ⟨B', hB'N⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨D', hD'N⟩ := by
    rw [hD'proj, hB'proj]
    exact hcomm
  exact ⟨D', B', hD'gu, hB'gu, hD'N, hB'N, hD'p, hB'p,
    commute_of_gu_of_not_shape h hd hdq hp hnd hD'gu hB'gu hD'N hB'N hD'p hB'p hcomm',
    hD'proj, hB'proj⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
