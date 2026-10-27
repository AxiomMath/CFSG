module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenTypeOne
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.SemisimpleCentralizers.Held
open scoped commutatorElement

variable {K : Type} [Field K] {n d p : ℕ}

theorem exists_scalar_mul_mem_heldGU [Finite K] {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x)
    (hτq : ∀ x, τ x = x ^ 2 ^ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (A₀ : GL (Fin d) K) (hA₀ : A₀ ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    ∃ σ : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin d) σ * A₀ ∈ heldGU d K τ hτ := by
  obtain ⟨μ, hμ0, hμq, hA⟩ := hA₀
  obtain ⟨c, hc0, hcμ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_qplus1_root hK hμ0 hμq
  refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), ?_⟩
  rw [mem_heldGU]
  have hτf : (⇑τ) = fun x => x ^ 2 ^ n := funext hτq
  have hval : ((Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c⁻¹ (inv_ne_zero hc0)) * A₀ :
      GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (c⁻¹ : K) • (A₀ : Matrix (Fin d) (Fin d) K) := by
    rw [Units.val_mul, CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.val_scalar_gl', Matrix.smul_mul,
      Matrix.one_mul]
    rfl
  have hscal : (c⁻¹ : K) ^ 2 ^ n * c⁻¹ * μ = 1 := by
    rw [← hcμ, pow_succ, inv_pow]
    have hc' : c ^ 2 ^ n ≠ 0 := pow_ne_zero _ hc0
    field_simp
  rw [hval, hτf, CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.map_smul_pow, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, smul_smul, hscal, one_smul]

theorem commutatorElement_mem_heldGU {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x)
    (hτq : ∀ x, τ x = x ^ 2 ^ n) (hK : Nat.card K = (2 ^ n) ^ 2) [Finite K]
    {D B : GL (Fin d) K} (hD : D ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hB : B ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    ⁅D, B⁆ ∈ heldGU d K τ hτ := by
  obtain ⟨σD, hDσ⟩ := exists_scalar_mul_mem_heldGU (d := d) hτ hτq hK D hD
  obtain ⟨σB, hBσ⟩ := exists_scalar_mul_mem_heldGU (d := d) hτ hτq hK B hB
  have hcomm : ⁅Matrix.GeneralLinearGroup.scalar (Fin d) σD * D,
      Matrix.GeneralLinearGroup.scalar (Fin d) σB * B⁆ = ⁅D, B⁆ :=
    CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center
      (Subgroup.mem_center_iff.2 fun x =>
        (Matrix.GeneralLinearGroup.scalar_commute σD x).symm)
      (Subgroup.mem_center_iff.2 fun x =>
        (Matrix.GeneralLinearGroup.scalar_commute σB x).symm) D B
  rw [← hcomm]
  exact mul_mem (mul_mem (mul_mem hDσ hBσ) (inv_mem hDσ)) (inv_mem hBσ)

theorem commute_of_mem_heldGU (h : UnitaryFieldData 2 n K) [Finite K]
    {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x) (hτq : ∀ x, τ x = x ^ 2 ^ n)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    (hnd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1)
    {D B : GL (Fin d) K} (hD : D ∈ heldGU d K τ hτ) (hB : B ∈ heldGU d K τ hτ)
    (hDN : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hDp : (TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩) ^ p = 1)
    (hBp : (TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩) ^ p = 1)
    (hcomm : TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ =
      TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ *
        TableB.projConj (unitarySU 2 n K d) ⟨D, hDN⟩) :
    D * B = B * D := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hXN : (⁅D, B⁆ : GL (Fin d) K) ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hDN hBN) (Subgroup.inv_mem _ hDN)) (Subgroup.inv_mem _ hBN)
  have hXproj : TableB.projConj (unitarySU 2 n K d) ⟨⁅D, B⁆, hXN⟩ = 1 := by
    have heq : (⟨⁅D, B⁆, hXN⟩ : Subgroup.normalizer
          (unitarySU 2 n K d : Set (GL (Fin d) K))) =
        (⟨D, hDN⟩ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) *
          ⟨B, hBN⟩ * ⟨D, hDN⟩⁻¹ * ⟨B, hBN⟩⁻¹ := by
      apply Subtype.ext
      change (⁅D, B⁆ : GL (Fin d) K) = D * B * D⁻¹ * B⁻¹
      rw [commutatorElement_def]
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hd hdq hXN hXproj
  have hcq : (c : K) ^ (2 ^ n + 1) = 1 := by
    have hmem : (⁅D, B⁆ : GL (Fin d) K) ∈ heldGU d K τ hτ :=
      mul_mem (mul_mem (mul_mem hD hB) (inv_mem hD)) (inv_mem hB)
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
  have hDp_scal : ∃ cD : Kˣ, D ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) cD := by
    have hDNp : D ^ p ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      Subgroup.pow_mem _ hDN p
    have hproj : TableB.projConj (unitarySU 2 n K d) ⟨D ^ p, hDNp⟩ = 1 := by
      have h1 : (⟨D ^ p, hDNp⟩ : Subgroup.normalizer
            (unitarySU 2 n K d : Set (GL (Fin d) K))) =
          (⟨D, hDN⟩ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) ^ p :=
        Subtype.ext rfl
      rw [h1, map_pow, hDp]
    obtain ⟨cD, hcD⟩ := mem_scalars_of_projConj_eq_one h hd hdq hDNp hproj
    exact ⟨cD, hcD.symm⟩
  have hBp_scal : ∃ cB : Kˣ, B ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) cB := by
    have hBNp : B ^ p ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      Subgroup.pow_mem _ hBN p
    have hproj : TableB.projConj (unitarySU 2 n K d) ⟨B ^ p, hBNp⟩ = 1 := by
      have h1 : (⟨B ^ p, hBNp⟩ : Subgroup.normalizer
            (unitarySU 2 n K d : Set (GL (Fin d) K))) =
          (⟨B, hBN⟩ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) ^ p :=
        Subtype.ext rfl
      rw [h1, map_pow, hBp]
    obtain ⟨cB, hcB⟩ := mem_scalars_of_projConj_eq_one h hd hdq hBNp hproj
    exact ⟨cB, hcB.symm⟩
  have hXp : (⁅D, B⁆ : GL (Fin d) K) ^ p = 1 := by
    obtain ⟨cB, hcB⟩ := hBp_scal
    have hXB : Commute (⁅D, B⁆ : GL (Fin d) K) B := by
      rw [← hc]
      exact (commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute c B)
    have hconj : (D * B * D⁻¹) ^ p = ⁅D, B⁆ ^ p * B ^ p := by
      have hDB : D * B * D⁻¹ = ⁅D, B⁆ * B := by rw [commutatorElement_def]; group
      rw [hDB, hXB.mul_pow]
    have hconj2 : (D * B * D⁻¹) ^ p = B ^ p := by
      have hk : ∀ k : ℕ, (D * B * D⁻¹) ^ k = D * B ^ k * D⁻¹ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, ih]; group
      rw [hk p, hcB]
      calc D * Matrix.GeneralLinearGroup.scalar (Fin d) cB * D⁻¹
          = Matrix.GeneralLinearGroup.scalar (Fin d) cB * D * D⁻¹ := by
            rw [(Matrix.GeneralLinearGroup.scalar_commute cB D).symm]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) cB * (D * D⁻¹) := by rw [mul_assoc]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) cB := by rw [mul_inv_cancel, mul_one]
    have h1 : B ^ p = ⁅D, B⁆ ^ p * B ^ p := by rw [← hconj, hconj2]
    calc ⁅D, B⁆ ^ p = ⁅D, B⁆ ^ p * (B ^ p * (B ^ p)⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = (⁅D, B⁆ ^ p * B ^ p) * (B ^ p)⁻¹ := by group
      _ = B ^ p * (B ^ p)⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel _
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
    have hdet : Matrix.GeneralLinearGroup.det (⁅D, B⁆ : GL (Fin d) K) = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      simp [mul_comm, mul_left_comm, mul_assoc]
    have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) c) =
        Matrix.GeneralLinearGroup.det (⁅D, B⁆ : GL (Fin d) K) := by rw [hc]
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
  have hX1 : (⁅D, B⁆ : GL (Fin d) K) = 1 := by rw [← hc, hc1, map_one]
  calc D * B = D * B * D⁻¹ * B⁻¹ * (B * D) := by group
    _ = ⁅D, B⁆ * (B * D) := by rw [commutatorElement_def]
    _ = B * D := by rw [hX1, one_mul]

theorem exists_pow_eq_of_scalar_pow (h : UnitaryFieldData 2 n K) [Finite K]
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    (hnd : ¬ p ∣ 2 ^ n + 1 ∨ ¬ p ∣ d)
    {B : GL (Fin d) K} (hB : B ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hBp : (TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩) ^ p = 1)
    {c : Kˣ} (hc : B ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    ∃ lam : Kˣ, lam ^ p = c := by
  rcases hnd with hpq | hpd
  ·
    obtain ⟨μ, hμ⟩ := norm_scalar_of_pow_eq_scalar h (by omega : 1 ≤ d) hB hc
    have hcop : Nat.Coprime (2 ^ n + 1) p :=
      ((hp.coprime_iff_not_dvd).2 hpq).symm
    have hμ' : (c : K) ^ (2 ^ n + 1) = (μ : K) ^ p :=
      congrArg (fun u : Kˣ => (u : K)) hμ
    obtain ⟨x, hxc, -⟩ :=
      (pow_eq_pow_iff_of_coprime (a := (c : K)) (b := (μ : K)) hcop).1 hμ'
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hxc
      exact c.ne_zero hxc
    exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hxc.symm)⟩
  ·
    have h1 : (c : Kˣ) ^ d = (Matrix.GeneralLinearGroup.det B) ^ p := by
      have h2 : Matrix.GeneralLinearGroup.det (B ^ p) =
          (Matrix.GeneralLinearGroup.det B) ^ p := map_pow _ _ _
      rw [hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h2
      exact h2
    have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.2 hpd).symm
    have h1' : (c : K) ^ d = (((Matrix.GeneralLinearGroup.det B : Kˣ)) : K) ^ p :=
      congrArg (fun u : Kˣ => (u : K)) h1
    obtain ⟨x, hxc, -⟩ :=
      (pow_eq_pow_iff_of_coprime (a := (c : K))
        (b := ((Matrix.GeneralLinearGroup.det B : Kˣ) : K)) hcop).1 h1'
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hxc
      exact c.ne_zero hxc
    exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hxc.symm)⟩

theorem exists_pow_eq_one_of_projConj_pow_eq_one_of_not_shape (h : UnitaryFieldData 2 n K)
    [Finite K] (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    (hnd : ¬ p ∣ 2 ^ n + 1 ∨ ¬ p ∣ d)
    {B : GL (Fin d) K} (hB : B ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hBp : (TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩) ^ p = 1) :
    ∃ (B' : GL (Fin d) K) (_ : B' ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
      (hB'N : B' ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      B' ^ p = 1 ∧
        TableB.projConj (unitarySU 2 n K d) ⟨B', hB'N⟩ =
          TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩ := by
  classical
  haveI := h.finite
  obtain ⟨c, hc⟩ := exists_scalar_of_projConj_pow_eq_one h hd hdq hp hB hBN hBp
  obtain ⟨lam, hlam⟩ := exists_pow_eq_of_scalar_pow h hd hdq hp hnd hB hBN hBp hc
  let B' : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) lam⁻¹ * B
  have hB'gu : B' ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := scalar_mul_mem_guSet h hB lam⁻¹
  have hscalMem : Matrix.GeneralLinearGroup.scalar (Fin d) lam⁻¹ ∈
      LargeEvenScalars (Fin d) K := by
    rw [largeEvenScalars_def]
    exact ⟨lam⁻¹, rfl⟩
  have hscalN : Matrix.GeneralLinearGroup.scalar (Fin d) lam⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    TableB.scalar_mem_normalizer (unitarySU 2 n K d) hscalMem
  have hB'N : B' ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.mul_mem _ hscalN hBN
  have hB'p : B' ^ p = 1 := by
    have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) lam⁻¹) B :=
      (commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute lam⁻¹ B)
    have h1 : (Matrix.GeneralLinearGroup.scalar (Fin d) lam⁻¹) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ := by
      rw [← map_pow, inv_pow, hlam]
    dsimp only [B']
    calc B' ^ p = (Matrix.GeneralLinearGroup.scalar (Fin d) lam⁻¹) ^ p * B ^ p :=
          hcomm.mul_pow p
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ *
            Matrix.GeneralLinearGroup.scalar (Fin d) c := by rw [h1, hc]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨B', hB'gu, hB'N, hB'p, ?_⟩
  have hsub : (⟨B', hB'N⟩ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) =
      (⟨Matrix.GeneralLinearGroup.scalar (Fin d) lam⁻¹, hscalN⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) * ⟨B, hBN⟩ :=
    Subtype.ext rfl
  rw [hsub, map_mul, TableB.projConj_of_scalar (unitarySU 2 n K d) hscalMem, one_mul]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
