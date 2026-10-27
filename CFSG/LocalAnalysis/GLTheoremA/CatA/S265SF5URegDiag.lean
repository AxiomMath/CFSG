module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMat
import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
  (scalarU coe_scalarU rescale_pow_eq_one norm_eq_one_of_pow_norm)

section Roots

variable {F : Type} [Field F]

private theorem exists_apply_eq_of_injective {t : Fin 5 → F} (ht : Function.Injective t)
    (h5 : ∀ i, t i ^ 5 = 1) {z : F} (hz : z ^ 5 = 1) : ∃ j, t j = z := by
  classical
  by_contra hne
  push Not at hne
  have hsub : insert z (Finset.univ.image t) ⊆ (Polynomial.nthRoots 5 (1 : F)).toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hz
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact h5 i
  have hz' : z ∉ Finset.univ.image t := fun hmem => by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
    exact hne j hj
  have h1 := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 5 (1 : F)))
  rw [Finset.card_insert_of_notMem hz', Finset.card_image_of_injective _ ht, Finset.card_univ,
    Fintype.card_fin] at h1
  omega

theorem exists_perm_apply_eq_inv {t : Fin 5 → F} (ht : Function.Injective t)
    (h5 : ∀ i, t i ^ 5 = 1) : ∃ τ : Equiv.Perm (Fin 5), ∀ i, t (τ i) = (t i)⁻¹ := by
  choose g hg using fun i => exists_apply_eq_of_injective ht h5 (z := (t i)⁻¹)
    (by rw [inv_pow, h5, inv_one])
  have hinj : Function.Injective g := fun i j hij =>
    ht (inv_injective (by rw [← hg i, ← hg j, hij]))
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hinj), hg⟩

private theorem prod_eq_one_of_injective {t : Fin 5 → F} (ht : Function.Injective t)
    (h5 : ∀ i, t i ^ 5 = 1) : ∏ i, t i = 1 := by
  obtain ⟨τ, hτ⟩ := exists_perm_apply_eq_inv ht h5
  set x := ∏ i, t i with hx
  have hx5 : x ^ 5 = 1 := by
    rw [hx, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => h5 i
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx5
  have hinv : x⁻¹ = x := by
    rw [hx, ← Finset.prod_inv_distrib, ← Equiv.prod_comp τ t]
    exact Finset.prod_congr rfl fun i _ => (hτ i).symm
  have hsq : x ^ 2 = 1 := by
    rw [sq]
    nth_rw 1 [← hinv]
    exact inv_mul_cancel₀ hx0
  linear_combination hx5 - x * (x ^ 2 + 1) * hsq

end Roots

variable {m : ℕ} {F : Type} [Field F]

theorem exists_unitary_diag_injective (hF : UnitaryFieldData 2 m F) (h5 : 5 ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)))}
    (hX : IsElemAbelian 5 X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer 5 (fixSubgroup α) = ⊥)
    {A : primeFormUnitary hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)}
    (hdet : ((A : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1)
    (hA : primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A ∈ X)
    (hA1 : primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A ≠ 1) :
    ∃ P ∈ primeFormUnitary hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      ∃ t : Fin 5 → F, Function.Injective t ∧ (∀ i, t i ^ 5 = 1) ∧
        ((P⁻¹ * (A : GL (Fin 5) F) * P : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
          diagonal t := by
  haveI := hF.finite
  have hq : 3 < 2 ^ m := by
    have := Nat.le_of_dvd (by positivity) h5
    omega
  have hne : ¬(5 = 3 ∧ 2 ^ m = 2) := fun h' => by omega
  obtain ⟨c, hcN, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne (A ^ 5)).1
    (by rw [map_pow]; exact hX.2 _ hA)
  rw [Subgroup.coe_pow] at hc
  have hcM : ((A : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) ^ 5 =
      Matrix.scalar (Fin 5) (c : F) := by
    rw [← Units.val_pow_eq_pow_val, hc, GeneralLinearGroup.coe_scalar]
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, u ^ 5 = c := by
    by_contra hnot
    have hω : ∀ b : F, b ^ 5 ≠ (c : F) := fun b hb => by
      have hb0 : b ≠ 0 := fun h0 => c.ne_zero (by rw [← hb, h0, zero_pow (by norm_num)])
      exact hnot ⟨Units.mk0 b hb0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hb])⟩
    have h1 := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA.det_eq_of_pow_eq_scalar
      Nat.prime_five (by norm_num) hcM hω
    exact hω 1 (by rw [one_pow, ← h1, hdet])
  have hun : hF.norm ((u⁻¹ : Fˣ) : F) = 1 := by
    refine norm_eq_one_of_pow_norm Nat.prime_five (by norm_num) h5 ?_
    rw [inv_pow, hu, ← pow_succ_eq_one_iff_norm hF, inv_pow, hcN, inv_one]
  have hAu : (A : GL (Fin 5) F) ^ 5 = GeneralLinearGroup.scalar (Fin 5) (u ^ 5) := by
    rw [hu, hc]
  set A' := scalarU hF 5 u⁻¹ hun * A with hA'
  have hA'5 : A' ^ 5 = 1 := rescale_pow_eq_one (by norm_num) hne hun hAu
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hF Nat.prime_five h5
    (Subgroup.zpowers A') (fun x hx y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow_self A' k l).eq)
    (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm k, _root_.zpow_mul, zpow_natCast, hA'5,
        _root_.one_zpow])
  have hdiag : (((P : GL (Fin 5) F)⁻¹ * (A : GL (Fin 5) F) * P : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F).IsDiag := by
    have e : (((P⁻¹ * A' * P : primeFormUnitary hF (idGram F 5)) : GL (Fin 5) F) :
        Matrix (Fin 5) (Fin 5) F) = ((u⁻¹ : Fˣ) : F) •
          (((P : GL (Fin 5) F)⁻¹ * (A : GL (Fin 5) F) * P : GL (Fin 5) F) :
            Matrix (Fin 5) (Fin 5) F) := by
      simp only [hA', Subgroup.coe_mul, Subgroup.coe_inv, coe_scalarU, Units.val_mul,
        GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_eq_diagonal_mul, Matrix.mul_smul,
        Matrix.smul_mul]
    have h1 := (hP A' (Subgroup.mem_zpowers A')).smul (u : F)
    rwa [e, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] at h1
  obtain ⟨t, hNt⟩ : ∃ t : Fin 5 → F, (((P : GL (Fin 5) F)⁻¹ * (A : GL (Fin 5) F) * P :
      GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = diagonal t := ⟨_, hdiag.diagonal_diag.symm⟩
  have htinj : Function.Injective t := fun i j hij => by
    by_contra hij'
    exact SF.glaPLayer_ne_bot_of_unitary_diag_eq hF (by norm_num) Nat.prime_five hq h5 hc P.2
      hNt hij' hij (hnl _ hA hA1)
  have hprod : ∏ i, t i = 1 := by
    rw [← det_diagonal, ← hNt, Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one,
      ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  have hP5 : ((P : GL (Fin 5) F)⁻¹ * (A : GL (Fin 5) F) * P) ^ 5 =
      GeneralLinearGroup.scalar (Fin 5) c := by
    have h1 : ((P : GL (Fin 5) F)⁻¹ * (A : GL (Fin 5) F) * (P : GL (Fin 5) F)⁻¹⁻¹) ^ 5 =
        GeneralLinearGroup.scalar (Fin 5) c := by
      rw [conj_pow, hc, ← GeneralLinearGroup.scalar_commute c (P : GL (Fin 5) F)⁻¹,
        mul_inv_cancel_right]
    rwa [inv_inv] at h1
  have ht5c : ∀ i, t i ^ 5 = c := fun i => by
    have h2 := congrArg (fun B : GL (Fin 5) F => (B : Matrix (Fin 5) (Fin 5) F) i i) hP5
    simpa only [Units.val_pow_eq_pow_val, hNt, diagonal_pow, diagonal_apply_eq, Pi.pow_apply,
      GeneralLinearGroup.coe_scalar, scalar_apply] using h2
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have huc : (u : F) ^ 5 = c := by rw [← Units.val_pow_eq_pow_val, hu]
  have hd1 := prod_eq_one_of_injective (t := fun i => t i * (u : F)⁻¹)
    (fun i j hij => htinj (mul_right_cancel₀ (inv_ne_zero hu0) hij))
    (fun i => show (t i * (u : F)⁻¹) ^ 5 = 1 by
      rw [mul_pow, ht5c, inv_pow, huc, mul_inv_cancel₀ c.ne_zero])
  rw [Finset.prod_mul_distrib, hprod, Fin.prod_const, inv_pow, huc, one_mul, inv_eq_one] at hd1
  exact ⟨P, P.2, t, htinj, fun i => by rw [ht5c, hd1], hNt⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
