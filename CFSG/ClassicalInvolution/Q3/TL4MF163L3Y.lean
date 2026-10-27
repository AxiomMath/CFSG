module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3A
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem conjAut_inv_proj_blkP (Q : GL (Fin 3) K) (A : GL (Fin 2) K) :
    (conjAut 3 K Q)⁻¹ (proj 3 K (blkP Q A)) = proj 3 K (blkP 1 A) := by
  rw [← map_inv, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  show ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((Q * Lemma41aL3.blk A * Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Q⁻¹⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((1 * Lemma41aL3.blk A * 1⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem conjAut_toGL (g : SL(3, K)) :
    conjAut 3 K (SpecialLinearGroup.toGL g) = MulAut.conj (proj 3 K g) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective 3 K x
  rw [conjAut_proj, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  show (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    ((g * y * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
  rfl

theorem commutator_conj {P : Type} [Group P] (x : P) (φ : MulAut P) :
    ⁅MulAut.conj x, φ⁆ = MulAut.conj (x * (φ x)⁻¹) := by
  have h : φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
    ext w
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulAut.apply_inv_self, MulAut.conj_apply]
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc φ,
    show φ * (MulAut.conj x)⁻¹ * φ⁻¹ = (φ * MulAut.conj x * φ⁻¹)⁻¹ by group, h, map_mul, map_inv]

theorem proj_blkP_scalar_cube {ω : Kˣ} (hω : ω ^ 3 = 1) :
    proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) ω)) = 1 := by
  rw [proj_eq_one_iff, mem_scalars]
  refine ⟨ω, hω, ?_⟩
  rw [coe_blkP_one, GeneralLinearGroup.coe_scalar]
  have hω0 : (ω : K) ≠ 0 := ω.ne_zero
  have hω3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
  have hdet : (scalar (Fin 2) (ω : K)).det⁻¹ = ω := by
    rw [Matrix.det_fin_two]
    simp
    field_simp
    linear_combination -hω3
  rw [hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem exists_orderOf_eight [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {τ : K ≃+* K} (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) :
    ∃ μ : Kˣ, orderOf μ = 8 := by
  obtain ⟨-, -, -, -, hAut, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hAut]; omega)
  have h2 : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ) hτ1
  have hf2 : 2 ∣ f := hAut ▸ h2 ▸ orderOf_dvd_natCard τ
  obtain ⟨k, rfl⟩ := hf2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp8 : p ^ 2 ≡ 1 [MOD 8] := by
    obtain ⟨m, rfl⟩ := hodd
    unfold Nat.ModEq
    rw [Nat.pow_mod]
    have : (2 * m + 1) % 8 = 1 ∨ (2 * m + 1) % 8 = 3 ∨ (2 * m + 1) % 8 = 5 ∨
        (2 * m + 1) % 8 = 7 := by omega
    rcases this with h | h | h | h <;> rw [h]
  have h8 : 8 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK, pow_mul]
    have hk : (p ^ 2) ^ k ≡ 1 [MOD 8] := by simpa using hp8.pow k
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow k (p ^ 2) (pow_pos hp.pos 2))).1 hk.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨d, hd⟩ := h8
  have hd0 : d ≠ 0 := by
    rintro rfl
    have : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
    omega
  refine ⟨g ^ d, ?_⟩
  rw [orderOf_pow' g hd0, hog, hd, Nat.gcd_mul_left_left]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)

end CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
