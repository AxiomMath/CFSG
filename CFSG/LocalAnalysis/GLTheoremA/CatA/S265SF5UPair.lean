module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5URegDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (gramSU)
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {m : ℕ} {F : Type} [Field F]

theorem exists_conj_eq_scalar_mul_ne_one (hF : UnitaryFieldData 2 m F) (h5 : 5 ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)))}
    (hXD : X ≤ primeFormD hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
    (hX : IsElemAbelian 5 X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer 5 (fixSubgroup α) = ⊥)
    (hcard : Nat.card X = 5 ^ 2)
    {S : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)}
    (hS : MulAut.conj (S : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) ∈ X)
    (hS1 : MulAut.conj (S : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) ≠ 1) :
    ∃ A : primeFormUnitary hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A ∈ X ∧
        ∃ c : Fˣ, c ^ 5 = 1 ∧ c ≠ 1 ∧ (A : GL (Fin 5) F) * S * (A : GL (Fin 5) F)⁻¹ =
          GeneralLinearGroup.scalar (Fin 5) c * S := by
  have hq : 3 < 2 ^ m := by
    have := Nat.le_of_dvd (by positivity) h5
    omega
  have hne : ¬(5 = 3 ∧ 2 ^ m = 2) := fun h' => by omega
  have hρS := primeFormConjHom_eq_conj hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) S
  obtain ⟨P, hP, t, htinj, -, hNt⟩ := exists_unitary_diag_injective hF h5 hX hnl
    (A := ⟨S, S.2.1⟩) S.2.2 (by rw [hρS]; exact hS) (by rw [hρS]; exact hS1)
  have hNt' : ((P⁻¹ * (S : GL (Fin 5) F) * P : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      diagonal t := hNt
  by_contra hall
  push Not at hall
  have hle := SF.card_le_of_unitary_diag_nl hF (by norm_num) Nat.prime_five hq h5 hXD hX hnl hP
    fun A hA => ?_
  · rw [hcard] at hle
    norm_num at hle
  have hcomm : primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
      (A * ⟨S, S.2.1⟩ * A⁻¹ * (⟨S, S.2.1⟩ : primeFormUnitary hF
        ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρS, hX.comm hA hS, mul_inv_cancel_right,
      mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne _).1 hcomm
  have hASA : (A : GL (Fin 5) F) * S * (A : GL (Fin 5) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) c * S := mul_inv_eq_iff_eq_mul.1 hc
  have hc5 : c ^ 5 = 1 := by
    have h1 := congrArg GeneralLinearGroup.det hASA
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, map_mul, GeneralLinearGroup.det_scalar,
      Fintype.card_fin] at h1
    exact mul_eq_right.1 h1.symm
  have hc1 : c = 1 := by
    by_contra hc1
    exact hall A hA c hc5 hc1 hASA
  have hAS : (A : GL (Fin 5) F) * S = S * A := by
    rw [hc1, map_one, one_mul] at hASA
    exact mul_inv_eq_iff_eq_mul.1 hASA
  have hMS : (P⁻¹ * A * P) * (P⁻¹ * S * P) = (P⁻¹ * S * P) * (P⁻¹ * (A : GL (Fin 5) F) * P) := by
    calc _ = P⁻¹ * ((A : GL (Fin 5) F) * S) * P := by group
      _ = P⁻¹ * ((S : GL (Fin 5) F) * A) * P := by rw [hAS]
      _ = _ := by group
  have hMS' := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F)) hMS
  simp only [Units.val_mul (P⁻¹ * (A : GL (Fin 5) F) * P),
    Units.val_mul (P⁻¹ * (S : GL (Fin 5) F) * P)] at hMS'
  rw [hNt'] at hMS'
  intro i j hij
  have h1 := congrFun (congrFun hMS' i) j
  rw [mul_diagonal, diagonal_mul] at h1
  have h2 : (t i - t j) * ((P⁻¹ * (A : GL (Fin 5) F) * P : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F) i j = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (htinj (sub_eq_zero.1 h)) hij
  · exact h

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
