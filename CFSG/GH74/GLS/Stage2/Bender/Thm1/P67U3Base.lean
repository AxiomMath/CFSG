module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

abbrev U3T : Type :=
  primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

abbrev U3U : Subgroup (GL (Fin 3) K) :=
  primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem u3_conj_eq_one_iff (A : U3U h) :
    primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A = 1 ↔
      ∃ c : Kˣ, (A : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  constructor
  · intro hA
    have h1 : primeFormPsi h (isPrimeFormGram_one (n := 3)) ⟨A, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one, hA]
    obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h (isPrimeFormGram_one (n := 3))
      (le_refl 3) ⟨A, 1⟩).1 h1
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [primeFormConjHom_mk]
    have e : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ = g := by
      rw [hc, ← (commute_scalar c (g : GL (Fin 3) K)).eq, mul_inv_cancel_right]
    congr 1
    exact Subtype.ext e

theorem u3_SUid_eq [Finite K] [Fact p.Prime] [CharP K p] :
    SUid (CFSG.LieType.BorelTits.unitaryInvolution K p f) 3 =
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  (SUid_eq_statedSU h.card_eq_sq 3).trans (unitarySU_eq_gramSU h 3)

@[expose] noncomputable def u3Psi (F : U3U h) : ↥(gramSU h ((1 : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)) →* U3T h :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)) 3)).comp
    (primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) F).toMonoidHom

theorem u3Psi_surjective (F : U3U h) : Function.Surjective (u3Psi h F) := by
  intro t
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ t
  exact ⟨(primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) F).symm g',
    by simp [u3Psi]⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
