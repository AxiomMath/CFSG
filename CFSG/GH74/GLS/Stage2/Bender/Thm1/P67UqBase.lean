module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (n : ℕ)

abbrev UqT : Type :=
  primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

abbrev UqU : Subgroup (GL (Fin n) K) :=
  primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

variable {n}

theorem uq_conj_eq_one_iff (hn : 3 ≤ n) (A : UqU h n) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A = 1 ↔
      ∃ c : Kˣ, (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  constructor
  · intro hA
    have h1 : primeFormPsi h (isPrimeFormGram_one (n := n)) ⟨A, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one, hA]
    obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h (isPrimeFormGram_one (n := n))
      hn ⟨A, 1⟩).1 h1
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [primeFormConjHom_mk]
    have e : (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g := by
      rw [hc, ← (commute_scalar c (g : GL (Fin n) K)).eq, mul_inv_cancel_right]
    congr 1
    exact Subtype.ext e

theorem uq_SUid_eq [Finite K] [Fact p.Prime] [CharP K p] :
    SUid (CFSG.LieType.BorelTits.unitaryInvolution K p f) n =
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  (SUid_eq_statedSU h.card_eq_sq n).trans (unitarySU_eq_gramSU h n)

variable (n) in
@[expose] noncomputable def uqPsi (F : UqU h n) : ↥(gramSU h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) →* UqT h n :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) n)).comp
    (primeFormConjSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) F).toMonoidHom

theorem uqPsi_surjective (F : UqU h n) : Function.Surjective (uqPsi h n F) := by
  intro t
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ t
  exact ⟨(primeFormConjSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) F).symm g',
    by simp [uqPsi]⟩

theorem uq_conj_mem_D (y : UqT h n) :
    (MulAut.conj y : MulAut (UqT h n)) ∈
      primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have hs : (s : GL (Fin n) K) ∈ UqU h n := ((mem_gramSU_iff_unitary h).1 s.2).1
  refine ⟨⟨s, hs⟩, ?_⟩
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk]
  simp only [MulAut.conj_apply]
  rfl

theorem uq_scalar_mem_iff (hn : 0 < n) (c : Kˣ) :
    (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈ UqU h n ↔
      h.bar (c : K) * c = 1 := by
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, GeneralLinearGroup.coe_scalar]
  have e : ((Matrix.scalar (Fin n) (c : K)).map h.bar)ᵀ * Matrix.scalar (Fin n) (c : K) =
      Matrix.diagonal (fun _ : Fin n => h.bar (c : K) * c) := by
    simp only [Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
  rw [e]
  constructor
  · intro h1
    have := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this
  · intro h1
    rw [h1, Matrix.diagonal_one]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
