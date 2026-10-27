module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.SubfieldGL
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF

open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF)
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three (liftGL)

variable {ℓ f : ℕ} {F : Type} [Field F]

theorem exists_fixData (h : UnitaryFieldData ℓ f F) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    ∃ h₀ : UnitaryFieldData ℓ (f / 3) (fixF σ), ∀ c : fixF σ, (h₀.bar c : F) = h.bar c := by
  have key : ∀ k : Subfield F, k = CFSG.LieType.Chevalley.fixSubfield σ →
      ∃ h₀ : UnitaryFieldData ℓ (f / 3) k, ∀ c : k, (h₀.bar c : F) = h.bar c := by
    intro k hk
    subst hk
    exact ⟨CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσ,
      CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσ⟩
  have := h.finite
  refine key (fixF σ) ?_
  ext x
  rw [mem_fixF]
  exact Iff.symm (RingHom.mem_eqLocusField (f := (σ : F →+* F)) (g := RingHom.id F) (x := x))

theorem three_dvd_of_orderOf (h : UnitaryFieldData ℓ f F) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    3 ∣ f :=
  (CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary h Nat.prime_three (by norm_num) hσ).1

theorem pow_eq_cube (h : UnitaryFieldData ℓ f F) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    ℓ ^ f = (ℓ ^ (f / 3)) ^ 3 := by
  obtain ⟨e, he⟩ := three_dvd_of_orderOf h hσ
  rw [he, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3), ← pow_mul, mul_comm]

theorem three_dvd_sub_data (h : UnitaryFieldData ℓ f F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (h3 : 3 ∣ ℓ ^ f + 1) : 3 ∣ ℓ ^ (f / 3) + 1 := by
  rw [pow_eq_cube h hσ] at h3
  generalize ℓ ^ (f / 3) = a at h3 ⊢
  have : a ^ 3 % 3 = a % 3 := by
    have := Nat.mod_lt a (by norm_num : 3 > 0)
    interval_cases hm : a % 3 <;> simp [Nat.pow_mod, hm]
  omega

variable (h : UnitaryFieldData ℓ f F) {σ : F ≃+* F} (h₀ : UnitaryFieldData ℓ (f / 3) (fixF σ))
  (hbar : ∀ c : fixF σ, (h₀.bar c : F) = h.bar c)

include hbar in
theorem liftGL_mem_unitaryIsom3_iff (M : GL (Fin 3) (fixF σ)) :
    liftGL σ M ∈ unitaryIsom3 h ↔ M ∈ unitaryIsom3 h₀ := by
  rw [mem_unitaryIsom3, mem_unitaryIsom3]
  have e : ((liftGL σ M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (M : Matrix (Fin 3) (Fin 3) (fixF σ)).map (fixF σ).subtype := rfl
  have key : ((((liftGL σ M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((liftGL σ M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      ((((M : Matrix (Fin 3) (Fin 3) (fixF σ)).map h₀.bar)ᵀ *
        (M : Matrix (Fin 3) (Fin 3) (fixF σ))).map (fixF σ).subtype) := by
    rw [e, Matrix.map_mul, Matrix.transpose_map]
    congr 2
    ext i j
    exact (hbar _).symm
  rw [key]
  constructor
  · intro h1
    apply Matrix.map_injective (f := (fixF σ).subtype) Subtype.val_injective
    beta_reduce
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro h1
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF
