module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Open CFSG.AGLEmbedding

theorem heldFlagSU {K : Type} [Field K] [Finite K] [CharP K 2] {n q : ℕ}
    (hK : Nat.card K = q ^ 2) (U : Subgroup (StatedSU n q K)) (hU : U ≠ ⊥) (hUp : IsPGroup 2 U) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ IsTotallyIsotropicSU q W ∧
      ∀ y ∈ Subgroup.normalizer (U : Set (StatedSU n q K)), ∀ w ∈ W,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  obtain ⟨f, -, rfl⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ f) ^ 2 := hK
  have hρ : IsIsometric (unitaryForm 2 f hK' n) (natRep (StatedSU n (2 ^ f) K)) :=
    isIsometric_natRep_statedSU hK' n
  have hinj : Function.Injective (natRep (StatedSU n (2 ^ f) K)) := natRep_injective _
  refine ⟨isoSeq (unitaryForm 2 f hK' n) (natRep (StatedSU n (2 ^ f) K)) U 1,
    isoSeq_one_ne_bot _ _ 2 hρ hinj U hUp hU, ?_, ?_⟩
  · intro v hv w hw
    have hWiso := isoSeq_isTotallyIsotropic (unitaryForm 2 f hK' n)
      (natRep (StatedSU n (2 ^ f) K)) U 1
    have hperp : w ∈ (unitaryForm 2 f hK' n).perp
        (isoSeq (unitaryForm 2 f hK' n) (natRep (StatedSU n (2 ^ f) K)) U 1) := hWiso hw
    have hβ := (ReflForm.mem_perp _).mp hperp v hv
    rw [unitaryForm_β hK'] at hβ
    simp only [unitaryInvolution_apply] at hβ
    exact hβ
  · intro y hy w hw
    have hmem := apply_mem_isoSeq (unitaryForm 2 f hK' n) (natRep (StatedSU n (2 ^ f) K)) hρ U 1
      hy hw
    rwa [natRep_apply] at hmem

end CFSG.LieType.BorelTits
