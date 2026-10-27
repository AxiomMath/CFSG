module

public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Open

theorem heldFlagSp {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (U : Subgroup (StatedSp n K)) (hU : U ≠ ⊥) (hUp : IsPGroup 2 U) :
    ∃ W : Submodule K (Fin n ⊕ Fin n → K), W ≠ ⊥ ∧
      (∀ v ∈ W, ∀ w ∈ W, v ⬝ᵥ (fromBlocks 0 1 (-1) 0 *ᵥ w) = 0) ∧
      ∀ y ∈ Subgroup.normalizer (U : Set (StatedSp n K)), ∀ w ∈ W,
        ((y : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρ := isIsometric_natRep_statedSp n K
  have hinj : Function.Injective (natRep (StatedSp n K)) := natRep_injective _
  refine ⟨isoSeq (spForm n K) (natRep (StatedSp n K)) U 1,
    isoSeq_one_ne_bot _ _ 2 hρ hinj U hUp hU, ?_, ?_⟩
  · intro v hv w hw
    have hWiso := isoSeq_isTotallyIsotropic (spForm n K) (natRep (StatedSp n K)) U 1
    have hperp : w ∈ (spForm n K).perp
        (isoSeq (spForm n K) (natRep (StatedSp n K)) U 1) := hWiso hw
    have hβ := (ReflForm.mem_perp _).mp hperp v hv
    exact hβ
  · intro y hy w hw
    have hmem := apply_mem_isoSeq (spForm n K) (natRep (StatedSp n K)) hρ U 1 hy hw
    rwa [natRep_apply] at hmem

end CFSG.LieType.BorelTits
