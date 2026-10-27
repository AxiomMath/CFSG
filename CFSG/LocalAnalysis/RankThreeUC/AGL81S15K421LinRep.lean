module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinCG

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421RepProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CenProof K421K4Proof K421CGProof

@[expose] def gStd (ι β : Type) [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] :
    Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2) :=
  fromBlocks 1 0 0 (Ωstd β)

theorem gmat_eq (ι β : Type) [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] :
    (gmat psi4 omega4 : Matrix (ι ⊕ (β × Fin 2)) (ι ⊕ (β × Fin 2)) (ZMod 2)) = gStd ι β := by
  rw [gmat, gStd, psiB_scalar_omega]

@[expose] def kapFun0 (e : ℕ) : Fin e ⊕ Idx → (Fin e ⊕ (Fin 2 × Fin 2)) ⊕ (Fin 1 × Fin 2)
  | .inl i => .inl (.inl i)
  | .inr (b, j) =>
    if hb : b.val = 0 then .inr (0, j) else .inl (.inr (⟨b.val - 1, by omega⟩, j))

@[expose] def kapFun1 (e : ℕ) : Fin e ⊕ Idx → (Fin e ⊕ (Fin 1 × Fin 2)) ⊕ (Fin 2 × Fin 2)
  | .inl i => .inl (.inl i)
  | .inr (b, j) =>
    if hb : b.val < 2 then .inr (⟨b.val, hb⟩, j) else .inl (.inr (0, j))

theorem kapFun0_bijective : ∀ e : ℕ, e ≤ 1 → Function.Bijective (kapFun0 e) := by
  intro e he
  interval_cases e <;> decide +kernel

theorem kapFun1_bijective : ∀ e : ℕ, e ≤ 1 → Function.Bijective (kapFun1 e) := by
  intro e he
  interval_cases e <;> decide +kernel

theorem hg_t0 : ∀ e : ℕ, e ≤ 1 →
    (fromBlocks (1 : Matrix (Fin e) (Fin e) (ZMod 2)) 0 0 (aMat (rep 0)) :
      Matrix (Fin e ⊕ Idx) (Fin e ⊕ Idx) (ZMod 2)) =
    (gStd (Fin e ⊕ (Fin 2 × Fin 2)) (Fin 1)).submatrix (kapFun0 e) (kapFun0 e) := by
  intro e he
  interval_cases e <;> (unfold gStd Ωstd aMat cpow rep Cm; decide +kernel)

theorem hg_t1 : ∀ e : ℕ, e ≤ 1 →
    (fromBlocks (1 : Matrix (Fin e) (Fin e) (ZMod 2)) 0 0 (aMat (rep 1)) :
      Matrix (Fin e ⊕ Idx) (Fin e ⊕ Idx) (ZMod 2)) =
    (gStd (Fin e ⊕ (Fin 1 × Fin 2)) (Fin 2)).submatrix (kapFun1 e) (kapFun1 e) := by
  intro e he
  interval_cases e <;> (unfold gStd Ωstd aMat cpow rep Cm; decide +kernel)

theorem hg_t2 : ∀ e : ℕ, e ≤ 1 →
    (fromBlocks (1 : Matrix (Fin e) (Fin e) (ZMod 2)) 0 0 (aMat (rep 2)) :
      Matrix (Fin e ⊕ Idx) (Fin e ⊕ Idx) (ZMod 2)) = gStd (Fin e) (Fin 3) := by
  intro e he
  interval_cases e <;> (unfold gStd Ωstd aMat cpow rep Cm; decide +kernel)

end K421RepProof

end CFSG.LocalAnalysis.RankThreeUC.S15
