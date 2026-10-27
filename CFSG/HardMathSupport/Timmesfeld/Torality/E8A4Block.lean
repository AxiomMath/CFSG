module

public import CFSG.HardMathSupport.Timmesfeld.Torality.A4Block
public import CFSG.HardMathSupport.Timmesfeld.Torality.E8Chain
public import CFSG.RankThree.PartOne.KE.E8A4Sigma

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (chainRoot)

@[expose] def chainSum (β : Fin 4 → Fin Tag.E8.rank → ℤ) (i j : Fin 5) : Fin Tag.E8.rank → ℤ :=
  ∑ k : Fin 4, ((if (i : ℕ) ≤ k ∧ (k : ℕ) < j then 1 else 0) -
    (if (j : ℕ) ≤ k ∧ (k : ℕ) < i then 1 else 0) : ℤ) • β k

@[expose] def chainSet5 (β : Fin 4 → Fin Tag.E8.rank → ℤ) : Set (Fin Tag.E8.rank → ℤ) :=
  {r | ∃ i j : Fin 5, i ≠ j ∧ r = chainSum β i j}

theorem chainSum_succ (β : Fin 4 → Fin Tag.E8.rank → ℤ) (k : Fin 4) :
    chainSum β k.castSucc k.succ = β k := by
  fin_cases k <;> simp [chainSum, Fin.sum_univ_four]

theorem chainRoot_e8a4chain_eq (i j : Fin 5) :
    chainRoot e8a4chain i j = ∑ k : Fin 4, ((if (i : ℕ) ≤ k ∧ (k : ℕ) < j then 1 else 0) -
      (if (j : ℕ) ≤ k ∧ (k : ℕ) < i then 1 else 0) : ℤ) • e8s k := by
  funext l
  simp only [chainRoot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : e8s k = Pi.single (e8a4chain k) 1 := by
    fin_cases k <;> rfl
  rw [h1, Pi.single_apply]
  simp [eq_comm]

section

theorem sigmaRootE8A4_eq_chainSum {v : WeylGroup Tag.E8} {β : Fin 4 → Fin Tag.E8.rank → ℤ}
    (hv : ∀ k, v • e8s k = β k) (i j : Fin 5) : sigmaRootE8A4 v i j = chainSum β i j := by
  rw [sigmaRootE8A4_eq_smul, chainRoot_e8a4chain_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm, hv k]

end

section

variable {L : Type} [Field L]

theorem e8A4_frame (v : WeylGroup Tag.E8) :
    IsA4Frame (rhoSigmaE8A4 L v) (sigmaRootE8A4 v) where
  injective := rhoSigmaE8A4_injective v
  isRoot i j hij := isRoot_sigmaRootE8A4 v hij
  neg i j := (sigmaRootE8A4_neg v i j).symm
  add i j k := sigmaRootE8A4_add v i j k
  transv i j hij := rhoSigmaE8A4_transvection v i j hij
  range := by
    rw [rhoSigmaE8A4_range, sigmaSetE8A4_eq]
    rfl
  torus b := ⟨fun i => rootChar b (wbE8A4 v i), fun A => rhoSigmaE8A4_torus v b A⟩
  diag A hA := rhoSigmaE8A4_diagonal v A hA

theorem a4Block_E8 [IsAlgClosed L] (hL : ringChar L ≠ 5) {β : Fin 4 → Fin Tag.E8.rank → ℤ}
    (hβ : IsE8Chain β) :
    ∃ m ∈ rootSpan Tag.E8 L (chainSet5 β), ∃ hm : m ∈ monomialSubgroup Tag.E8 L,
      weylQuotientHom Tag.E8 L ⟨m, hm⟩ = rootReflection (β 0) * rootReflection (β 1) *
        rootReflection (β 2) * rootReflection (β 3) ∧
      ∀ t ∈ torusGroup Tag.E8 L, ∃ y ∈ rootSpan Tag.E8 L (chainSet5 β),
        y * (m * t) * y⁻¹ ∈ torusGroup Tag.E8 L := by
  obtain ⟨v, hv⟩ := exists_weyl_chain_E8 hβ
  have key := a4BlockAt_of_frame hL (e8A4_frame (L := L) v)
  have hσ : ∀ i j, sigmaRootE8A4 v i j = chainSum β i j := sigmaRootE8A4_eq_chainSum hv
  have hset : frameRoots5 (sigmaRootE8A4 v) = chainSet5 β := by
    ext r
    simp only [frameRoots5, chainSet5, hσ]
  have h01 : sigmaRootE8A4 v 0 1 = β 0 := by rw [hσ]; exact chainSum_succ β 0
  have h12 : sigmaRootE8A4 v 1 2 = β 1 := by rw [hσ]; exact chainSum_succ β 1
  have h23 : sigmaRootE8A4 v 2 3 = β 2 := by rw [hσ]; exact chainSum_succ β 2
  have h34 : sigmaRootE8A4 v 3 4 = β 3 := by rw [hσ]; exact chainSum_succ β 3
  rw [hset, h01, h12, h23, h34] at key
  exact key

end

end CFSG.HardMathSupport.Timmesfeld.Torality
