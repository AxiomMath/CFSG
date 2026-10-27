module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLeviComponents
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLLevi

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.CurtisTits CFSG.AGLEmbeddingD2.SquareLinear
open Matrix

private noncomputable def slReindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {R : Type} [CommRing R] (e : ι ≃ κ) :
    Matrix.SpecialLinearGroup ι R ≃* Matrix.SpecialLinearGroup κ R where
  toFun A := ⟨Matrix.reindex e e (A : Matrix ι ι R), by
    rw [Matrix.det_reindex_self]; exact A.2⟩
  invFun A := ⟨Matrix.reindex e.symm e.symm (A : Matrix κ κ R), by
    rw [Matrix.det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv A := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change Matrix.reindex e e ((A : Matrix ι ι R) * (B : Matrix ι ι R)) =
      Matrix.reindex e e (A : Matrix ι ι R) * Matrix.reindex e e (B : Matrix ι ι R)
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv])

section Combinatorics

variable {m : ℕ} {F : Type} [Field F]

private theorem nodeAdj_val {C : Set (Fin m)} {i j : Fin m}
    (h : NodeAdj (rootDatum m F) C i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have h1 := h.2.2
  change (TauCeti.diagramGraph (CartanMatrix.A m)).Adj i j at h1
  rw [TauCeti.DynkinType.diagramGraph_cartanMatrix_A, SimpleGraph.pathGraph_adj] at h1
  exact h1

theorem blkSet_eq_Icc {C : Set (Fin m)} {a b : Fin m} (hCab : C = Set.Icc a b)
    {i : Fin m} (hi : i ∈ C) :
    blkSet C i.castSucc = Finset.Icc a.castSucc b.succ := by
  ext p
  rw [mem_blkSet, Finset.mem_Icc, Fin.le_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ]
  have hii : a.val ≤ i.val ∧ i.val ≤ b.val := by
    have h := hi; rw [hCab] at h
    exact ⟨Fin.le_def.mp h.1, Fin.le_def.mp h.2⟩
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have hp : p.val < m := by have := p.isLt; have := a.isLt; omega
      have hjC : (⟨p.val, hp⟩ : Fin m) ∉ C := by
        intro hjc
        rw [hCab] at hjc
        have : a.val ≤ p.val := Fin.le_def.mp hjc.1
        omega
      have hiff := h ⟨p.val, hp⟩ hjC
      have h2 : (⟨p.val, hp⟩ : Fin m).val ≤ p.val := le_refl p.val
      have h3 : ¬ i.castSucc.val ≤ p.val := by simp only [Fin.val_castSucc]; omega
      exact h3 (hiff.mpr h2)
    · by_contra hlt
      push Not at hlt
      have hp : b.val + 1 < m := by have := p.isLt; omega
      have hjC : (⟨b.val + 1, hp⟩ : Fin m) ∉ C := by
        intro hjc
        rw [hCab] at hjc
        have : b.val + 1 ≤ b.val := Fin.le_def.mp hjc.2
        omega
      have hiff := h ⟨b.val + 1, hp⟩ hjC
      have h2 : i.castSucc.val ≤ b.val + 1 := by simp only [Fin.val_castSucc]; omega
      have h3 : ¬ p.val ≤ b.val + 1 := by omega
      exact h3 (hiff.mp h2)
  · intro ⟨hap, hpb⟩ j hjC
    have hjv : j.val < a.val ∨ b.val < j.val := by
      have h := hjC; rw [hCab] at h
      simp only [Set.mem_Icc, not_and_or, not_le] at h
      exact h
    simp only [Fin.val_castSucc]
    constructor
    · intro hle
      rcases hjv with h | h <;> omega
    · intro hle
      rcases hjv with h | h <;> omega

theorem card_blkSet_eq_Icc {C : Set (Fin m)} {a b : Fin m}
    (hCab : C = Set.Icc a b) (ha : a ∈ C) : (blkSet C a.castSucc).card = C.ncard + 1 := by
  have hab : a.val ≤ b.val := by
    have h := ha; rw [hCab] at h
    exact Fin.le_def.mp h.2
  rw [blkSet_eq_Icc hCab ha, hCab, Set.ncard_Icc]
  simp only [Fin.card_Icc, Fin.val_castSucc, Fin.val_succ]
  omega

end Combinatorics

theorem nonempty_mulEquiv_leviM_of_isNodeConnected {m : ℕ} {F : Type} [Field F]
    {C : Set (Fin m)} (hC : IsNodeConnected (rootDatum m F) C) :
    Nonempty (↥(leviM (rootDatum m F) C) ≃* Matrix.SpecialLinearGroup (Fin (C.ncard + 1)) F) := by
  classical
  obtain ⟨a, b, ha, _, hCab⟩ := hC.exists_eq_Icc (fun _ _ h => nodeAdj_val h)
  have hB : blkSet C a.castSucc = Finset.Icc a.castSucc b.succ := blkSet_eq_Icc hCab ha
  have hcard := card_blkSet_eq_Icc hCab ha
  have hlevi : leviM (rootDatum m F) C =
      (coordHom (F := F) (blkSet C a.castSucc)).range := by
    apply le_antisymm
    · refine iSup₂_le fun i hi => ?_
      let i' : Fin m := i
      have hi' : i' ∈ C := hi
      have h1 : rankOne (rootDatum m F).rootGroup i' ≤
          (coordHom (F := F) (blkSet C i'.castSucc)).range := by
        have hs : SameBlk C i'.castSucc i'.succ := by
          intro j hj
          have hji : j.val ≠ i'.val := fun h => hj (Fin.ext h ▸ hi')
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega
        exact rankOne_le_range_coordHom i' (mem_blkSet.mpr (SameBlk.refl C _))
          (mem_blkSet.mpr hs)
      rw [blkSet_eq_Icc hCab hi'] at h1
      rw [hB]
      exact h1
    · exact range_coordHom_le_leviM a.castSucc
  refine ⟨(MulEquiv.subgroupCongr hlevi).trans ?_⟩
  exact ((MonoidHom.ofInjective (coordHom_injective (F := F) (blkSet C a.castSucc))).symm.trans
    (slReindex (Finset.equivFin (blkSet C a.castSucc)))).trans (slReindex (finCongr hcard))

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
