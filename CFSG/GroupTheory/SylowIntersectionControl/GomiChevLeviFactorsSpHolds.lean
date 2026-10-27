module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorInputs
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpLevi
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLLeviConnected
import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.ModelSp

public section

namespace CFSG.GroupTheory

open CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Universal.Symplectic
  CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding

section Combinatorics

variable {n : ℕ} {F : Type} [Field F]

private theorem diagramGraph_cartanC (n : ℕ) :
    (TauCeti.diagramGraph (CFSG.LieType.Universal.Symplectic.cartanC n) :
      SimpleGraph (Fin n)) = SimpleGraph.pathGraph n := by
  ext i j
  rw [TauCeti.diagramGraph_adj, SimpleGraph.pathGraph_adj]
  simp only [CFSG.LieType.Universal.Symplectic.cartanC, Matrix.of_apply]
  constructor
  · rintro ⟨hne, hij, -⟩
    by_contra hcon
    push Not at hcon
    exact hij (by simp [hne, hcon])
  · rintro (h | h)
    · have hne : i ≠ j := by intro he; rw [he] at h; omega
      refine ⟨hne, ?_, ?_⟩
      · simp only [if_neg hne, if_pos (Or.inl h)]
        split_ifs <;> norm_num
      · simp only [if_neg (Ne.symm hne), if_pos (Or.inr h)]
        split_ifs <;> norm_num
    · have hne : i ≠ j := by intro he; rw [he] at h; omega
      refine ⟨hne, ?_, ?_⟩
      · simp only [if_neg hne, if_pos (Or.inr h)]
        split_ifs <;> norm_num
      · simp only [if_neg (Ne.symm hne), if_pos (Or.inl h)]
        split_ifs <;> norm_num

private theorem nodeAdj_val_sp {C : Set (Fin n)} {i j : Fin n}
    (h : NodeAdj (CFSG.LieType.Universal.Symplectic.rootDatum n F) C i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have h1 := h.2.2
  change (TauCeti.diagramGraph (CFSG.LieType.Universal.Symplectic.cartanC n)).Adj i j at h1
  rw [diagramGraph_cartanC, SimpleGraph.pathGraph_adj] at h1
  exact h1

end Combinatorics

section Blocks

variable {n : ℕ} {F : Type} [Field F] {C : Set (Fin n)} {a b : Fin n}

private theorem nodesOf_blkSet_Icc (hCab : C = Set.Icc a b) (ha : a ∈ C) :
    nodesOf (blkSet C a.castSucc) = C := by
  rw [blkSet_eq_Icc (i := a) hCab ha, hCab]
  ext k
  simp only [nodesOf, Set.mem_setOf_eq, Finset.mem_Icc, Set.mem_Icc, Fin.le_def,
    Fin.val_castSucc, Fin.val_succ]
  omega

private theorem card_coordsOf_eq (B : Finset (Fin (n + 1))) :
    (coordsOf B).card = (B.erase (Fin.last n)).card := by
  have himage : (coordsOf B).image (fun i : Fin n => i.castSucc) = B.erase (Fin.last n) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_erase, mem_coordsOf]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Fin.castSucc_lt_last i).ne, hi⟩
    · rintro ⟨hpne, hpB⟩
      have hp : p.val < n := by
        have := p.isLt
        have hne : p.val ≠ n := fun h => hpne (Fin.ext (by simpa [Fin.val_last] using h))
        omega
      exact ⟨⟨p.val, hp⟩, by simpa using hpB, by ext; rfl⟩
  rw [← himage, Finset.card_image_of_injective (coordsOf B)
    (fun i j h => Fin.ext (by simpa using congrArg Fin.val h))]

private theorem card_coordsOf_of_not_mem (B : Finset (Fin (n + 1)))
    (h : Fin.last n ∉ B) : (coordsOf B).card = B.card := by
  rw [card_coordsOf_eq, Finset.erase_eq_of_notMem h]

private theorem card_coordsOf_of_mem (B : Finset (Fin (n + 1)))
    (h : Fin.last n ∈ B) : (coordsOf B).card = B.card - 1 := by
  rw [card_coordsOf_eq, Finset.card_erase_of_mem h]

end Blocks

section Factors

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem gomiLeviFactor_of_GA_ns (B : Finset (Fin (n + 1)))
    (hns : CFSG.IsQuasisimple ↥(GA F B) ∧
      IsClassicalTwoOrG2 (↥(GA F B) ⧸ Subgroup.center ↥(GA F B))) :
    GomiLeviFactor ↥(GA F B) := by
  refine Or.inl (IsGomiChevTwo.of_isQuasisimple hns.1 ?_
    (isChevTwo_of_classicalTwoOrG2 hns.2))
  rw [Nat.card_congr (Subgroup.centerCongr (GA_equiv (F := F) B)).toEquiv]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.not_dvd_card_center_specialLinearGroup)

end Factors

theorem gomiLeviFactorsSp_holds : GomiLeviFactorsSp := by
  intro n F _ _ _ C hC h2C hproper
  obtain ⟨a, b, ha, _, hCab⟩ := hC.exists_eq_Icc (fun _ _ h => nodeAdj_val_sp h)
  let B : Finset (Fin (n + 1)) := blkSet C a.castSucc
  have hB : B = blkSet C a.castSucc := rfl
  have hnodes : (nodesOf B :
      Set (Fin (CFSG.LieType.Universal.Symplectic.rootDatum n F).rank)) = C := by
    change nodesOf B = C
    exact nodesOf_blkSet_Icc hCab ha
  have hBbcard : B.card = C.ncard + 1 := card_blkSet_eq_Icc hCab ha
  have hGb : Gb F B = leviM (CFSG.LieType.Universal.Symplectic.rootDatum n F) C := by
    calc
      Gb F B = leviM (CFSG.LieType.Universal.Symplectic.rootDatum n F) (nodesOf B) :=
        Gb_eq (F := F) (I := C) hB
      _ = leviM (CFSG.LieType.Universal.Symplectic.rootDatum n F) C := by rw [hnodes]
  rw [← hGb]
  by_cases hl : Fin.last n ∈ B
  · have hGE : Gb F B = GE F B := by simp [Gb, hl]
    rw [hGE]
    have hk : (coordsOf B).card = C.ncard := by
      rw [card_coordsOf_of_mem B hl, hBbcard]
      omega
    exact GomiLeviFactor.of_mulEquiv (GE_equiv B).symm
      (GomiLeviExc.gomiLeviFactor_statedSp F (by omega))
  · have hGA : Gb F B = GA F B := by simp [Gb, hl]
    rw [hGA]
    have hk : (coordsOf B).card = C.ncard + 1 := by
      rw [card_coordsOf_of_not_mem B hl, hBbcard]
    have hk' : 3 ≤ (coordsOf B).card ∨
        ((coordsOf B).card = 2 ∧ 4 ≤ Nat.card F) := Or.inl (by omega)
    have hns := GA_ns (MonoidHom.id _) Function.injective_id B hk'
    rw [Subgroup.map_id] at hns
    exact gomiLeviFactor_of_GA_ns B hns

end CFSG.GroupTheory
