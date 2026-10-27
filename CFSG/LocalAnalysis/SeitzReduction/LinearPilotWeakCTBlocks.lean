module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockIdx det_blockMat)
open scoped MatrixGroups

@[expose] def consecutiveBlock (m i k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun a => i ≤ a.val ∧ a.val < i + k

theorem mem_consecutiveBlock {m i k : ℕ} {a : Fin m} :
    a ∈ consecutiveBlock m i k ↔ i ≤ a.val ∧ a.val < i + k := by
  simp [consecutiveBlock]

theorem card_consecutiveBlock_le (m i k : ℕ) : (consecutiveBlock m i k).card ≤ k := by
  calc (consecutiveBlock m i k).card
      = ((consecutiveBlock m i k).map Fin.valEmbedding).card := (Finset.card_map _).symm
    _ ≤ (Finset.Ico i (i + k)).card := Finset.card_le_card fun x hx => by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
        rw [mem_consecutiveBlock] at ha
        rw [Finset.mem_Ico, Fin.valEmbedding_apply]
        exact ha
    _ = k := by simp

theorem consecutiveBlock_two {m : ℕ} (i : Fin m) :
    consecutiveBlock (m + 1) i 2 = ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
  ext a
  rw [mem_consecutiveBlock, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  omega

theorem consecutiveBlock_three {m : ℕ} (i j : Fin m) (hj : (j : ℕ) = i + 1) :
    consecutiveBlock (m + 1) i 3 =
      ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} := by
  ext a
  simp only [mem_consecutiveBlock, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

theorem disjoint_nodePair_of_lt {m : ℕ} (i j : Fin m) (hij : (i : ℕ) + 1 < j) :
    Disjoint ({i.castSucc, i.succ} : Finset (Fin (m + 1))) {j.castSucc, j.succ} := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at ha hb
  omega

theorem card_nodePair {m : ℕ} (i : Fin m) :
    ({i.castSucc, i.succ} : Finset (Fin (m + 1))).card = 2 :=
  Finset.card_pair (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne

theorem card_union_nodePair_le {m : ℕ} (i j : Fin m) :
    (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}).card ≤ 4 := by
  have := Finset.card_union_le ({i.castSucc, i.succ} : Finset (Fin (m + 1)))
    {j.castSucc, j.succ}
  rw [card_nodePair, card_nodePair] at this
  exact this

theorem card_union_nodePair_adjacent_le {m : ℕ} (i j : Fin m) (hj : (j : ℕ) = i + 1) :
    (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}).card ≤ 3 := by
  rw [← consecutiveBlock_three i j hj]
  exact card_consecutiveBlock_le _ _ _

section Blocks

variable {F : Type} [Field F]

theorem range_blockSL_eq {m k i : ℕ} (h : i + k ≤ m) :
    (CFSG.ClassicalInvolution.WeakCT.blockSL F m k i h).range =
      blockSpecialLinear (K := F) (consecutiveBlock m i k) := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    rw [mem_blockSpecialLinear]
    intro a b hab
    rw [CFSG.ClassicalInvolution.WeakCT.coe_blockSL, blockMat_apply, dite_eq_right]
    rintro ⟨ha, hb⟩
    rcases hab with ha' | hb'
    · exact ha' (mem_consecutiveBlock.2 ha)
    · exact hb' (mem_consecutiveBlock.2 hb)
  · intro A hA
    let B : Matrix (Fin k) (Fin k) F := fun x y =>
      (A : Matrix (Fin m) (Fin m) F) (blockIdx i h x) (blockIdx i h y)
    have hAB : blockMat m i B = (A : Matrix (Fin m) (Fin m) F) := by
      ext a b
      rw [blockMat_apply]
      split_ifs with hab
      · obtain ⟨⟨hai, hak⟩, ⟨hbi, hbk⟩⟩ := hab
        have ea : blockIdx i h ⟨a.val - i, by omega⟩ = a :=
          Fin.ext (by simp only [CFSG.ClassicalInvolution.Phan.blockIdx_val]; omega)
        have eb : blockIdx i h ⟨b.val - i, by omega⟩ = b :=
          Fin.ext (by simp only [CFSG.ClassicalInvolution.Phan.blockIdx_val]; omega)
        change (A : Matrix (Fin m) (Fin m) F) (blockIdx i h _) (blockIdx i h _) = _
        rw [ea, eb]
      · refine ((mem_blockSpecialLinear.1 hA) a b ?_).symm
        rw [not_and_or] at hab
        rcases hab with ha | hb
        · exact Or.inl fun h' => ha (mem_consecutiveBlock.1 h')
        · exact Or.inr fun h' => hb (mem_consecutiveBlock.1 h')
    have hdet : B.det = 1 := by
      rw [← det_blockMat h, hAB]
      exact A.2
    exact ⟨⟨B, hdet⟩, Subtype.ext hAB⟩

theorem range_blockSL2_eq (m : ℕ) (i : Fin m) :
    (CFSG.ClassicalInvolution.WeakCT.blockSL2 F m i).range =
      blockSpecialLinear (K := F) ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
  rw [← consecutiveBlock_two]
  exact range_blockSL_eq _

theorem range_blockSL3_le (m : ℕ) (i j : Fin m) (hj : (j : ℕ) = i + 1) (h : (i : ℕ) + 1 < m) :
    (CFSG.ClassicalInvolution.WeakCT.blockSL3 F m i h).range ≤
      blockSpecialLinear (K := F)
        (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}) := by
  rw [← consecutiveBlock_three i j hj]
  exact (range_blockSL_eq _).le

theorem iSup_blockSL_pair_eq_top (K : Type) [Field K] (m : ℕ) :
    ⨆ i : Fin m, blockSL (K := K) ({i.castSucc, i.succ} : Finset (Fin (m + 1))) = ⊤ := by
  have h := congrArg (Subgroup.map (LinearFlag.proj (m + 1) K))
    (CFSG.ClassicalInvolution.WeakCT.iSup_range_blockSL2 (K := K) m)
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 (LinearFlag.proj_surjective _ _)] at h
  rw [← h]
  refine iSup_congr fun i => ?_
  rw [range_blockSL2_eq, blockSL]

end Blocks

end CFSG.SeitzReduction.LinearPilot
