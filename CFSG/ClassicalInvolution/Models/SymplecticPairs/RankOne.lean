module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.LieType.Universal.SymplecticExtras.RankOne
import all CFSG.LieType.Universal.SymplecticExtras.RankOne

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (blockMat blockHom coe_blockHom blockHom_injective mem_closure_sl2
  isBlk_blockMat toBlock_blockMat)
open CFSG.LieType.Universal.Symplectic (equivStatedSp rootGroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt elt_mem_rootGroup toBlock
  eq_of_toBlock_eq stdVec_shortPos_eq stdVec_shortNeg_eq stdVec_positiveLong_eq
  stdVec_negativeLong_eq ne_succ' rankOne_short_mem rankOne_long_mem toBlock_mat_leviHom)
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem range_longBlock_eq_rankOne {k : Fin n} (hk : ¬k.val + 1 < n) :
    (longBlock K n k).range = rankOne (rootGroup n K) k := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
        (rankOne (rootGroup n K) k).comap (longBlock K n k) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change longBlock K n k (sl2Upper c) ∈ rankOne (rootGroup n K) k
        rw [longBlock_sl2Upper]
        exact le_sup_left (a := rootGroup n K (Pi.single k 1))
          (b := rootGroup n K (-Pi.single k 1))
          (elt_mem_rootGroup (stdVec_positiveLong_eq hk) c)
      · change longBlock K n k (sl2Lower c) ∈ rankOne (rootGroup n K) k
        rw [longBlock_sl2Lower]
        exact le_sup_right (a := rootGroup n K (Pi.single k 1))
          (b := rootGroup n K (-Pi.single k 1))
          (elt_mem_rootGroup (stdVec_negativeLong_eq hk) c)
    exact hle (mem_closure_sl2 A)
  · intro g hg
    obtain ⟨hblk, hdet⟩ := rankOne_long_mem hk hg
    refine ⟨mkSL (toBlock (Sum.inl k) (Sum.inr k) (mat n K g)) hdet, mat_injective ?_⟩
    rw [mat_longBlock, coe_mkSL]
    exact eq_of_toBlock_eq (isBlk_blockMat _) hblk (toBlock_blockMat hpq _)

theorem range_shortBlock_eq_rankOne {k : Fin n} (hk : k.val + 1 < n) :
    (shortBlock K (ne_succ' hk)).range = rankOne (rootGroup n K) k := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
        (rankOne (rootGroup n K) k).comap (shortBlock K (ne_succ' hk)) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change shortBlock K (ne_succ' hk) (sl2Upper c) ∈ rankOne (rootGroup n K) k
        rw [shortBlock_sl2Upper]
        exact le_sup_left (a := rootGroup n K (Pi.single k 1))
          (b := rootGroup n K (-Pi.single k 1))
          (elt_mem_rootGroup (stdVec_shortPos_eq hk) c)
      · change shortBlock K (ne_succ' hk) (sl2Lower c) ∈ rankOne (rootGroup n K) k
        rw [shortBlock_sl2Lower]
        exact le_sup_right (a := rootGroup n K (Pi.single k 1))
          (b := rootGroup n K (-Pi.single k 1))
          (elt_mem_rootGroup (stdVec_shortNeg_eq hk) c)
    exact hle (mem_closure_sl2 A)
  · intro g hg
    obtain ⟨⟨A, hA, hgA⟩, hdet⟩ := rankOne_short_mem hk hg
    rw [hgA, toBlock_mat_leviHom] at hdet
    have hAeq : blockHom K (ne_succ' hk)
        (mkSL (toBlock k ⟨k.val + 1, hk⟩ (A : Matrix (Fin n) (Fin n) K)) hdet) = A := by
      apply Units.ext
      rw [coe_blockHom, coe_mkSL]
      exact (eq_of_toBlock_eq hA (isBlk_blockMat _) (toBlock_blockMat (ne_succ' hk) _).symm).symm
    refine ⟨mkSL (toBlock k ⟨k.val + 1, hk⟩ (A : Matrix (Fin n) (Fin n) K)) hdet, mat_injective ?_⟩
    rw [hgA]
    change mat n K (equivStatedSp n K (TauCeti.GLSymplecticFin.leviHom (blockHom K (ne_succ' hk)
      (mkSL (toBlock k ⟨k.val + 1, hk⟩ (A : Matrix (Fin n) (Fin n) K)) hdet)))) = _
    rw [hAeq]

end CFSG.ClassicalInvolution.Models.SymplecticPairs
