module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryRoots
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Universal.SpecialLinear (signedPerm signedPerm_apply)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups

section Sp

variable {K : Type} [Field K] {N : ℕ}

theorem zThreeSL_eq_mul [CharP K 2] : (zThreeSL : SL(2, K)) = sl2Upper 1 * sl2Lower 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_zThreeSL, zThreeMat, CFSG.LieType.Steinberg.Sp.coe_sl2Upper,
      CFSG.LieType.Steinberg.Sp.coe_sl2Lower, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem nsElt_eq_mul [CharP K 2] (k : Fin N) :
    nsElt (K := K) k = longBlock K N k (sl2Upper 1) * longBlock K N k (sl2Lower 1) := by
  rw [nsElt, zThreeSL_eq_mul, map_mul]

theorem nsElt_eq_conj_permSp_swap (k : Fin N) (hk : k.val + 1 < N) :
    nsElt (K := K) k = permSp K (Equiv.swap k ⟨k.val + 1, hk⟩) * nsElt ⟨k.val + 1, hk⟩ *
      (permSp K (Equiv.swap k ⟨k.val + 1, hk⟩))⁻¹ := by
  rw [nsElt, nsElt, conj_permSp_longBlock, Equiv.swap_apply_right]

theorem eq_nsElt_of_eq_last_of_eq_swap {G : Type*} [Group G] (φ ψ : StatedSp N K →* G)
    (hlast : ∀ k : Fin N, k.val + 1 = N → φ (nsElt k) = ψ (nsElt k))
    (hswap : ∀ (j : Fin N) (hj : j.val + 1 < N),
      φ (permSp K (Equiv.swap j ⟨j.val + 1, hj⟩)) = ψ (permSp K (Equiv.swap j ⟨j.val + 1, hj⟩)))
    (k : Fin N) : φ (nsElt k) = ψ (nsElt k) := by
  obtain ⟨d, hd⟩ : ∃ d, d = N - 1 - k.val := ⟨_, rfl⟩
  induction d generalizing k with
  | zero => exact hlast k (by have := k.2; omega)
  | succ d ih =>
    have hk1 : k.val + 1 < N := by omega
    rw [nsElt_eq_conj_permSp_swap k hk1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
      hswap k hk1, ih ⟨k.val + 1, hk1⟩ (by simp only; omega)]

end Sp

section Coords

variable {N ε : ℕ}

theorem swap_rev_ctuCoord (hε : ε ≤ 1) {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) (w : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    Equiv.swap (Fin.rev (lowIdx j)) (Fin.rev (lowIdx ⟨j.val + 1, hj⟩)) (ctuCoord N ε w) =
      ctuCoord N ε (Sum.map (Sum.map id
        (Equiv.swap (⟨j.val, by omega⟩ : Fin N) ⟨j.val + 1, by omega⟩)) id w) := by
  apply Fin.ext
  rw [val_swap_apply]
  rcases w with (p | p) | i
  · have hp := p.2
    split_ifs <;>
      simp only [Fin.val_rev, val_lowIdx, ctuCoord_inl_inl, Sum.map_inl, id] at * <;> omega
  · have hp := p.2
    split_ifs <;>
      simp only [Fin.val_rev, val_lowIdx, ctuCoord_inl_inr, Sum.map_inl, Sum.map_inr,
        val_swap_apply] at * <;> split_ifs <;> omega
  · have hi := i.2
    split_ifs <;>
      simp only [Fin.val_rev, val_lowIdx, ctuCoord_inr, Sum.map_inr, id] at * <;> omega

theorem swap_lowIdx_ctuCoord (hε : ε ≤ 1) {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) (w : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    Equiv.swap (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) (ctuCoord N ε w) =
      ctuCoord N ε (Sum.map (Sum.map
        (Equiv.swap (⟨j.val, by omega⟩ : Fin N) ⟨j.val + 1, by omega⟩) id) id w) := by
  apply Fin.ext
  rw [val_swap_apply]
  rcases w with (p | p) | i
  · have hp := p.2
    split_ifs <;>
      simp only [val_lowIdx, ctuCoord_inl_inl, Sum.map_inl, val_swap_apply] at * <;>
      split_ifs <;> omega
  · have hp := p.2
    split_ifs <;>
      simp only [val_lowIdx, ctuCoord_inl_inr, Sum.map_inl, Sum.map_inr, id] at * <;> omega
  · have hi := i.2
    split_ifs <;> simp only [val_lowIdx, ctuCoord_inr, Sum.map_inr, id] at * <;> omega

theorem swap_mul_swap_rev_ctuCoord (hε : ε ≤ 1) {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) (w : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    (Equiv.swap (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) *
        Equiv.swap (Fin.rev (lowIdx j)) (Fin.rev (lowIdx ⟨j.val + 1, hj⟩))) (ctuCoord N ε w) =
      ctuCoord N ε (Sum.map (Sum.map
        (Equiv.swap (⟨j.val, by omega⟩ : Fin N) ⟨j.val + 1, by omega⟩)
        (Equiv.swap (⟨j.val, by omega⟩ : Fin N) ⟨j.val + 1, by omega⟩)) id w) := by
  rw [Equiv.Perm.mul_apply, swap_rev_ctuCoord hε hj, swap_lowIdx_ctuCoord hε hj]
  rcases w with (p | p) | i <;> rfl

end Coords

section Model

variable {K F : Type} [Field K] [Field F] [CharP K 2] [CharP F 2] {N ε : ℕ} {hε : ε ≤ 1}
  {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

omit [CharP K 2] in
theorem ι_mem_traceZero (hι : ∀ c, σ (ι c) = ι c) (c : K) : ι c ∈ traceZero σ := by
  rw [mem_traceZero, hι, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem coe_ctuEmbed_longBlock_sl2Upper (k : Fin N) (c : K) :
    ((ctuEmbed ε hε σ ι hι (longBlock K N k (sl2Upper c)) : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
      longRootMatrix (ctuCoord N ε (Sum.inl (Sum.inl k))) (ι c) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuEmbed_apply_ctuCoord, longRootMatrix, ctuCoord_rev hε, ctuPar_inl, par_inl,
    Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, mat_longBlock]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rcases w with (p | p) | i <;> rcases w' with (q | q) | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      map_apply, Matrix.zero_apply, Matrix.one_apply, CFSG.LieType.Steinberg.Sp.blockMat,
      of_apply, CFSG.LieType.Steinberg.Sp.coe_sl2Upper, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, false_and, and_false, ite_false, add_zero, zero_add] <;>
    split_ifs <;> aesop

omit [CharP F 2] in
theorem coe_ctuEmbed_longBlock_sl2Lower (k : Fin N) (c : K) :
    ((ctuEmbed ε hε σ ι hι (longBlock K N k (sl2Lower c)) : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
      longRootMatrix (ctuCoord N ε (Sum.inl (Sum.inr k))) (ι c) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuEmbed_apply_ctuCoord, longRootMatrix, ctuCoord_rev hε, ctuPar_inl, par_inr,
    Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, mat_longBlock]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rcases w with (p | p) | i <;> rcases w' with (q | q) | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      map_apply, Matrix.zero_apply, Matrix.one_apply, CFSG.LieType.Steinberg.Sp.blockMat,
      of_apply, CFSG.LieType.Steinberg.Sp.coe_sl2Lower, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, false_and, and_false, ite_false, add_zero, zero_add] <;>
    split_ifs <;> aesop

theorem ctuEmbed_longBlock_sl2Upper_eq {j : Fin ((2 * N + ε) / 2)} (hj : j.val < N) (c : K) :
    ctuEmbed ε hε σ ι hι (longBlock K N ⟨j.val, hj⟩ (sl2Upper c)) =
      longRootHom σ (lowIdx_ne_rev j j) (Multiplicative.ofAdd ⟨ι c, ι_mem_traceZero hι c⟩) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuEmbed_longBlock_sl2Upper, coe_longRootHom, ← lowIdx_eq_ctuCoord hj]
  rfl

theorem ctuEmbed_longBlock_sl2Lower_eq {j : Fin ((2 * N + ε) / 2)} (hj : j.val < N) (c : K) :
    ctuEmbed ε hε σ ι hι (longBlock K N ⟨j.val, hj⟩ (sl2Lower c)) =
      longRootHom σ (rev_ne_rev_rev (lowIdx_ne_rev j j))
        (Multiplicative.ofAdd ⟨ι c, ι_mem_traceZero hι c⟩) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuEmbed_longBlock_sl2Lower, coe_longRootHom, ← rev_lowIdx_eq_ctuCoord hε hj]
  rfl

theorem ctuEmbed_nsElt_mem_rankOne (hσ : ∀ c, σ (σ c) = c) {j : Fin ((2 * N + ε) / 2)}
    (hj : ¬j.val + 1 < (2 * N + ε) / 2) :
    ctuEmbed ε hε σ ι hι (nsElt ⟨j.val, by have := j.2; omega⟩) ∈
      rankOne (rootGroup σ hσ (2 * N + ε)) j := by
  have hjN : j.val < N := by have := j.2; omega
  rw [nsElt_eq_mul, map_mul, ctuEmbed_longBlock_sl2Upper_eq hjN,
    ctuEmbed_longBlock_sl2Lower_eq hjN]
  exact mul_mem (longRootHom_mem_rankOne hσ hj _).1 (longRootHom_mem_rankOne hσ hj _).2

theorem ctuEmbed_permSp_swap_eq (hσ : ∀ c, σ (σ c) = c) {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) :
    ctuEmbed ε hε σ ι hι
        (permSp K (Equiv.swap (⟨j.val, by omega⟩ : Fin N) ⟨j.val + 1, by omega⟩)) =
      shortWeyl σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _) 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_shortWeyl σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) one_ne_zero]
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  have hd : ∀ s, shortSign σ (lowIdx j) (lowIdx (n := 2 * N + ε) ⟨j.val + 1, hj⟩) 1 s = 1 := by
    intro s
    simp only [shortSign, inv_one, map_one, CharTwo.neg_eq]
    split_ifs <;> rfl
  rw [ctuEmbed_apply_ctuCoord, signedPerm_apply, swap_mul_swap_rev_ctuCoord hε hj, mat_permSp,
    hd]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rcases w with u | i <;> rcases w' with v | i'
  · rw [fromBlocks_apply₁₁, map_apply, spIncl_apply]
    simp only [Sum.map_inl, Sum.inl.injEq]
    split_ifs <;> simp
  · rw [fromBlocks_apply₁₂]
    simp
  · rw [fromBlocks_apply₂₁]
    simp
  · rw [fromBlocks_apply₂₂, Matrix.one_apply]
    simp

theorem ctuEmbed_permSp_swap_mem_rankOne (hσ : ∀ c, σ (σ c) = c) {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) :
    ctuEmbed ε hε σ ι hι
        (permSp K (Equiv.swap (⟨j.val, by omega⟩ : Fin N) ⟨j.val + 1, by omega⟩)) ∈
      rankOne (rootGroup σ hσ (2 * N + ε)) j := by
  rw [ctuEmbed_permSp_swap_eq hσ hj]
  exact shortWeyl_mem_rankOne hσ hj 1

end Model

end CFSG.SeitzReduction.SymplecticPilot
