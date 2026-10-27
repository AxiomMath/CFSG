module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveWit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallThreeOrders
public import CFSG.Sporadic.Bridge.Common
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.L34

open Equiv CFSG.Sporadic.Bridge CFSG.ComponentClassification.PSL3Four
open CFSG.AGLEmbedding.KFactProofs.RankOneCore CFSG.Assembly.LowTwoRank

@[expose] def g1T : Perm (Fin 42) :=
  tabPerm
    ![
      5, 0, 6, 8, 7, 1, 9, 17, 13, 2, 10, 20, 15, 3, 11, 18, 16, 4, 12, 19, 14, 26, 21, 27, 29, 28,
      22, 30, 38, 34, 23, 31, 41, 36, 24, 32, 39, 37, 25, 33, 40, 35
    ]
    ![
      1, 5, 9, 13, 17, 0, 2, 4, 3, 6, 10, 14, 18, 8, 20, 12, 16, 7, 15, 19, 11, 22, 26, 30, 34, 38,
      21, 23, 25, 24, 27, 31, 35, 39, 29, 41, 33, 37, 28, 36, 40, 32
    ] (by decide)
@[expose] def g2T : Perm (Fin 42) :=
  tabPerm
    ![
      0, 9, 10, 11, 12, 5, 6, 7, 8, 1, 2, 3, 4, 17, 19, 20, 18, 13, 16, 14, 15, 21, 22, 23, 24, 25,
      30, 31, 32, 33, 26, 27, 28, 29, 38, 39, 40, 41, 34, 35, 36, 37
    ]
    ![
      0, 9, 10, 11, 12, 5, 6, 7, 8, 1, 2, 3, 4, 17, 19, 20, 18, 13, 16, 14, 15, 21, 22, 23, 24, 25,
      30, 31, 32, 33, 26, 27, 28, 29, 38, 39, 40, 41, 34, 35, 36, 37
    ] (by decide)
@[expose] def g3T : Perm (Fin 42) :=
  tabPerm
    ![
      0, 17, 20, 18, 19, 5, 6, 7, 8, 13, 15, 16, 14, 9, 12, 10, 11, 1, 3, 4, 2, 21, 22, 23, 24, 25,
      34, 35, 36, 37, 38, 39, 40, 41, 26, 27, 28, 29, 30, 31, 32, 33
    ]
    ![
      0, 17, 20, 18, 19, 5, 6, 7, 8, 13, 15, 16, 14, 9, 12, 10, 11, 1, 3, 4, 2, 21, 22, 23, 24, 25,
      34, 35, 36, 37, 38, 39, 40, 41, 26, 27, 28, 29, 30, 31, 32, 33
    ] (by decide)

@[expose] def aP : Perm (Fin 42) :=
  tabPerm
    ![
      2, 0, 1, 3, 4, 9, 6, 19, 16, 10, 5, 20, 15, 11, 8, 17, 14, 12, 7, 18, 13, 30, 31, 21, 32, 33,
      26, 22, 38, 34, 23, 27, 37, 40, 41, 35, 28, 24, 36, 39, 25, 29
    ]
    ![
      1, 2, 0, 3, 4, 10, 6, 18, 14, 5, 9, 13, 17, 20, 16, 12, 8, 15, 19, 7, 11, 23, 27, 30, 37, 40,
      26, 31, 36, 41, 21, 22, 24, 25, 29, 35, 38, 32, 28, 39, 33, 34
    ] (by decide)
@[expose] def bP : Perm (Fin 42) :=
  tabPerm
    ![
      15, 12, 17, 6, 3, 9, 4, 18, 8, 10, 5, 2, 20, 0, 14, 13, 16, 11, 19, 7, 1, 30, 32, 21, 33, 31,
      35, 24, 28, 41, 23, 37, 40, 27, 29, 39, 36, 25, 38, 26, 22, 34
    ]
    ![
      13, 20, 11, 4, 6, 10, 3, 19, 8, 5, 9, 17, 1, 15, 14, 0, 16, 2, 7, 18, 12, 23, 40, 30, 27, 37,
      39, 33, 28, 34, 21, 25, 22, 24, 41, 26, 36, 31, 38, 35, 32, 29
    ] (by decide)
@[expose] def xP : Perm (Fin 42) :=
  tabPerm
    ![
      0, 11, 12, 9, 10, 6, 5, 8, 7, 4, 3, 2, 1, 20, 18, 17, 19, 13, 16, 14, 15, 39, 22, 35, 27, 31,
      30, 25, 29, 36, 26, 24, 37, 32, 38, 21, 41, 40, 34, 23, 33, 28
    ]
    ![
      0, 12, 11, 10, 9, 6, 5, 8, 7, 3, 4, 1, 2, 17, 19, 20, 18, 15, 14, 16, 13, 35, 22, 39, 31, 27,
      30, 24, 41, 28, 26, 25, 33, 40, 38, 23, 29, 32, 34, 21, 37, 36
    ] (by decide)
@[expose] def yP : Perm (Fin 42) :=
  tabPerm
    ![
      0, 13, 15, 16, 14, 7, 8, 5, 6, 18, 19, 17, 20, 2, 3, 1, 4, 12, 10, 9, 11, 41, 22, 29, 33, 37,
      38, 40, 39, 21, 34, 32, 27, 25, 30, 28, 35, 24, 26, 36, 31, 23
    ]
    ![
      0, 15, 13, 14, 16, 7, 8, 5, 6, 19, 18, 20, 17, 1, 4, 2, 3, 11, 9, 10, 12, 29, 22, 41, 37, 33,
      38, 32, 35, 23, 34, 40, 31, 24, 30, 36, 39, 25, 26, 28, 27, 21
    ] (by decide)

@[expose] def gen (i : ℕ) : Perm (Fin 42) :=
  if i = 0 then g1T else if i = 1 then g2T else if i = 2 then g3T else 1

theorem g1T_eq : g1T = g₁ := by decide +kernel
theorem g2T_eq : g2T = g₂ := by decide +kernel
theorem g3T_eq : g3T = g₃ := by decide +kernel

theorem gen_mem (i : ℕ) : gen i ∈ S := by
  unfold gen
  split
  · exact g1T_eq ▸ Subgroup.subset_closure (by simp)
  · split
    · exact g2T_eq ▸ Subgroup.subset_closure (by simp)
    · split
      · exact g3T_eq ▸ Subgroup.subset_closure (by simp)
      · exact Subgroup.one_mem _

theorem word_mem (w : List (ℕ × Bool)) : wordProd gen w ∈ S := wordProd_mem gen_mem w

@[expose] def wA : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false)]
@[expose] def wB : List (ℕ × Bool) :=
  [(0, false), (2, false), (0, false), (2, false), (0, true), (2, false), (0, true), (2, false),
    (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false)]
@[expose] def wX : List (ℕ × Bool) :=
  [(2, true), (1, true), (0, false), (1, false), (0, true), (2, false)]
@[expose] def wY : List (ℕ × Bool) :=
  [(2, true), (1, true), (0, false), (2, true), (0, true)]

theorem aP_eq : aP = wordProd gen wA := by decide +kernel
theorem bP_eq : bP = wordProd gen wB := by decide +kernel
theorem xP_eq : xP = wordProd gen wX := by decide +kernel
theorem yP_eq : yP = wordProd gen wY := by decide +kernel

theorem hab : aP * bP = bP * aP := by decide +kernel
theorem hap : aP ^ 3 = 1 := by decide +kernel
theorem hbp : bP ^ 3 = 1 := by decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem hdist : ∀ i < 3, ∀ j < 3, ∀ i' < 3, ∀ j' < 3, aP ^ i * bP ^ j = aP ^ i' * bP ^ j' →
    i = i' ∧ j = j' := by decide +kernel

theorem hx : (∃ i j : ℕ, xP * aP * xP⁻¹ = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, xP * bP * xP⁻¹ = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, xP⁻¹ * aP * xP = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, xP⁻¹ * bP * xP = aP ^ i * bP ^ j) :=
  ⟨⟨2, 1, by decide +kernel⟩, ⟨1, 1, by decide +kernel⟩, ⟨1, 2, by decide +kernel⟩,
    ⟨2, 2, by decide +kernel⟩⟩

theorem hy : (∃ i j : ℕ, yP * aP * yP⁻¹ = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, yP * bP * yP⁻¹ = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, yP⁻¹ * aP * yP = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, yP⁻¹ * bP * yP = aP ^ i * bP ^ j) :=
  ⟨⟨0, 1, by decide +kernel⟩, ⟨2, 0, by decide +kernel⟩, ⟨0, 2, by decide +kernel⟩,
    ⟨1, 0, by decide +kernel⟩⟩

theorem hxy : ∀ i < 3, ∀ j < 3, xP * yP * xP⁻¹ * yP⁻¹ ≠ aP ^ i * bP ^ j := by decide +kernel

theorem not_normalizerQuotientComm_S (hS : Nat.card S = 20160) :
    ¬ NormalizerQuotientComm 3 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact not_normalizerQuotientComm_of_elemAbelian S (p := 3) (m := 2240)
    (by rw [hS]; norm_num) (by norm_num) aP bP xP yP (aP_eq ▸ word_mem wA)
    (bP_eq ▸ word_mem wB) (xP_eq ▸ word_mem wX) (yP_eq ▸ word_mem wY) hab hap hbp hdist hx hy hxy

theorem not_normalizerQuotientComm_linThreeFour
    {L : Type} [Group L] [Finite L] (hL : IsLinThreeFour L) : ¬ NormalizerQuotientComm 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := id hL
  obtain ⟨eS⟩ := CFSG.AGLEmbeddingD2.nonempty_equiv_S_of_index hd e
  have hcard : Nat.card S = 20160 := by
    rw [← Nat.card_congr eS.toEquiv]
    exact card_of_isLinThreeFour hL
  intro h
  exact not_normalizerQuotientComm_S hcard (h.of_mulEquiv eS)

end CFSG.AGLEmbedding.KFactProofs.SmallBad.L34
