module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveWit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.M11

open Equiv CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.M11 CFSG.Blueprint
open CFSG.AGLEmbedding.KFactProofs.RankOneCore CFSG.AGLEmbedding.KFactProofs.SmallIdent

@[expose] def aP : Perm (Fin 11) :=
  tabPerm ![0, 1, 9, 7, 6, 2, 10, 8, 3, 5, 4] ![0, 1, 5, 8, 10, 9, 4, 3, 7, 2, 6] (by decide)
@[expose] def bP : Perm (Fin 11) :=
  tabPerm ![0, 1, 4, 2, 3, 10, 7, 9, 5, 6, 8] ![0, 1, 3, 4, 2, 8, 9, 6, 10, 7, 5] (by decide)
@[expose] def xP : Perm (Fin 11) :=
  tabPerm ![0, 1, 2, 5, 9, 4, 7, 8, 10, 3, 6] ![0, 1, 2, 9, 5, 3, 10, 6, 7, 4, 8] (by decide)
@[expose] def yP : Perm (Fin 11) :=
  tabPerm ![0, 1, 2, 6, 8, 10, 4, 5, 3, 7, 9] ![0, 1, 2, 8, 6, 7, 3, 9, 4, 10, 5] (by decide)

@[expose] def wA : List (ℕ × Bool) :=
  [(1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
    (1, true), (0, true), (0, true)]
@[expose] def wB : List (ℕ × Bool) :=
  [(0, false), (1, false), (1, false), (0, false), (0, false), (1, false), (0, false), (1, true),
    (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (0, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, true),
    (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true)]
@[expose] def wX : List (ℕ × Bool) :=
  [(1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false),
    (1, false), (0, false), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (0, true), (0, true), (1, false), (0, true), (1, true),
    (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (1, true), (1, true),
    (0, true)]
@[expose] def wY : List (ℕ × Bool) :=
  [(0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true),
    (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
    (0, true)]

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
  ⟨⟨0, 2, by decide +kernel⟩, ⟨1, 0, by decide +kernel⟩, ⟨0, 1, by decide +kernel⟩,
    ⟨2, 0, by decide +kernel⟩⟩

theorem hy : (∃ i j : ℕ, yP * aP * yP⁻¹ = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, yP * bP * yP⁻¹ = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, yP⁻¹ * aP * yP = aP ^ i * bP ^ j) ∧
    (∃ i j : ℕ, yP⁻¹ * bP * yP = aP ^ i * bP ^ j) :=
  ⟨⟨1, 2, by decide +kernel⟩, ⟨2, 2, by decide +kernel⟩, ⟨2, 1, by decide +kernel⟩,
    ⟨1, 1, by decide +kernel⟩⟩

theorem hxy : ∀ i < 3, ∀ j < 3, xP * yP * xP⁻¹ * yP⁻¹ ≠ aP ^ i * bP ^ j := by decide +kernel

theorem not_normalizerQuotientComm_nativeM11 :
    ¬ NormalizerQuotientComm 3 Blueprint.NativeSporadic.M11 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact not_normalizerQuotientComm_of_elemAbelian Blueprint.NativeSporadic.M11 (p := 3) (m := 880)
    (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num) (by norm_num) aP bP xP yP
    (aP_eq ▸ nativeWord_mem wA)
    (bP_eq ▸ nativeWord_mem wB) (xP_eq ▸ nativeWord_mem wX) (yP_eq ▸ nativeWord_mem wY) hab hap
    hbp hdist hx hy hxy

theorem not_normalizerQuotientComm_m11
    {L : Type} [Group L] [Finite L] (hK : IsSporadicGroup .M11 L) :
    ¬ NormalizerQuotientComm 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_equiv_m11 hK
  intro h
  exact not_normalizerQuotientComm_nativeM11 (h.of_mulEquiv e)

end CFSG.AGLEmbedding.KFactProofs.SmallBad.M11
