module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracK5
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracDich
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Frac
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracSw

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem false_of_piece (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {w : X}
    (hwZ : w ∈ Z) (hw1 : w ≠ 1) (hws : w * s = s * w) {P : Subgroup X}
    (hP : IsPCompIn 2 (centralizer ({w} : Set X) ⊓ centralizer ({s} : Set X)) P) (hwP : w ∈ P) :
    False := by
  classical
  have hw2 : w * w = 1 := h.Z_sq_eq_one hwZ
  have hsw : s * w = w * s := hws.symm
  obtain ⟨M₀, hM₀, hPM₀⟩ := exists_isPCompIn_above_of_comp hw2 hsw hP hwP
  have hwM₀ : w ∈ M₀ := hPM₀ hwP
  have hwD : w ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hws
  have hW : ∃ B : Subgroup X, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
      w ∈ centralizerSection B (pPrimeCoreOf 2 B) := by
    by_cases hM₀A : Sec5Comp X n (centralizer ({s} : Set X)) M₀
    · refine ⟨M₀, hM₀A, ?_⟩
      have hPCw : P ≤ centralizer ({w} : Set X) := hP.1.trans inf_le_left
      have hPM : P ≤ M₀ ⊓ centralizer ({w} : Set X) := le_inf hPM₀ hPCw
      have hMH : M₀ ⊓ centralizer ({w} : Set X) ≤
          centralizer ({w} : Set X) ⊓ centralizer ({s} : Set X) :=
        le_inf inf_le_right (inf_le_left.trans hM₀.1)
      have hP' : IsPComponent 2 (P.subgroupOf (M₀ ⊓ centralizer ({w} : Set X))) :=
        isPComponent_subgroupOf_mono hPM hMH hP.2
      exact mem_centralizerSection_of_piece hM₀A.2 hwM₀ hw2 hPM hP' hwP
    · obtain ⟨B, hB, -⟩ := h.exists_comp_centralizer hs
      have hBM : B ≠ M₀ := fun e => hM₀A (e ▸ hB)
      refine ⟨B, hB, ?_⟩
      have hcomm : ∀ l ∈ B, ⁅l, w⁆ ∈ pPrimeCoreOf 2 (centralizer ({s} : Set X)) := by
        intro l hl
        have h1 := aux_K0_comm_mem_of_ne_comm hB.isPCompIn hM₀ hBM l hl w hwM₀
        exact oddCoreOf_le_of_isPCompIn hB.isPCompIn h1
      exact normalizes_isPCompIn_of_comm_mem hB.isPCompIn (Subgroup.le_normalizer hwD) hcomm
  obtain ⟨B, hB, hQ⟩ := hW
  have hw2' : w ^ 2 = 1 := by
    rw [sq]
    exact hw2
  exact K0_K0_inf_ne_bot_of_mem_centralizerSection hw2' hB hQ
    (sec5_K0_inf_eq_bot h hs hwZ hw1 hws)

end CFSG.OddStandard.Solomon75
