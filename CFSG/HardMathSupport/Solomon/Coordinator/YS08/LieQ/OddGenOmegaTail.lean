module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenOmega
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddInner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

section TailFlag

variable {K : Type} [Field K] {κ : Type} [DecidableEq κ]

@[expose] def tailVec (r : ℕ) (K : Type) [Field K] (κ : Type) [DecidableEq κ] (j : Fin r) :
    Fin r ⊕ Fin r ⊕ κ → K :=
  Pi.single (Sum.inl j) 1

theorem tailVec_ne_zero {r : ℕ} (j : Fin r) : (tailVec r K κ j) ≠ 0 := fun h => by
  have := congrFun h (Sum.inl j)
  simp [tailVec] at this

theorem tailModelFlag_zero {r : ℕ} (h : 0 < r) :
    tailModelFlag r K κ ⟨0, h⟩ = Submodule.span K {tailVec r K κ ⟨0, h⟩} := by
  unfold tailModelFlag
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have : j = ⟨0, h⟩ := Fin.ext (by simp at hj ⊢; omega)
    rw [this]
    rfl
  · rintro rfl
    exact ⟨⟨0, h⟩, by simp, rfl⟩

theorem tailModelFlag_one {r : ℕ} (h : 1 < r) :
    tailModelFlag r K κ ⟨1, h⟩ = Submodule.span K {tailVec r K κ ⟨0, by omega⟩} ⊔
      Submodule.span K {tailVec r K κ ⟨1, h⟩} := by
  unfold tailModelFlag
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : (j : ℕ) < 2 := by simpa using hj
    by_cases hj0 : (j : ℕ) = 0
    · left
      have : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [this]
      rfl
    · right
      have : j = ⟨1, h⟩ := Fin.ext (show (j : ℕ) = 1 by omega)
      rw [this]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by omega⟩, by simp, rfl⟩
    · exact ⟨⟨1, h⟩, by simp, rfl⟩

theorem tailVec_one_notMem {r : ℕ} (h : 1 < r) :
    tailVec r K κ ⟨1, h⟩ ∉ Submodule.span K {tailVec r K κ ⟨0, by omega⟩} := by
  intro hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have := congrFun ha (Sum.inl ⟨1, h⟩)
  simp [tailVec, Pi.single_apply] at this

end TailFlag

section Tail

variable {q : ℕ} [Fact q.Prime]

theorem twoParabolics_POmegaOdd (hq2 : q ≠ 2) {n f : ℕ} {S : Type} [Group S] [Finite S]
    (hm : StatedClassicalModel S .POmegaOdd n q f) : TwoParabolics q S := by
  have hBI := orthogonal_geometry_tail_model_Borel_overgroup_interface S .POmegaOdd (Or.inl rfl) n q f hm
  obtain ⟨⟨-, -, hn3, -⟩, K, _, hfin, hcard, ⟨e⟩⟩ := hm
  haveI : CharP K q := charP_of_natCard_eq hcard
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_odd hq2
  have hBIK : BorelInterface q (StatedQuadOdd n K) (tailModelFlag n K Unit) := hBI K hcard
  have hι : 6 ≤ Fintype.card (Fin n ⊕ Fin n ⊕ Unit) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have key := twoParabolics_Omega_of_borel (quadOddForm n K h2) hι (tailModelFlag n K Unit) hBIK
    ⟨0, h0⟩ ⟨1, h1⟩ rfl rfl (x₁ := tailVec n K Unit ⟨0, h0⟩) (x₂ := tailVec n K Unit ⟨1, h1⟩)
    (tailVec_ne_zero _) (tailVec_one_notMem h1) (tailModelFlag_zero h0) (tailModelFlag_one h1)
  exact key.of_mulEquiv e.symm

theorem twoParabolics_POmegaMinus {n f : ℕ} {S : Type} [Group S] [Finite S]
    (hm : StatedClassicalModel S .POmegaMinus n q f) : TwoParabolics q S := by
  have hBI := orthogonal_geometry_tail_model_Borel_overgroup_interface S .POmegaMinus (Or.inr rfl) n q f hm
  obtain ⟨⟨-, -, hn4⟩, K, _, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hm
  haveI : CharP K q := charP_of_natCard_eq hcard
  have hBIK : BorelInterface q (StatedQuadMinus n K b c) (tailModelFlag (n - 1) K (Fin 2)) :=
    hBI K hcard b c hirr
  have hι : 6 ≤ Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have h0 : 0 < n - 1 := by omega
  have h1 : 1 < n - 1 := by omega
  have key := twoParabolics_Omega_of_borel (quadMinusForm n K b c hirr) hι
    (tailModelFlag (n - 1) K (Fin 2)) hBIK ⟨0, h0⟩ ⟨1, h1⟩ rfl rfl
    (x₁ := tailVec (n - 1) K (Fin 2) ⟨0, h0⟩) (x₂ := tailVec (n - 1) K (Fin 2) ⟨1, h1⟩)
    (tailVec_ne_zero _) (tailVec_one_notMem h1) (tailModelFlag_zero h0) (tailModelFlag_one h1)
  exact key.of_mulEquiv e.symm

end Tail

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
