module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddL28
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenU3
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenSL
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenSp
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenSU
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenOmegaTail
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenOmegaPlus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

section ClassicalFull

variable {q : ℕ}

theorem radRigid_classical_odd (hq : q.Prime) (hq2 : q ≠ 2) {S : Type} [Group S] [Finite S]
    {t : StatedLieTag} {n f : ℕ} (ht : t ∈ classicalTags) (h : StatedClassicalModel S t n q f)
    (hH : Holds S q) : RadRigid q S := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hI : RadRigidInner q S := radRigidInner_classical_odd hq hq2 ht h
  have hBT : HoldsTits S q := hH.holdsTits
  have hLI : ∀ R : Subgroup S, IsRadical q R → ∀ x : S, (∀ r ∈ R, x * r = r * x) → x ∈ R :=
    fun R hR => centralizer_le_of_radRigidInner hI hR
  have hadm := h.1
  simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨-, -, hn2, -, -⟩ := hadm
    rcases Nat.lt_or_ge n 3 with hn | hn
    · obtain rfl : n = 2 := by omega
      exact radRigid_of_sylowRigid hBT hLI (sylowRigid_of_PSL_two h)
    · obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
      haveI : CharP K q := charP_of_natCard_eq hcard
      exact radRigid_of_twoParabolics hBT hI
        ((twoParabolics_PSL (q := q) (F := K) hn).of_mulEquiv e.symm)
  ·
    obtain ⟨-, -, hn3, -⟩ := hadm
    rcases Nat.lt_or_ge n 4 with hn | hn
    · obtain rfl : n = 3 := by omega
      exact radRigid_of_sylowRigid hBT hLI (sylowRigid_of_PSU_three hq2 h)
    · exact radRigid_of_twoParabolics hBT hI (twoParabolics_PSU hn h)
  ·
    obtain ⟨-, -, hn2, -⟩ := hadm
    obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
    haveI : CharP K q := charP_of_natCard_eq hcard
    exact radRigid_of_twoParabolics hBT hI
      ((twoParabolics_PSp (q := q) (F := K) hn2).of_mulEquiv e.symm)
  ·
    exact radRigid_of_twoParabolics hBT hI (twoParabolics_POmegaOdd hq2 h)
  ·
    exact radRigid_of_twoParabolics hBT hI (twoParabolics_POmegaPlus h)
  ·
    exact radRigid_of_twoParabolics hBT hI (twoParabolics_POmegaMinus h)

end ClassicalFull

section Assembly


theorem oddFamiliesFull {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h28 : q = 3 → Psl28Full) :
    OddFamiliesFor q (fun S _ => RadRigid q S) := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact
    { classical := fun S _ _ _ _ t n f ht h hH => radRigid_classical_odd hq hq2 ht h hH
      exceptional := fun S _ _ _ _ t f ht h _ => radRigid_exceptional_odd hq hq2 ht h
      ree := fun S _ _ _ _ f h _ => radRigid_ree_odd h
      psl28 := fun hq3 S _ _ hs hna h => by
        subst hq3
        exact h28 rfl S hs hna h }

theorem lieQConstrained_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : LieQConstrained q :=
  lieQConstrained_of_oddFamilies hq hq2 (oddFamiliesFull hq hq2 fun _ => psl28Full)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
