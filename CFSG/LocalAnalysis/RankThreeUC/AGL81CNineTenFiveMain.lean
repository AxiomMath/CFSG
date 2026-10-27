module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

section Abstract

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem le_oPPrimeHull_top_of_isElemAbelian (hp : p.Prime) {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian p E) : E ≤ oPPrimeHull p (⊤ : Subgroup X) := by
  intro x hxE
  refine Subgroup.subset_closure ⟨Subgroup.mem_top x, ?_⟩
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hE.2 x hxE)
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

namespace IsSplitCover

variable {L W : Subgroup X}

theorem five_core (h661 : SixSixOneRank) (hp : p.Prime) (hp3 : 3 < p) (hLn : L.Normal)
    (hW : IsSplitCover p L W) (hZ : ∀ z ∈ L, z ∈ centralizer (L : Set X) → z ^ p = 1 → z = 1)
    (hRY : CFSG.pCore p X ≤ centralizer (L : Set X))
    (hYR : centralizer (L : Set X) ⊓ centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) (hrkL : CFSG.Open.pRank p L ≤ 1)
    (hLq : CFSG.IsQuasisimple ↥L) {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2)
    (hEY : ∀ U : Subgroup X, U ≤ E ⊔ centralizer (L : Set X) →
      (U.subgroupOf (E ⊔ centralizer (L : Set X))).Normal → IsPGroup p U → ¬ E ≤ U) :
    oPPrimeHull p (⊤ : Subgroup X) = L ⊔ oPPrimeHull p (centralizer (L : Set X)) ∧
      IsExtNotation (fun B _ => IsSLType 2 (ZMod p) B) (fun B _ => IsHomocyclicRank2 p B)
        ↥(oPPrimeHull p (centralizer (L : Set X))) ∧
      ∃ x ∈ E, x ∈ centralizer (L : Set X) ∧ x ≠ 1 := by
  have hEO : E ≤ oPPrimeHull p (⊤ : Subgroup X) := le_oPPrimeHull_top_of_isElemAbelian hp hE
  have hEW : E ≤ L ⊔ W := hEO.trans hW.2.2.1
  have hV : ¬ IsPGroup p ↥(closure {x : X | x ∈ W ∧ orderOf x = p}) := by
    intro hVp
    obtain ⟨hUp, hUn⟩ := normal_sup_pCore_of_isPGroup hp hLn hW hZ hRY hE hEW hVp
    exact hEY (E ⊔ CFSG.pCore p X) (sup_le_sup_left hRY E) hUn hUp le_sup_left
  obtain ⟨hWV, hYV, hext⟩ := oPPrimeHull_eq h661 hp hp3 hLn hW hZ hRY hYR hrk hV
  have htop := oPPrimeHull_top_eq hp hLn hW hZ hLq
  have htop' : oPPrimeHull p (⊤ : Subgroup X) =
      L ⊔ oPPrimeHull p (centralizer (L : Set X)) := by
    rw [htop, hWV, hYV]
  have hYle : oPPrimeHull p (centralizer (L : Set X)) ≤ centralizer (L : Set X) := by
    rw [oPPrimeHull, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx
  have hElY : E ≤ L ⊔ centralizer (L : Set X) :=
    (hEO.trans htop'.le).trans (sup_le_sup_left hYle L)
  obtain ⟨x, hxE, hxY, hx1⟩ :=
    exists_mem_inf_ne_one_of_le_sup hp hLn hrkL hZ hE hEc hElY
  exact ⟨htop', by rw [hYV]; exact hext, x, hxE, hxY, hx1⟩

end IsSplitCover

end Abstract

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
