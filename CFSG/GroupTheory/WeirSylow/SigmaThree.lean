module

public import CFSG.GroupTheory.WeirSylow.Defs
public import CFSG.GroupTheory.UniqueElemSylow
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

private theorem sigmaModelEquivWreath_digits {a : ℕ} {L : List ℕ} (hL : L = [0, 1]) :
    Nonempty (((i : Fin L.length) → Fin L[i] →
      wreathTower 3 (Multiplicative (ZMod (3 ^ a))) ↑i) ≃*
      (Multiplicative (ZMod (3 ^ a)) ≀ᵣ Multiplicative (ZMod 3))) := by
  subst L
  let β : Fin 2 → Type := fun i =>
    Fin ([0, 1] : List ℕ)[i] → wreathTower 3 (Multiplicative (ZMod (3 ^ a))) ↑i
  haveI : Unique (β 0) := ⟨⟨fun j => j.elim0⟩, fun f => funext fun j => j.elim0⟩
  refine ⟨(MulEquiv.mk' (piFinTwoEquiv β) (fun f g => rfl)).trans ?_⟩
  refine MulEquiv.uniqueProd.trans ?_
  exact MulEquiv.funUnique (Fin 1)
    (Multiplicative (ZMod (3 ^ a)) ≀ᵣ Multiplicative (ZMod 3))

theorem sigmaModelEquivWreath {e a N : ℕ} (h : N / e = 3) :
    Nonempty (sigmaModel 3 e a N ≃*
      (Multiplicative (ZMod (3 ^ a)) ≀ᵣ Multiplicative (ZMod 3))) := by
  have hdig : Nat.digits 3 (N / e) = [0, 1] := by rw [h]; decide
  change Nonempty (((i : Fin (Nat.digits 3 (N / e)).length) →
      Fin (Nat.digits 3 (N / e))[i] →
        wreathTower 3 (Multiplicative (ZMod (3 ^ a))) ↑i) ≃*
      (Multiplicative (ZMod (3 ^ a)) ≀ᵣ Multiplicative (ZMod 3)))
  exact sigmaModelEquivWreath_digits hdig

theorem uniqueElemSylow_of_sigmaModel {G : Type*} [Group G] [Finite G] {e a N : ℕ} (ha : 1 ≤ a)
    (h : N / e = 3) (hP : ∀ P : Sylow 3 G, Nonempty (P ≃* sigmaModel 3 e a N)) :
    UniqueElemSylow 3 3 G := by
  obtain ⟨A, _, habel, hcard, huniq, _⟩ := zwr_unique_E27_Zwr (n := a) ha
  have hM : ∃! A : Subgroup (ZWr a),
      CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
    refine ⟨A, ⟨habel, by rw [hcard]; norm_num⟩, ?_⟩
    intro B hB
    exact huniq B hB.1 (by rw [hB.2]; norm_num)
  refine UniqueElemSylow.of_forall_sylow_mulEquiv (p := 3) (k := 3) hM ?_
  intro P
  obtain ⟨φ⟩ := hP P
  obtain ⟨ψ⟩ := sigmaModelEquivWreath (e := e) (a := a) (N := N) h
  exact ⟨φ.trans ψ⟩

end CFSG.GroupTheory.WeirSylow
