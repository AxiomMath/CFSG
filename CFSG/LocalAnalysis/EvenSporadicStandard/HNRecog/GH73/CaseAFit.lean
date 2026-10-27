module

public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private theorem oddCore_eq_pPrimeCore (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem exists_selfCentralizing_two_core {X : Type*} [Group X] [Finite X] [Nontrivial X]
    (hO : CFSG.oddCore X = ⊥) (hE : CFSG.layer X = ⊥) :
    ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 Q ∧ Q ≠ ⊥ ∧
      (∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N ≤ Q) ∧
      (∀ x : X, (∀ q ∈ Q, q * x = x * q) → x ∈ Q) := by
  have hcore : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [← oddCore_eq_pPrimeCore X]
    exact hO
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X 2 hcore hE
  refine ⟨CFSG.pCore 2 X, CFSG.pCore_normal, CFSG.pCore_isPGroup, ?_, ?_, ?_⟩
  · intro hQ
    have hbot : ∀ x : X, x ∈ (⊥ : Subgroup X) := by
      intro x
      rw [← hQ]
      exact hchar (Subgroup.mem_centralizer_iff.mpr (by
        intro q hq
        rw [hQ] at hq
        rw [Subgroup.mem_bot.mp hq]
        simp))
    exact not_subsingleton X ⟨fun a b => by
      rw [show a = 1 from by simpa using hbot a,
        show b = 1 from by simpa using hbot b]⟩
  · intro N hN hNp
    unfold CFSG.pCore
    exact le_sSup ⟨hN, hNp⟩
  · intro x hx
    exact hchar (Subgroup.mem_centralizer_iff.mpr hx)

end CFSG.EvenSporadicStandard.HNRecog.GH73
