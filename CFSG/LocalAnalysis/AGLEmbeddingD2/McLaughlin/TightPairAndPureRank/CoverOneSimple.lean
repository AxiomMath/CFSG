module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.HallHigman

theorem not_isPSolvable_three_of_simple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ¬ IsMulCommutative S) (h3 : 3 ∣ Nat.card S) : ¬ IsPSolvable 3 S := by
  intro hN
  have e : (↥(⊤ : Subgroup S) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup S))) ≃* S :=
    (QuotientGroup.quotientBot).trans Subgroup.topEquiv
  have hsimple : IsSimpleGroup (↥(⊤ : Subgroup S) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup S))) :=
    haveI := hS; e.isSimpleGroup
  have hidx : (⊥ : Subgroup ↥(⊤ : Subgroup S)).index = Nat.card S := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr e.toEquiv
  rcases hN ⊤ (Subgroup.Normal.isSubnormal inferInstance) ⊥ hsimple with h | h
  · rw [hidx] at h
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic S := isCyclic_of_prime_card (p := 3) h
    exact hnc ⟨⟨fun a b => mul_comm a b⟩⟩
  · rw [hidx] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h h3

theorem not_isPSolvable_perm_six : ¬ IsPSolvable 3 (Equiv.Perm (Fin 6)) := by
  intro hs
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 : 5 ≤ Nat.card (Fin 6) := by simp
  have hS : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h5
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    intro hc
    have := hS.prime_card
    rw [hcard] at this
    exact absurd this (by norm_num)
  have hsol : IsPSolvable 3 ↥(⊤ : Subgroup (Equiv.Perm (Fin 6))) :=
    Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv.symm hs
  exact not_isPSolvable_three_of_simple hS hnc (by rw [hcard]; norm_num)
    (Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hsol le_top)

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
