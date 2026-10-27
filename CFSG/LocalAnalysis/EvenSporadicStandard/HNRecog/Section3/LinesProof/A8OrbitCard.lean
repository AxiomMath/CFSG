module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma linesA8_card_S (S : Subgroup (alternatingGroup (Fin 8)))
    (hS : Nonempty (↥S ≃* alternatingGroup (Fin 5))) : Nat.card ↥S = 60 := by
  have h1 : Nat.card ↥S = Nat.card (alternatingGroup (Fin 5)) :=
    Nat.card_congr hS.some.toEquiv
  rw [h1, nat_card_alternatingGroup, Nat.card_fin]
  decide

private lemma linesA8_index_ne_two_three_four
    (S : Subgroup (alternatingGroup (Fin 8)))
    (hS : Nonempty (↥S ≃* alternatingGroup (Fin 5))) (i : Fin 8)
    (hcardS : Nat.card ↥S = 60) :
    (MulAction.stabilizer ↥S i).index ≠ 2 ∧
      (MulAction.stabilizer ↥S i).index ≠ 3 ∧
      (MulAction.stabilizer ↥S i).index ≠ 4 := by
  haveI : IsSimpleGroup ↥S := hS.some.isSimpleGroup
  set H : Subgroup ↥S := MulAction.stabilizer ↥S i with hH
  have hcore : H.normalCore = ⊥ ∨ H.normalCore = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore
  have key : ∀ c : ℕ, H.index = c → (c = 2 ∨ c = 3 ∨ c = 4) → False := by
    intro c hidx hc
    rcases hcore with hbot | htop
    · have hle : Nat.card ↥S ≤ Nat.factorial H.index := by
        have h := Subgroup.index_normalCore_le_factorial_index H
        rwa [hbot, Subgroup.index_bot] at h
      rw [hcardS, hidx] at hle
      rcases hc with rfl | rfl | rfl <;> exact absurd hle (by decide)
    · have htopH : H = ⊤ := le_antisymm le_top (htop ▸ H.normalCore_le)
      rw [htopH, Subgroup.index_top] at hidx
      rcases hc with rfl | rfl | rfl <;> norm_num at hidx
  exact ⟨fun h => key 2 h (Or.inl rfl), fun h => key 3 h (Or.inr (Or.inl rfl)),
    fun h => key 4 h (Or.inr (Or.inr rfl))⟩

theorem linesA8_orbit_card (S : Subgroup (alternatingGroup (Fin 8)))
    (hS : Nonempty (↥S ≃* alternatingGroup (Fin 5))) (i : Fin 8) :
    Set.ncard {j : Fin 8 | ∃ g : alternatingGroup (Fin 8), g ∈ S ∧
      (g : Equiv.Perm (Fin 8)) i = j} ∈ ({1, 5, 6} : Set ℕ) := by
  have hO : ({j : Fin 8 | ∃ g : alternatingGroup (Fin 8), g ∈ S ∧
      (g : Equiv.Perm (Fin 8)) i = j} : Set (Fin 8)) = MulAction.orbit ↥S i := by
    ext j
    constructor
    · rintro ⟨g, hg, hgj⟩
      exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩, hgj⟩
    · intro hj
      obtain ⟨⟨g, hg⟩, hgj⟩ := MulAction.mem_orbit_iff.mp hj
      exact ⟨g, hg, hgj⟩
  rw [hO, ← MulAction.index_stabilizer ↥S i]
  have hcardS : Nat.card ↥S = 60 := linesA8_card_S S hS
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (MulAction.stabilizer ↥S i).index := ⟨_, rfl⟩
  have hdvd : n ∣ 60 := by
    rw [hn]
    simpa [hcardS] using (MulAction.stabilizer ↥S i).index_dvd_card
  have hle : n ≤ 8 := by
    rw [hn, MulAction.index_stabilizer ↥S i]
    calc (MulAction.orbit ↥S i).ncard ≤ Nat.card (Fin 8) := Set.ncard_le_card _
      _ = 8 := by simp
  have hpos : 1 ≤ n := by
    rw [hn, MulAction.index_stabilizer ↥S i]
    have hne : (MulAction.orbit ↥S i).ncard ≠ 0 :=
      Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self i)
    omega
  have hnot := linesA8_index_ne_two_three_four S hS i hcardS
  rw [← hn] at hnot
  rw [← hn]
  interval_cases n
  · simp
  · exact absurd rfl hnot.1
  · exact absurd rfl hnot.2.1
  · exact absurd rfl hnot.2.2
  · simp
  · simp
  · exact absurd hdvd (by decide)
  · exact absurd hdvd (by decide)

end CFSG.EvenSporadicStandard.HNRecog.Section3
