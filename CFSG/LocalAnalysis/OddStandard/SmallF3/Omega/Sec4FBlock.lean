module

public section

namespace CFSG.OddStandard.SmallF3.Omega

universe u

@[expose] def Sec4FBlock {Ω : Type u} (R : Ω → Ω → Prop) (a a' c c' : Ω) : Prop :=
  a ≠ a' ∧ c ≠ c' ∧ (∀ g, R g c ↔ g = a ∨ g = a') ∧ (∀ g, R g c' ↔ g = a ∨ g = a') ∧
    (∀ e, R a e ↔ e = c ∨ e = c') ∧ (∀ e, R a' e ↔ e = c ∨ e = c')

theorem sec4F_block_exists {Ω : Type u} (R : Ω → Ω → Prop)
    (hL : ∀ c, ∃ u v, u ≠ v ∧ ∀ g, R g c ↔ g = u ∨ g = v)
    (hR : ∀ a, ∃ u v, u ≠ v ∧ ∀ c, R a c ↔ c = u ∨ c = v)
    (hov : ∀ c c' g, R g c → R g c' → ∀ g', R g' c ↔ R g' c') (a : Ω) :
    ∃ a' c c', Sec4FBlock R a a' c c' := by
  have key : ∀ c : Ω, R a c → ∃ a', a' ≠ a ∧ ∀ g, R g c ↔ g = a ∨ g = a' := by
    intro c hac
    obtain ⟨u, v, huv, hLc⟩ := hL c
    rcases (hLc a).mp hac with hau | hav
    · refine ⟨v, ?_, ?_⟩
      · rw [hau]
        exact Ne.symm huv
      · intro g
        rw [hLc g, hau]
    · refine ⟨u, ?_, ?_⟩
      · rw [hav]
        exact huv
      · intro g
        rw [hLc g, hav]
        exact or_comm
  obtain ⟨c, c', hcc', hRc⟩ := hR a
  have hac : R a c := (hRc c).mpr (Or.inl rfl)
  have hac' : R a c' := (hRc c').mpr (Or.inr rfl)
  obtain ⟨a', ha'a, hLc'⟩ := key c hac
  have hLc'_c' : ∀ g, R g c' ↔ g = a ∨ g = a' := fun g =>
    (hov c c' a hac hac' g).symm.trans (hLc' g)
  have ha'c : R a' c := (hLc' a').mpr (Or.inr rfl)
  have ha'c' : R a' c' := (hLc'_c' a').mpr (Or.inr rfl)
  obtain ⟨u', v', huv', hRa'⟩ := hR a'
  have hcu' : c = u' ∨ c = v' := (hRa' c).mp ha'c
  have hc'u' : c' = u' ∨ c' = v' := (hRa' c').mp ha'c'
  have ha'_nbhd : ∀ e, R a' e ↔ e = c ∨ e = c' := by
    intro e
    rw [hRa' e]
    rcases hcu' with h1 | h1 <;> rcases hc'u' with h2 | h2
    · exact absurd (h1.trans h2.symm) hcc'
    · rw [← h1, ← h2]
    · rw [← h2, ← h1]
      exact or_comm
    · exact absurd (h1.trans h2.symm) hcc'
  exact ⟨a', c, c', ha'a.symm, hcc', hLc', hLc'_c', hRc, ha'_nbhd⟩

end CFSG.OddStandard.SmallF3.Omega
