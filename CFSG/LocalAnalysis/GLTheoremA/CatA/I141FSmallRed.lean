module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDyn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

abbrev rsG2Char2 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .G2 q => q.p = 2 | _ => False

abbrev rsG2Odd : TauCeti.CFSGIndex → Prop :=
  onLie fun | .G2 q => q.p ≠ 2 | _ => False

abbrev rsU3 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 3 | _ => False

abbrev rsAlt (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  fun | .alternating m _ => m = n | _ => False

abbrev rsL27 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 1 q => q.card = 7 | _ => False

abbrev rsTits : TauCeti.CFSGIndex → Prop :=
  onLie fun d => d = TauCeti.LieTypeIndex.tits

@[expose] def I141RankFamily (F : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (L A : Subgroup Γ),
    catalogIs (PSimple p L) F → IsElemAbelian p A → S10.InnDiagOn p A L →
    p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p L) ≤ Nat.card A → False

@[expose] def I141RankG2Char2 : Prop := I141RankFamily rsG2Char2

@[expose] def I141RankG2Odd : Prop := I141RankFamily rsG2Odd

@[expose] def I141RankU3 : Prop := I141RankFamily rsU3

@[expose] def I141RankA5 : Prop := I141RankFamily (rsAlt 5)

@[expose] def I141RankA6 : Prop := I141RankFamily (rsAlt 6)

@[expose] def I141RankA8 : Prop := I141RankFamily (rsAlt 8)

@[expose] def I141RankL27 : Prop := I141RankFamily rsL27

@[expose] def I141RankTits : Prop := I141RankFamily rsTits

theorem isRankSmall_families {i : TauCeti.CFSGIndex} (h : isRankSmall i) :
    rsG2Char2 i ∨ rsG2Odd i ∨ rsU3 i ∨ rsAlt 5 i ∨ rsAlt 6 i ∨ rsAlt 8 i ∨ rsL27 i ∨ rsTits i := by
  cases i with
  | cyclic p hp => simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
  | sporadic s => simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
  | alternating n hn =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by
      simpa [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] using h
    rcases hn' with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | lie d =>
    obtain ⟨t, ht⟩ := d
    cases t with
    | G2 q =>
      by_cases hq : q.p = 2
      · exact Or.inl hq
      · exact Or.inr (Or.inl (by simpa [rsG2Odd, onLie] using hq))
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
      · simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
      · have hq : q.p ^ q.exponent = 3 := by
          simpa [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] using h
        exact Or.inr (Or.inr (Or.inl (by
          show q.card = 3
          rw [TauCeti.PrimePower.card_def]; exact hq)))
      · simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
      · simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
    | A r q =>
      rcases r with _ | _ | r
      · simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
      · have hq : q.p ^ q.exponent = 7 := by
          simpa [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] using h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
          show q.card = 7
          rw [TauCeti.PrimePower.card_def]; exact hq)))))))
      · simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h
    | tits =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [rsTits, onLie])))))))
    | _ => simp [isRankSmall, S10.isG2Quot, ambiguousChev, onLie] at h

theorem i141RankSmall_of_families (hG2 : I141RankG2Char2) (hG2o : I141RankG2Odd) (hU3 : I141RankU3)
    (hA5 : I141RankA5) (hA6 : I141RankA6) (hA8 : I141RankA8) (hL27 : I141RankL27) (hT : I141RankTits) :
    I141RankSmall := by
  intro p hp hp2 Γ _ _ L A hL hA hInn hcard
  obtain ⟨i, hi, e⟩ := hL
  rcases isRankSmall_families hi with h | h | h | h | h | h | h | h
  · exact hG2 p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard
  · exact hG2o p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard
  · exact hU3 p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard
  · exact hA5 p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard
  · exact hA6 p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard
  · exact hA8 p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard
  · exact hL27 p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard
  · exact hT p hp hp2 Γ L A ⟨i, h, e⟩ hA hInn hcard

end CFSG.LocalAnalysis.GLTheoremA.I141F
