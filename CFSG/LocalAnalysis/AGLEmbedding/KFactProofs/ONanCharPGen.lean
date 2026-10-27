module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenExc

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem exists_family_of_odd {d : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp2 : p ≠ 2)
    (hchar : p = d.1.characteristic) (hrank : ¬ IsRankOneLieIndex d.1) :
    IsSLIndex d ∨ IsSpIndex d ∨ IsSUIndex d ∨ IsBOddIndex d ∨ IsDIndex d ∨
      IsTwistedDIndex d ∨ IsExceptionalIndex d := by
  obtain ⟨d, hv⟩ := d
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hv'
  have hE : IsExceptionalIndex ⟨d, hv⟩ → IsSLIndex ⟨d, hv⟩ ∨ IsSpIndex ⟨d, hv⟩ ∨
      IsSUIndex ⟨d, hv⟩ ∨ IsBOddIndex ⟨d, hv⟩ ∨ IsDIndex ⟨d, hv⟩ ∨
      IsTwistedDIndex ⟨d, hv⟩ ∨ IsExceptionalIndex ⟨d, hv⟩ :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  cases d with
  | A r q =>
    have h1 : 1 ≤ r := hv'.1.1
    have h2 : r ≠ 1 := fun h => hrank (Or.inl ⟨q, by subst h; rfl⟩)
    exact Or.inl ⟨r, q, by omega, rfl⟩
  | twistedA r q =>
    have h1 : 2 ≤ r := hv'.1.1
    have h2 : r ≠ 2 := fun h => hrank (Or.inr (Or.inl ⟨q, by subst h; rfl⟩))
    exact Or.inr (Or.inr (Or.inl ⟨r, q, by omega, rfl⟩))
  | B r q =>
    have h1 : 2 ≤ r := hv'.1.1
    by_cases h2 : r = 2
    · subst h2
      exact Or.inr (Or.inl (Or.inl ⟨q, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, by omega, rfl⟩)))
  | C r q => exact Or.inr (Or.inl (Or.inr ⟨r, q, hv'.1.1, rfl⟩))
  | D r q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))))
  | twistedD r q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩)))))
  | G2 q => exact hE (Or.inl ⟨q, rfl⟩)
  | F4 q => exact hE (Or.inr (Or.inl ⟨q, rfl⟩))
  | E6 q => exact hE (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))
  | E7 q => exact hE (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))
  | E8 q => exact hE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))
  | twistedE6 q => exact hE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))
  | trialityD4 q => exact hE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩))))))
  | suzuki m => exact absurd (by simpa using hchar) hp2
  | reeG2 m => exact absurd (Or.inr (Or.inr ⟨m, rfl⟩)) hrank
  | reeF4 m => exact absurd (by simpa using hchar) hp2
  | tits => exact absurd (by simpa using hchar) hp2

theorem charPGen_of_exceptional (hexc : CharPGenAt IsExceptionalIndex) : CharPGen :=
  charPGen_of_charPGenAt
    (charPGenAt_or charPGenAt_sl (charPGenAt_or charPGenAt_sp (charPGenAt_or charPGenAt_su
      (charPGenAt_or charPGenAt_bOdd (charPGenAt_or charPGenAt_d
        (charPGenAt_or charPGenAt_twistedD hexc))))))
    fun _ _ _ hp2 hchar hrank => exists_family_of_odd hp2 hchar hrank

section Certified


theorem charPGen : CharPGen := charPGen_of_exceptional charPGenAt_exceptional

end Certified

end CFSG.AGLEmbedding
