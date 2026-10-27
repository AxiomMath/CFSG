module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Up34Chev2Good (d : TauCeti.LieTypeIndex) : Prop :=
  IsL364Index d ∨ Is3D44Index d ∨ IsD44Index d

@[expose] def Up34Chev2At (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, Up34Pumpup S α → Up34Chev2Good d.1

theorem Up34Chev2At.union {F G : TauCeti.LieTypeIndex → Prop} (hF : Up34Chev2At F)
    (hG : Up34Chev2At G) : Up34Chev2At (fun d => F d ∨ G d) :=
  fun S _ _ hs hnab d hd hc he α hα => by
    rcases hd with h | h
    · exact hF S hs hnab d h hc he α hα
    · exact hG S hs hnab d h hc he α hα

theorem up34Chev2Leaf_of_cover {F : TauCeti.LieTypeIndex → Prop}
    (hcov : ∀ d : TauCeti.ValidLieTypeIndex, IsCharTwoLieIndex d.1 → F d.1)
    (h : Up34Chev2At F) : Up34Chev2Leaf := by
  intro S _ _ hs hnab ⟨d, hd, he⟩ α hα
  rcases h S hs hnab d (hcov d hd) hd he α hα with h1 | h2 | h3
  · exact Or.inl ⟨d, h1, he⟩
  · exact Or.inr (Or.inl ⟨d, h2, he⟩)
  · exact Or.inr (Or.inr ⟨d, h3, he⟩)

@[expose] def Up34Chev2Inn (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ x : S, ¬ Up34Pumpup S (MulAut.conj x)

@[expose] def Up34Chev2Out (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∉ (MulAut.conj : S →* MulAut S).range → Up34Pumpup S α →
        Up34Chev2Good d.1

theorem Up34Chev2At.of_inn_out {F : TauCeti.LieTypeIndex → Prop} (hI : Up34Chev2Inn F)
    (hO : Up34Chev2Out F) : Up34Chev2At F := by
  intro S _ _ hs hnab d hd hc he α hα
  by_cases hin : α ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨x, rfl⟩ := hin
    exact absurd hα (hI S hs hnab d hd hc he x)
  · exact hO S hs hnab d hd hc he α hin hα

@[expose] def FamA1 : TauCeti.LieTypeIndex → Prop
  | .A r _ => r = 1
  | _ => False

@[expose] def FamA2 : TauCeti.LieTypeIndex → Prop
  | .A r _ => r = 2
  | _ => False

@[expose] def FamAHigh : TauCeti.LieTypeIndex → Prop
  | .A r _ => 3 ≤ r
  | _ => False

@[expose] def FamTwA2 : TauCeti.LieTypeIndex → Prop
  | .twistedA r _ => r = 2
  | _ => False

@[expose] def FamTwAHigh : TauCeti.LieTypeIndex → Prop
  | .twistedA r _ => 3 ≤ r
  | _ => False

@[expose] def FamB : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | _ => False

@[expose] def FamD4 : TauCeti.LieTypeIndex → Prop
  | .D r _ => r = 4
  | _ => False

@[expose] def FamDHigh : TauCeti.LieTypeIndex → Prop
  | .D r _ => 5 ≤ r
  | _ => False

@[expose] def FamTwD : TauCeti.LieTypeIndex → Prop
  | .twistedD _ _ => True
  | _ => False

@[expose] def FamE6 : TauCeti.LieTypeIndex → Prop
  | .E6 _ => True
  | _ => False

@[expose] def FamTwE6 : TauCeti.LieTypeIndex → Prop
  | .twistedE6 _ => True
  | _ => False

@[expose] def FamE7 : TauCeti.LieTypeIndex → Prop
  | .E7 _ => True
  | _ => False

@[expose] def FamE8 : TauCeti.LieTypeIndex → Prop
  | .E8 _ => True
  | _ => False

@[expose] def FamF4 : TauCeti.LieTypeIndex → Prop
  | .F4 _ => True
  | _ => False

@[expose] def FamG2 : TauCeti.LieTypeIndex → Prop
  | .G2 _ => True
  | _ => False

@[expose] def FamTriD4 : TauCeti.LieTypeIndex → Prop
  | .trialityD4 _ => True
  | _ => False

@[expose] def FamSz : TauCeti.LieTypeIndex → Prop
  | .suzuki _ => True
  | _ => False

@[expose] def FamReeF4 : TauCeti.LieTypeIndex → Prop
  | .reeF4 _ => True
  | _ => False

@[expose] def FamTits : TauCeti.LieTypeIndex → Prop
  | .tits => True
  | _ => False

theorem famCover (d : TauCeti.ValidLieTypeIndex) (hc : IsCharTwoLieIndex d.1) :
    FamA1 d.1 ∨ FamA2 d.1 ∨ FamAHigh d.1 ∨ FamTwA2 d.1 ∨ FamTwAHigh d.1 ∨ FamB d.1 ∨ FamD4 d.1 ∨
      FamDHigh d.1 ∨ FamTwD d.1 ∨ FamE6 d.1 ∨ FamTwE6 d.1 ∨ FamE7 d.1 ∨ FamE8 d.1 ∨ FamF4 d.1 ∨
      FamG2 d.1 ∨ FamTriD4 d.1 ∨ FamSz d.1 ∨ FamReeF4 d.1 ∨ FamTits d.1 := by
  obtain ⟨d, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    have h1 : 1 ≤ r := hr.1
    simp only [FamA1, FamA2, FamAHigh]
    omega
  | twistedA r q =>
    have h2 : 2 ≤ r := hr.1
    simp only [FamTwA2, FamTwAHigh]
    omega
  | B r q => simp [FamB]
  | C r q =>
    exfalso
    exact hr.2 hc
  | D r q =>
    have h4 : 4 ≤ r := hr
    simp only [FamD4, FamDHigh]
    omega
  | twistedD r q => simp [FamTwD]
  | E6 q => simp [FamE6]
  | E7 q => simp [FamE7]
  | E8 q => simp [FamE8]
  | F4 q => simp [FamF4]
  | G2 q => simp [FamG2]
  | twistedE6 q => simp [FamTwE6]
  | trialityD4 q => simp [FamTriD4]
  | suzuki m => simp [FamSz]
  | reeG2 m => exact absurd hc (by simp [IsCharTwoLieIndex])
  | reeF4 m => simp [FamReeF4]
  | tits => simp [FamTits]

end CFSG.HardMathSupport.Dickson.Sec6
