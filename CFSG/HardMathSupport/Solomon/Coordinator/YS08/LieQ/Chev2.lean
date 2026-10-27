module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Twisted
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Interface
public import CFSG.LieType.ChevTwo.BorelTitsTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.ChevTwo

theorem isChevIndexOfChar_two_cases (d : TauCeti.LieTypeIndex) (h : IsChevIndexOfChar 2 d) :
    IsChevIndexTwo d ∨ (∃ r : TauCeti.PrimePower, d = .A 1 r ∧ r.card = 9) ∨
      (∃ r : TauCeti.PrimePower, d = .twistedA 2 r ∧ r.card = 3) := by
  cases d with
  | A rk r =>
    rcases rk with _ | _ | rk
    · left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
    · simp only [IsChevIndexOfChar] at h
      rcases h with h | ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨r, rfl, h⟩)
      · omega
    · left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | twistedA rk r =>
    rcases rk with _ | _ | _ | rk
    · left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
    · left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
    · simp only [IsChevIndexOfChar] at h
      rcases h with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨r, rfl, h⟩)
    · left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | B rk r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | C rk r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | D rk r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | twistedD rk r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | E6 r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | E7 r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | E8 r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | F4 r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | G2 r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | twistedE6 r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | trialityD4 r => left; simpa [IsChevIndexOfChar, lieIndexChar, IsChevIndexTwo] using h
  | suzuki m => left; simp [IsChevIndexTwo]
  | reeG2 m => simp [IsChevIndexOfChar, lieIndexChar] at h
  | reeF4 m => left; simp [IsChevIndexTwo]
  | tits => left; simp [IsChevIndexTwo]

theorem isChevTwo_of_isChevOfChar_two {S : Type} [Group S] (h : IsChevOfChar 2 S) :
    IsChevTwo S := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  rcases isChevIndexOfChar_two_cases d hd with hch | ⟨r, rfl, hr⟩ | ⟨r, rfl, hr⟩
  · exact Or.inl ⟨⟨d, hv⟩, hch, ⟨e⟩⟩
  · exfalso
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
    exact h1 ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2
      (Or.inl ⟨rfl, Or.inr (Or.inr hr)⟩))
  · exact Or.inr (Or.inr ⟨⟨_, hv⟩, Or.inr ⟨r, hr, rfl⟩, ⟨e⟩⟩)

@[expose] def ClassicalTagTwo (t : StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus

structure TwoFamilies : Prop where
  classical : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ (t : StatedLieTag) (n f : ℕ),
    ClassicalTagTwo t → StatedClassicalModel S t n 2 f → HoldsTits S 2 → RadRigid 2 S
  suzuki : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ (f : ℕ), SuzukiModel S 2 f →
    HoldsTits S 2 → RadRigid 2 S
  ree : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ (t : StatedLieTag) (f : ℕ),
    (t = .twistedF4 ∨ t = .Tits) → ReeTitsModel S t 2 f → HoldsTits S 2 → RadRigid 2 S
  u33 : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → StatedClassicalModel S .PSU 3 3 1 →
    HoldsTits S 2 → RadRigid 2 S

set_option linter.unusedSectionVars false

section Dispatch


theorem radRigid_of_chevalleyExceptionalModel_two {S : Type} [Group S] [Finite S]
    (hBT : HoldsTits S 2) {t : StatedLieTag} {f : ℕ} (h : ChevalleyExceptionalModel S t 2 f) :
    RadRigid 2 S := by
  obtain ⟨hadm, hmodel⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  cases t
  all_goals first
    | exact hmodel.elim
    | exact radRigid_of_untwistedChevalleyModel (by decide) hmodel
    | exact radRigid_of_twistedChevalleyModel hBT hf hmodel

theorem radRigid_of_isChevOfChar_two (F : TwoFamilies) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (h : IsChevOfChar 2 S) :
    RadRigid 2 S := by
  have hBT : HoldsTits S 2 := holdsTits_two_of_isChevTwo hs hna (isChevTwo_of_isChevOfChar_two h)
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  rcases isChevIndexOfChar_two_cases d hd with hch | ⟨r, rfl, hr⟩ | ⟨r, rfl, hr⟩
  · obtain ⟨t, n, f, hL⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid ⟨d, hv⟩
      (characteristic_two_of_isChevIndexTwo hch) e
    rcases hL with ⟨ht, hcl⟩ | ⟨-, -, hce⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
    · have hadm := hcl.1
      have htag : ClassicalTagTwo t := by
        simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact absurd rfl hadm.2.2.2
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      exact F.classical S hs t n f htag hcl hBT
    · exact radRigid_of_chevalleyExceptionalModel_two hBT hce
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact absurd hree.1.2.2.2.1 (by decide)
      · exact F.ree S hs _ f (Or.inl rfl) hree hBT
      · exact F.ree S hs _ f (Or.inr rfl) hree hBT
    · exact F.suzuki S hs f hsz hBT
  · exfalso
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
    exact h1 ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2
      (Or.inl ⟨rfl, Or.inr (Or.inr hr)⟩))
  · exact F.u33 S hs (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two r hv
      hr e) hBT

theorem lieQConstrained_two (F : TwoFamilies) : LieQConstrained 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact lieQConstrained_of_families
    (fun S _ _ hs hna h => holdsTits_two_of_isChevTwo hs hna (isChevTwo_of_isChevOfChar_two h))
    (fun S _ _ hs hna h => radRigid_of_isChevOfChar_two F hs hna h)

end Dispatch

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
