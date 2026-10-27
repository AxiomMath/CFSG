module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Interface
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.LieType.BorelTits.AllModels
public import CFSG.Models.Transport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b TauCeti

theorem isChevIndexOfChar_odd {q : ℕ} (hq2 : q ≠ 2) (d : TauCeti.LieTypeIndex)
    (h : IsChevIndexOfChar q d) :
    lieIndexChar d = q ∨ (q = 3 ∧ ∃ r : TauCeti.PrimePower, d = .A 1 r ∧ r.card = 8) := by
  cases d with
  | A rk r =>
    rcases rk with _ | _ | rk
    · left; simpa [IsChevIndexOfChar, lieIndexChar] using h
    · simp only [IsChevIndexOfChar] at h
      rcases h with h | ⟨h, -⟩ | ⟨h3, h8⟩
      · left; simpa [lieIndexChar] using h
      · exact absurd h hq2
      · exact Or.inr ⟨h3, r, rfl, h8⟩
    · left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | twistedA rk r =>
    rcases rk with _ | _ | _ | rk
    · left; simpa [IsChevIndexOfChar, lieIndexChar] using h
    · left; simpa [IsChevIndexOfChar, lieIndexChar] using h
    · simp only [IsChevIndexOfChar] at h
      rcases h with h | ⟨h, -⟩
      · left; simpa [lieIndexChar] using h
      · exact absurd h hq2
    · left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | B rk r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | C rk r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | D rk r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | twistedD rk r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | E6 r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | E7 r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | E8 r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | F4 r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | G2 r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | twistedE6 r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | trialityD4 r => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | suzuki m => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | reeG2 m => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | reeF4 m => left; simpa [IsChevIndexOfChar, lieIndexChar] using h
  | tits => left; simpa [IsChevIndexOfChar, lieIndexChar] using h

theorem lieIndexChar_eq_characteristic (d : TauCeti.LieTypeIndex) :
    lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]

structure OddFamiliesFor (q : ℕ) (Rig : ∀ (S : Type) [Group S], Prop) : Prop where
  classical : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (n f : ℕ),
      t ∈ classicalTags → StatedClassicalModel S t n q f → Holds S q → Rig S
  exceptional : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (f : ℕ),
      t ∈ chevalleyExceptionalTags → ChevalleyExceptionalModel S t q f → Holds S q → Rig S
  ree : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ f : ℕ, ReeTitsModel S .twistedG2 q f → Holds S q → Rig S
  psl28 : q = 3 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    StatedClassicalModel S .PSL 2 2 3 → Rig S ∧ Holds S 3

set_option linter.unusedSectionVars false

section Dispatch


theorem rig_of_isChevOfChar_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Rig : ∀ (S : Type) [Group S], Prop} (F : OddFamiliesFor q Rig) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (h : IsChevOfChar q S) :
    Rig S ∧ HoldsTits S q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  rcases isChevIndexOfChar_odd hq2 d hd with hch | ⟨hq3, r, rfl, hr8⟩
  · obtain ⟨t, n, p, f, hp, hm⟩ := ChevQ.exists_lieModel_char ⟨d, hv⟩
    have hpq : p = q := by
      rw [hp, ← lieIndexChar_eq_characteristic]
      exact hch
    subst hpq
    have hmS : CFSG.Models.LieModel S t n p f := CFSG.Models.LieModel.of_mulEquiv e.symm hm
    have hbm : CFSG.Blueprint.LieModel S t n p f := blueprintLieModel_of_models hmS
    have hadm := hbm.admissible
    have htT : t ≠ .Tits := by
      rintro rfl
      exact hq2 hadm.2.2.2.1
    have hH : Holds S p := holds_of_lieModel hbm htT
    have hT := hH.holdsTits
    rcases hbm with ⟨htc, hcl⟩ | ⟨-, hte, hce⟩ | ⟨-, htr, hree⟩ | ⟨-, rfl, hsz⟩
    · exact ⟨F.classical S hs hna t n f htc hcl hH, hT⟩
    · exact ⟨F.exceptional S hs hna t f hte hce hH, hT⟩
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at htr
      rcases htr with rfl | rfl | rfl
      · exact ⟨F.ree S hs hna f hree hH, hT⟩
      · exact absurd hree.1.2.2.2.1 hq2
      · exact absurd rfl htT
    · exact absurd hsz.1 hq2
  · subst hq3
    have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 1 r hv
    have hmS : CFSG.Models.LieModel S .PSL 2 r.p r.exponent :=
      CFSG.Models.LieModel.of_mulEquiv e.symm hm
    have hcard : r.p ^ r.exponent = 8 := by
      have := TauCeti.PrimePower.card_def r
      omega
    have hp2 : r.p = 2 := by
      have hdvd : r.p ∣ 2 ^ 3 := by
        rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hcard]
        exact dvd_pow_self _ r.exponent_pos.ne'
      exact (Nat.prime_dvd_prime_iff_eq r.prime_p Nat.prime_two).1
        (r.prime_p.dvd_of_dvd_pow hdvd)
    have hf3 : r.exponent = 3 := by
      rw [hp2] at hcard
      exact Nat.pow_right_injective (le_refl 2) (show 2 ^ r.exponent = 2 ^ 3 by rw [hcard])
    rcases hmS.2 with hcl | ⟨h0, -⟩
    · rw [hp2, hf3] at hcl
      obtain ⟨hR, hH⟩ := F.psl28 rfl S hs hna hcl
      exact ⟨hR, hH.holdsTits⟩
    · exact absurd h0 (by norm_num)

theorem lieQConstrained_of_oddFamilies {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (F : OddFamiliesFor q fun S _ => RadRigid q S) : LieQConstrained q := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact lieQConstrained_of_families
    (fun S _ _ hs hna h => (rig_of_isChevOfChar_odd hq hq2 F hs hna h).2)
    (fun S _ _ hs hna h => (rig_of_isChevOfChar_odd hq hq2 F hs hna h).1)

theorem lieQConstrainedInner_of_oddFamilies {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (F : OddFamiliesFor q fun S _ => RadRigidInner q S) : LieQConstrainedInner q := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact lieQConstrainedInner_of_families
    (fun S _ _ hs hna h => (rig_of_isChevOfChar_odd hq hq2 F hs hna h).2)
    (fun S _ _ hs hna h => (rig_of_isChevOfChar_odd hq hq2 F hs hna h).1)

end Dispatch

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
