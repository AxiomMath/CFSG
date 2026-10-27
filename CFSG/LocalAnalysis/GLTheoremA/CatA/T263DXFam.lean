module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXSeed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

@[expose] def T263SelWP (Q : ℕ → TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
    ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → catalogIs (↥S ⧸ Subgroup.center ↥S) (Q p) →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ → GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 →
    ∀ B₀ : Subgroup Ω, T263HasB0 p S B B₀ → T263Dich p S B →
    p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀ →
    ∀ T' : Subgroup Ω, T' ≠ ⊥ → IsPGroup 2 T' → T' ≤ S → B ≤ Subgroup.normalizer (T' : Set Ω) →
    B ⊓ Subgroup.centralizer (T' : Set Ω) ≤ Subgroup.centralizer (S : Set Ω) →
    ∀ x : Ω, x ∈ B₀ → x ∉ Subgroup.centralizer (S : Set Ω) →
    (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥ →
    T263GConcl p S B ∨ ∃ J : Subgroup Ω, SelComp p S B₀ T' x J

theorem t263SelW_of_or {Q : TauCeti.CFSGIndex → Prop} {Q₁ Q₂ : ℕ → TauCeti.CFSGIndex → Prop}
    (hcov : ∀ p i, Q i → Q₁ p i ∨ Q₂ p i) (h₁ : T263SelWP Q₁) (h₂ : T263SelWP Q₂) :
    T263SelW Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hcat
  obtain ⟨i, hi, e⟩ := hcat
  rcases hcov p i hi with h | h
  · exact h₁ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩
  · exact h₂ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩

theorem T263SelWP.or {Q₁ Q₂ : ℕ → TauCeti.CFSGIndex → Prop} (h₁ : T263SelWP Q₁)
    (h₂ : T263SelWP Q₂) : T263SelWP fun p i => Q₁ p i ∨ Q₂ p i := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hcat
  obtain ⟨i, hi, e⟩ := hcat
  rcases hi with h | h
  · exact h₁ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩
  · exact h₂ p hp hp2 Ω hK S B hSn hSq hSp hSc ⟨i, h, e⟩

@[expose] def t263GExcEasy (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E7 q | .E8 q | .F4 q | .G2 q => q.p = 2 ∧ 4 ≤ q.card ∧ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GExcGF2 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E7 q | .E8 q | .F4 q | .G2 q => q.card = 2 ∧ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GExcHard (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E7 q | .E8 q | .F4 q | .G2 q => q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GE6Easy (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.p = 2 ∧ 4 ≤ q.card ∧ p ∣ q.card ^ 2 - 1 ∧ ¬ (p = 3 ∧ 3 ∣ q.card - 1)
    | .twistedE6 q => q.p = 2 ∧ 4 ≤ q.card ∧ p ∣ q.card ^ 2 - 1 ∧ ¬ (p = 3 ∧ 3 ∣ q.card + 1)
    | _ => False

@[expose] def t263GE6Shape (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.p = 2 ∧ 4 ≤ q.card ∧ p = 3 ∧ 3 ∣ q.card - 1
    | .twistedE6 q => q.p = 2 ∧ 4 ≤ q.card ∧ p = 3 ∧ 3 ∣ q.card + 1
    | _ => False

@[expose] def t263GE6GF2 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q | .twistedE6 q => q.card = 2 ∧ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GE6Hard (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q | .twistedE6 q => q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GTD4Easy (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .trialityD4 q => q.p = 2 ∧ 4 ≤ q.card ∧ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GTD4GF2 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .trialityD4 q => q.card = 2 ∧ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GTD4Hard (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .trialityD4 q => q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

theorem card_eq_two_or_four_le {q : TauCeti.PrimePower} (h : q.p = 2) : q.card = 2 ∨ 4 ≤ q.card := by
  rw [TauCeti.PrimePower.card_def, h]
  rcases Nat.lt_or_ge q.exponent 2 with he | he
  · left
    rw [show q.exponent = 1 by have := q.exponent_pos; omega, pow_one]
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he

private theorem cover_three {p : ℕ} {q : TauCeti.PrimePower} (h : q.p = 2) :
    ((q.p = 2 ∧ 4 ≤ q.card ∧ p ∣ q.card ^ 2 - 1) ∨ (q.card = 2 ∧ p ∣ q.card ^ 2 - 1)) ∨
      (q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1) := by
  by_cases hd : p ∣ q.card ^ 2 - 1
  · rcases card_eq_two_or_four_le h with h2 | h4
    · exact Or.inl (Or.inr ⟨h2, hd⟩)
    · exact Or.inl (Or.inl ⟨h, h4, hd⟩)
  · exact Or.inr ⟨h, hd⟩

private theorem cover_four {p : ℕ} {q : TauCeti.PrimePower} (h : q.p = 2) (c : ℕ) :
    (((q.p = 2 ∧ 4 ≤ q.card ∧ p ∣ q.card ^ 2 - 1 ∧ ¬ (p = 3 ∧ 3 ∣ c)) ∨
        (q.p = 2 ∧ 4 ≤ q.card ∧ p = 3 ∧ 3 ∣ c)) ∨ (q.card = 2 ∧ p ∣ q.card ^ 2 - 1)) ∨
      (q.p = 2 ∧ ¬ p ∣ q.card ^ 2 - 1) := by
  by_cases hd : p ∣ q.card ^ 2 - 1
  · rcases card_eq_two_or_four_le h with h2 | h4
    · exact Or.inl (Or.inr ⟨h2, hd⟩)
    · by_cases hs : p = 3 ∧ 3 ∣ c
      · exact Or.inl (Or.inl (Or.inr ⟨h, h4, hs⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨h, h4, hd, hs⟩))
  · exact Or.inr ⟨h, hd⟩

theorem t263Desc_exc_of (he : T263SelWP t263GExcEasy) (hg : T263SelWP t263GExcGF2)
    (hh : T263SelWP t263GExcHard) : T263Desc t263GExc := by
  refine t263Desc_of_selW (t263SelW_of_or ?_ (he.or hg) hh)
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GExc, t263GExcEasy, t263GExcGF2, t263GExcHard, onLie] at hi ⊢ <;>
      first | exact hi.elim | exact cover_three hi
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem t263Desc_e6_of (he : T263SelWP t263GE6Easy) (hs : T263SelWP t263GE6Shape)
    (hg : T263SelWP t263GE6GF2) (hh : T263SelWP t263GE6Hard) : T263Desc t263GE6 := by
  refine t263Desc_of_selW (t263SelW_of_or ?_ ((he.or hs).or hg) hh)
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;>
      simp only [t263GE6, t263GE6Easy, t263GE6Shape, t263GE6GF2, t263GE6Hard, onLie] at hi ⊢ <;>
      first | exact hi.elim | exact cover_four hi _
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem t263Desc_td4_of (he : T263SelWP t263GTD4Easy) (hg : T263SelWP t263GTD4GF2)
    (hh : T263SelWP t263GTD4Hard) : T263Desc t263GTD4 := by
  refine t263Desc_of_selW (t263SelW_of_or ?_ (he.or hg) hh)
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GTD4, t263GTD4Easy, t263GTD4GF2, t263GTD4Hard, onLie] at hi ⊢ <;>
      first | exact hi.elim | exact cover_three hi
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
