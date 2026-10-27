module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MainFact
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Red
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I171Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped commutatorElement

structure T158Hyp {X : Type} [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X)
    (L₁ L₂ : Subgroup X) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  hyp : I158HypK p (⊤ : Subgroup X) K B x₁ x₂ L₁ L₂
  layer : GLAPLayer p (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) ≠ ⊥

@[expose] def T158Concl15 {X : Type} [Group X] (p : ℕ) (K B : Subgroup X) (x₂ : X) (L₁ : Subgroup X) : Prop :=
  p = 3 ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧
    ((catalogIs (PSimple 3 K) (S10.isU6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isL2n (3 * n)) ∧
        (∃ M : Subgroup X, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) M ∧
          catalogIs (PSimple 3 M) (S10.isL2n n)) ∧
        Nat.card B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) ∨
      (catalogIs (PSimple 3 K) (S10.isTE6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isU3n (3 * n)) ∧
        (∃ M : Subgroup X, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) M ∧
          catalogIs (PSimple 3 M) (S10.isU3n n)) ∧
        Nat.card B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K)))

@[expose] def T158MainShape : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    T158Hyp p K B x₁ x₂ L₁ L₂ → T158Concl15 p K B x₂ L₁

@[expose] def T158MainTail : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    T158Hyp p K B x₁ x₂ L₁ L₂ → T158Concl15 p K B x₂ L₁ →
      ∀ T : Subgroup X, T ≤ (⊤ : Subgroup X) → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set X) →
        (⁅T, B⁆ : Subgroup X) = ⊥

theorem t158MainFact_iff : T158MainFact ↔ T158MainShape ∧ T158MainTail := by
  constructor
  · intro h
    refine ⟨fun X _ _ p K B x₁ x₂ L₁ L₂ hh => ?_, fun X _ _ p K B x₁ x₂ L₁ L₂ hh _ => ?_⟩
    · obtain ⟨hp3, n, hodd, hn1, hD, -⟩ :=
        h X p hh.prime hh.odd K B x₁ x₂ L₁ L₂ hh.hyp hh.layer
      exact ⟨hp3, n, hodd, hn1, hD⟩
    · obtain ⟨-, n, -, -, -, hT⟩ := h X p hh.prime hh.odd K B x₁ x₂ L₁ L₂ hh.hyp hh.layer
      exact hT
  · rintro ⟨hS, hT⟩ X _ _ p hp hp2 K B x₁ x₂ L₁ L₂ hh hl
    have hH : T158Hyp p K B x₁ x₂ L₁ L₂ := ⟨hp, hp2, hh, hl⟩
    obtain ⟨hp3, n, hodd, hn1, hD⟩ := hS X p K B x₁ x₂ L₁ L₂ hH
    exact ⟨hp3, n, hodd, hn1, hD, hT X p K B x₁ x₂ L₁ L₂ hH ⟨hp3, n, hodd, hn1, hD⟩⟩

@[expose] def t158FamCyc : TauCeti.CFSGIndex → Prop :=
  fun | .cyclic _ _ => True | _ => False

@[expose] def t158FamAlt : TauCeti.CFSGIndex → Prop :=
  fun | .alternating _ _ => True | _ => False

@[expose] def t158FamSpor : TauCeti.CFSGIndex → Prop :=
  fun | .sporadic _ => True | _ => False

@[expose] def t158FamOdd : TauCeti.CFSGIndex → Prop :=
  onLie fun d => d.characteristic ≠ 2

@[expose] def t158FamTwo : TauCeti.CFSGIndex → Prop :=
  onLie fun d => d.characteristic = 2

theorem t158_cover_nonchev (i : TauCeti.CFSGIndex) (h : ¬ l154Chev2 i) :
    t158FamCyc i ∨ t158FamAlt i ∨ t158FamSpor i ∨ t158FamOdd i := by
  cases i with
  | cyclic p hp => exact Or.inl trivial
  | alternating n hn => exact Or.inr (Or.inl trivial)
  | sporadic s => exact Or.inr (Or.inr (Or.inl trivial))
  | lie d =>
    refine Or.inr (Or.inr (Or.inr ?_))
    intro hc
    exact h (Or.inl (by simpa [onLie] using hc))

theorem t158_ambU33_odd {i : TauCeti.CFSGIndex} (h : l154AmbU33 i) : t158FamOdd i := by
  cases i with
  | cyclic _ _ => exact h.elim
  | alternating _ _ => exact h.elim
  | sporadic _ => exact h.elim
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact h.elim
      · exact h.elim
      · have h3 : q.card = 3 := h
        have hcard : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact h3
        have hp3 : q.p ∣ 3 := by rw [← hcard]; exact dvd_pow_self q.p q.exponent_pos.ne'
        have : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hp3
        simp [t158FamOdd, onLie, this]
      · exact h.elim
    | _ => exact h.elim

theorem t158_ambLie_odd {d : TauCeti.ValidLieTypeIndex} (h : ambiguousChev 2 (.lie d)) :
    t158FamOdd (.lie d) := by
  obtain ⟨d0, hv⟩ := d
  cases d0 with
  | A r q =>
    rcases r with _ | _ | r
    · simp [ambiguousChev] at h
    · have h7 : q.card = 7 := by
        rcases (show (q.card = 7 ∧ 2 = 2) ∨ (q.card = 8 ∧ 2 = 3) by simpa [ambiguousChev] using h) with h' | h'
        · exact h'.1
        · omega
      have hcard : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact h7
      have hp7 : q.p ∣ 7 := by rw [← hcard]; exact dvd_pow_self q.p q.exponent_pos.ne'
      have : q.p = 7 := (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 hp7
      simp [t158FamOdd, onLie, this]
    · simp [ambiguousChev] at h
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · simp [ambiguousChev] at h
    · simp [ambiguousChev] at h
    · exact t158_ambU33_odd (by simpa [l154AmbU33, onLie, ambiguousChev] using h)
    · simp [ambiguousChev] at h
    · simp [ambiguousChev] at h
  | _ => simp [ambiguousChev] at h

theorem t158_cover_chev {i : TauCeti.CFSGIndex} (h : l154Chev2 i) :
    t158FamAlt i ∨ t158FamOdd i ∨ t158FamTwo i := by
  rcases h with h | h
  · exact Or.inr (Or.inr h)
  · cases i with
    | cyclic _ _ => simp [ambiguousChev] at h
    | sporadic _ => simp [ambiguousChev] at h
    | alternating n hn => exact Or.inl trivial
    | lie d => exact Or.inr (Or.inl (t158_ambLie_odd h))

@[expose] def t158ShapeA (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A n q => q.p = 2 ∧ p ∣ Nat.gcd (n + 1) (q.card - 1) | _ => False

@[expose] def t158ShapeTwA (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA n q => q.p = 2 ∧ p ∣ Nat.gcd (n + 1) (q.card + 1) | _ => False

@[expose] def t158ShapeE6 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E6 q => p = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1 | _ => False

@[expose] def t158ShapeTwE6 (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedE6 q => p = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1 | _ => False

theorem t158_shape_cover {p : ℕ} {j : TauCeti.CFSGIndex} (h : onLie (I171.I171LieShape p) j) :
    t158ShapeA p j ∨ t158ShapeTwA p j ∨ t158ShapeE6 p j ∨ t158ShapeTwE6 p j := by
  cases j with
  | cyclic _ _ => exact h.elim
  | alternating _ _ => exact h.elim
  | sporadic _ => exact h.elim
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | A n q => exact Or.inl h
    | twistedA n q => exact Or.inr (Or.inl h)
    | E6 q => exact Or.inr (Or.inr (Or.inl h))
    | twistedE6 q => exact Or.inr (Or.inr (Or.inr h))
    | _ => exact h.elim

@[expose] def T158FalseOn (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → T158Hyp p K B x₁ x₂ L₁ L₂ → False

@[expose] def T158NoOn (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → ¬ IsChevSimple 2 (PSimple p K) → T158Hyp p K B x₁ x₂ L₁ L₂ → False

theorem t158NoOn_of_falseOn {Q : TauCeti.CFSGIndex → Prop} (h : T158FalseOn Q) : T158NoOn Q :=
  fun X _ _ p K B x₁ x₂ L₁ L₂ hQ _ hh => h X p K B x₁ x₂ L₁ L₂ hQ hh

@[expose] def T158InnOn (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → p.Prime → p ≠ 2 → I158HypK p (⊤ : Subgroup X) K B x₁ x₂ L₁ L₂ →
      InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K

@[expose] def T158Shape15 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) t158FamTwo → T158Hyp p K B x₁ x₂ L₁ L₂ →
      InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K → I171.I171LieShapeAt p K

@[expose] def T158ShapeLieOn (Q : ℕ → TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) (Q p) → T158Hyp p K B x₁ x₂ L₁ L₂ →
      InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K → T158Concl15 p K B x₂ L₁

@[expose] def T158TailOn (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → T158Hyp p K B x₁ x₂ L₁ L₂ → T158Concl15 p K B x₂ L₁ →
      ∀ T : Subgroup X, T ≤ (⊤ : Subgroup X) → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set X) →
        (⁅T, B⁆ : Subgroup X) = ⊥

theorem t158FalseOn_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i) (h : T158FalseOn Q') :
    T158FalseOn Q := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh
  obtain ⟨i, hi, e⟩ := hQ
  exact h X p K B x₁ x₂ L₁ L₂ ⟨i, hsub i hi, e⟩ hh

theorem t158FalseOn_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : T158FalseOn Q₁) (h₂ : T158FalseOn Q₂) :
    T158FalseOn (fun i => Q₁ i ∨ Q₂ i) := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh
  · exact h₂ X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh

theorem t158InnOn_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i) (h : T158InnOn Q') :
    T158InnOn Q := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hp hp2 hh
  obtain ⟨i, hi, e⟩ := hQ
  exact h X p K B x₁ x₂ L₁ L₂ ⟨i, hsub i hi, e⟩ hp hp2 hh

theorem t158InnOn_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : T158InnOn Q₁) (h₂ : T158InnOn Q₂) :
    T158InnOn (fun i => Q₁ i ∨ Q₂ i) := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hp hp2 hh
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hp hp2 hh
  · exact h₂ X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hp hp2 hh

theorem t158TailOn_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : T158TailOn Q₁) (h₂ : T158TailOn Q₂) :
    T158TailOn (fun i => Q₁ i ∨ Q₂ i) := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh hc
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh hc
  · exact h₂ X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh hc

theorem t158_catalogue {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} {x₁ x₂ : X}
    {L₁ L₂ : Subgroup X} (h : T158Hyp p K B x₁ x₂ L₁ L₂) : IsCatalogGroup (PSimple p K) := by
  obtain ⟨⟨hKG, hK, -⟩, -⟩ := h.hyp
  exact CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient'
    ((hKG.of_le hK.1).quotient _) (isQuasisimple_pQuot_of_glaPComponent h.prime hK)

@[expose] def T158ShapeChev : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    IsChevSimple 2 (PSimple p K) → T158Hyp p K B x₁ x₂ L₁ L₂ → T158Concl15 p K B x₂ L₁

@[expose] def T158ShapeNonChev : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    ¬ IsChevSimple 2 (PSimple p K) → T158Hyp p K B x₁ x₂ L₁ L₂ → False

theorem t158MainShape_of_chev_nonchev (h1 : T158ShapeChev) (h2 : T158ShapeNonChev) : T158MainShape := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hh
  by_cases hc : IsChevSimple 2 (PSimple p K)
  · exact h1 X p K B x₁ x₂ L₁ L₂ hc hh
  · exact (h2 X p K B x₁ x₂ L₁ L₂ hc hh).elim

theorem t158ShapeNonChev_of_families (hCyc : T158FalseOn t158FamCyc) (hAlt : T158FalseOn t158FamAlt)
    (hSpor : T158NoOn t158FamSpor) (hOdd : T158FalseOn t158FamOdd) : T158ShapeNonChev := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hc hh
  obtain ⟨i, e⟩ := t158_catalogue hh
  have hi : ¬ l154Chev2 i := fun hi => by
    rcases hi with h | h
    · exact hc (Or.inl ⟨i, h, e⟩)
    · exact hc (Or.inr ⟨i, h, e⟩)
  rcases t158_cover_nonchev i hi with h | h | h | h
  · exact hCyc X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh
  · exact hAlt X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh
  · exact hSpor X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hc hh
  · exact hOdd X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh

theorem t158ShapeChev_of (hAlt : T158FalseOn t158FamAlt) (hOdd : T158FalseOn t158FamOdd)
    (hInn : T158InnOn t158FamTwo) (h15 : T158Shape15) (hA : T158ShapeLieOn t158ShapeA)
    (hTwA : T158ShapeLieOn t158ShapeTwA) (hE6 : T158ShapeLieOn t158ShapeE6)
    (hTwE6 : T158ShapeLieOn t158ShapeTwE6) : T158ShapeChev := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hc hh
  obtain ⟨i, hi, e⟩ := catalogIs_l154Chev2 hc
  rcases t158_cover_chev hi with h | h | h
  · exact (hAlt X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh).elim
  · exact (hOdd X p K B x₁ x₂ L₁ L₂ ⟨i, h, e⟩ hh).elim
  · have hTwo : catalogIs (PSimple p K) t158FamTwo := ⟨i, h, e⟩
    have hE : InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K :=
      hInn X p K B x₁ x₂ L₁ L₂ hTwo hh.prime hh.odd hh.hyp
    obtain ⟨j, hj, f⟩ := h15 X p K B x₁ x₂ L₁ L₂ hTwo hh hE
    rcases t158_shape_cover hj with h' | h' | h' | h'
    · exact hA X p K B x₁ x₂ L₁ L₂ ⟨j, h', f⟩ hh hE
    · exact hTwA X p K B x₁ x₂ L₁ L₂ ⟨j, h', f⟩ hh hE
    · exact hE6 X p K B x₁ x₂ L₁ L₂ ⟨j, h', f⟩ hh hE
    · exact hTwE6 X p K B x₁ x₂ L₁ L₂ ⟨j, h', f⟩ hh hE

@[expose] def t158FamU6 : TauCeti.CFSGIndex → Prop := fun i => ∃ n : ℕ, S10.isU6n n i

@[expose] def t158FamTE6 : TauCeti.CFSGIndex → Prop := fun i => ∃ n : ℕ, S10.isTE6n n i

theorem t158MainTail_of_two (hU : T158TailOn t158FamU6) (hE : T158TailOn t158FamTE6) : T158MainTail := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hh hc T hT hT2 hBT
  have hc0 := hc
  obtain ⟨hp3, n, hodd, hn1, hD⟩ := hc
  subst hp3
  rcases hD with ⟨hK, -⟩ | ⟨hK, -⟩
  · obtain ⟨i, hi, e⟩ := hK
    exact hU X 3 K B x₁ x₂ L₁ L₂ ⟨i, ⟨n, hi⟩, e⟩ hh hc0 T hT hT2 hBT
  · obtain ⟨i, hi, e⟩ := hK
    exact hE X 3 K B x₁ x₂ L₁ L₂ ⟨i, ⟨n, hi⟩, e⟩ hh hc0 T hT hT2 hBT

theorem t158MainFact_of_shape_tail (hS : T158MainShape) (hT : T158MainTail) : T158MainFact :=
  t158MainFact_iff.2 ⟨hS, hT⟩

theorem t158MainFact_of_gaps (hCyc : T158FalseOn t158FamCyc) (hAlt : T158FalseOn t158FamAlt)
    (hSpor : T158NoOn t158FamSpor) (hOdd : T158FalseOn t158FamOdd) (hInn : T158InnOn t158FamTwo)
    (h15 : T158Shape15) (hA : T158ShapeLieOn t158ShapeA) (hTwA : T158ShapeLieOn t158ShapeTwA)
    (hE6 : T158ShapeLieOn t158ShapeE6) (hTwE6 : T158ShapeLieOn t158ShapeTwE6)
    (hU6 : T158TailOn t158FamU6) (hTE6 : T158TailOn t158FamTE6) : T158MainFact :=
  t158MainFact_of_shape_tail
    (t158MainShape_of_chev_nonchev (t158ShapeChev_of hAlt hOdd hInn h15 hA hTwA hE6 hTwE6)
      (t158ShapeNonChev_of_families hCyc hAlt hSpor hOdd))
    (t158MainTail_of_two hU6 hTE6)

end CFSG.LocalAnalysis.GLTheoremA.T158

end
