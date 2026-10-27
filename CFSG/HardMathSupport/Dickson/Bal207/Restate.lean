module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.HardMathSupport.Dickson.I271.Support.Action
public import CFSG.HardMathSupport.Dickson.Bal207.Corr
public import CFSG.HardMathSupport.Dickson.I271.I202Full

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

@[expose] def IsD4EightIdx : TauCeti.LieTypeIndex → Prop
  | .D r q => r = 4 ∧ IsTwoPow q 3
  | _ => False

theorem bal207Index_p {p : ℕ} {d : TauCeti.LieTypeIndex} (h : Bal207Index p d) :
    p = 3 ∨ p = 5 := by
  cases d <;> simp_all [Bal207Index]

theorem bal207Index_g2 {p : ℕ} {d : TauCeti.LieTypeIndex} (h : Bal207Index p d)
    (hg : IsG2EightIndex d) : p = 3 := by
  cases d <;> simp_all [Bal207Index, IsG2EightIndex]

@[expose] def Bal207Cond {X : Type} [Group X] [Finite X] (p : ℕ) (d : TauCeti.LieTypeIndex)
    (B K : Subgroup X) : Prop :=
  IsG2EightIndex d → CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) + 3 ≤
    CFSG.Open.pRank p B

@[expose] def NoTrialityOn (G : ∀ (S : Type) [Group S], MulAut S → Prop) {X : Type} [Group X]
    (B K : Subgroup X) : Prop :=
  ∀ φ ∈ autImage B K, ¬ (φ ^ 3 = 1 ∧ G (↥K ⧸ Subgroup.center ↥K) φ)

@[expose] def Bal207PlusHyp (G : ∀ (S : Type) [Group S], MulAut S → Prop) (p : ℕ) {X : Type}
    [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ((Bal207Index p d.1 ∧ Bal207Cond p d.1 B K) ∨
        (p = 3 ∧ IsD4EightIdx d.1 ∧ NoTrialityOn G B K))

@[expose] def Bal207PlusBody (G : ∀ (S : Type) [Group S], MulAut S → Prop) (X : Type) [Group X]
    [Finite X] : Prop :=
  ∀ (p : ℕ) (K B : Subgroup X), p.Prime → p ≠ 2 → CFSG.Open.IsComponentOf K ⊤ → IsSCp p ⊤ B →
    B ≤ Subgroup.normalizer (K : Set X) → Bal207PlusHyp G p K B → IsStronglyBalancedIn p B K

theorem bal207PlusHyp_p {G : ∀ (S : Type) [Group S], MulAut S → Prop} {p : ℕ} {X : Type}
    [Group X] [Finite X] {K B : Subgroup X} (h : Bal207PlusHyp G p K B) : p = 3 ∨ p = 5 := by
  obtain ⟨d, -, ⟨hi, -⟩ | ⟨hp3, -, -⟩⟩ := h
  · exact bal207Index_p hi
  · exact Or.inl hp3

structure Bal207PlusCtx (G : ∀ (S : Type) [Group S], MulAut S → Prop) (p : ℕ) {X : Type}
    [Group X] [Finite X] (K B A : Subgroup X) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  comp : CFSG.Open.IsComponentOf K ⊤
  scp : IsSCp p ⊤ B
  norm : B ≤ Subgroup.normalizer (K : Set X)
  hyp : Bal207PlusHyp G p K B
  le : A ≤ B
  noncyc : ¬ IsCyclic ↥A
  disj : A ⊓ Subgroup.centralizer (K : Set X) = ⊥
  sup : A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B

@[expose] def Bal207PlusIH (G : ∀ (S : Type) [Group S], MulAut S → Prop) {X : Type} [Group X]
    [Finite X] (A : Subgroup X) : Prop :=
  ∀ a ∈ A, a ≠ 1 → Bal207PlusBody G ↥(Subgroup.centralizer ({a} : Set X))

@[expose] def Bal207PlusDvdD4Eight : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X),
    CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K IsD4EightIdx → 3 ∣ Nat.card ↥K

@[expose] def Bal207PlusLocalBalD4Eight : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K A : Subgroup X),
    CFSG.Open.IsComponentOf K ⊤ → IsLieQuot ↥K IsD4EightIdx →
      A ≤ Subgroup.normalizer (K : Set X) → CFSG.Open.IsElemAbelian 3 A →
        IsCompLocallyBalanced 3 1 A K

@[expose] def Bal207PlusRankD4Eight : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B : Subgroup X),
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      IsLieQuot ↥K IsD4EightIdx →
        ∃ A : Subgroup X, A ≤ B ∧ ¬ IsCyclic ↥A ∧ A ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
          A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B

@[expose] def Bal207PlusFamClauses {X : Type} [Group X] (p : ℕ) (K B A : Subgroup X) : Prop :=
  (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X)) ∧
  (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → ¬ IsBalSmall J →
        IsStronglyLocallyOneBalanced p B a J) ∧
  (∃ a ∈ A, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X), Nat.Coprime p (orderOf w) →
      (∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X))

@[expose] def Bal207PlusFam (G : ∀ (S : Type) [Group S], MulAut S → Prop)
    (F : ℕ → TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B A : Subgroup X),
    Bal207PlusCtx G p K B A → IsLieQuot ↥K (F p) → Bal207PlusIH G A →
      Bal207PlusFamClauses p K B A

@[expose] def Bal207PlusFamSp (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G FamSp

@[expose] def Bal207PlusFamUni (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G FamUni

@[expose] def Bal207PlusFamOrth (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G FamOrth

abbrev FamExcNoG2 (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop := FamExc p d ∧ ¬ IsG2EightIndex d

@[expose] def Bal207PlusFamExc (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G FamExcNoG2

@[expose] def Bal207PlusFamG28 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K IsG2EightIndex →
      CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + 3 ≤ CFSG.Open.pRank 3 B →
        Bal207PlusIH G A → Bal207PlusFamClauses 3 K B A

@[expose] def Bal207PlusFamD4Eight (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K IsD4EightIdx → NoTrialityOn G B K →
      Bal207PlusIH G A → Bal207PlusFamClauses 3 K B A

@[expose] def IsExcU62 : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => r = 5 ∧ IsTwoPow q 1
  | _ => False

@[expose] def IsExc3D42 : TauCeti.LieTypeIndex → Prop
  | .trialityD4 q => IsTwoPow q 1
  | _ => False

@[expose] def IsExcF42 : TauCeti.LieTypeIndex → Prop
  | .F4 q => IsTwoPow q 1
  | _ => False

@[expose] def IsExcTits : TauCeti.LieTypeIndex → Prop
  | .tits => True
  | _ => False

@[expose] def IsExcRee32 : TauCeti.LieTypeIndex → Prop
  | .reeF4 m => m = 2
  | _ => False

@[expose] def IsExcSz32 : TauCeti.LieTypeIndex → Prop
  | .suzuki m => m = 2
  | _ => False

@[expose] def Bal207PlusFamU62 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G (fun p d => p = 3 ∧ IsExcU62 d)

@[expose] def Bal207PlusFam3D42 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G (fun p d => p = 3 ∧ IsExc3D42 d)

@[expose] def Bal207PlusFamF42 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G (fun p d => p = 3 ∧ IsExcF42 d)

@[expose] def Bal207PlusFamTitsThree (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G (fun p d => p = 3 ∧ IsExcTits d)

@[expose] def Bal207PlusFamTitsFive (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G (fun p d => p = 5 ∧ IsExcTits d)

@[expose] def Bal207PlusFamRee32 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G (fun p d => p = 5 ∧ IsExcRee32 d)

@[expose] def Bal207PlusFamSz32 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusFam G (fun p d => p = 5 ∧ IsExcSz32 d)

theorem famExcNoG2_cases {p : ℕ} {d : TauCeti.LieTypeIndex} (h : FamExcNoG2 p d) :
    (p = 3 ∧ IsExcU62 d) ∨ (p = 3 ∧ IsExc3D42 d) ∨ (p = 3 ∧ IsExcF42 d) ∨
      (p = 3 ∧ IsExcTits d) ∨ (p = 5 ∧ IsExcTits d) ∨ (p = 5 ∧ IsExcRee32 d) ∨
        (p = 5 ∧ IsExcSz32 d) := by
  obtain ⟨⟨hi, hs, hu, ho⟩, hg⟩ := h
  cases d with
  | B r q => exact absurd trivial hs
  | twistedA r q =>
    obtain ⟨hp, h1 | h1⟩ := hi
    · exact absurd (show IsUniIdx (.twistedA r q) from ⟨h1.2, h1.1⟩) hu
    · exact Or.inl ⟨hp, h1.2, h1.1⟩
  | D r q => exact absurd trivial ho
  | twistedD r q => exact absurd trivial ho
  | trialityD4 q =>
    obtain ⟨hp, h1⟩ := hi
    exact Or.inr (Or.inl ⟨hp, h1⟩)
  | G2 q => exact absurd (show IsG2EightIndex (.G2 q) from hi.2) hg
  | F4 q =>
    obtain ⟨hp, h1⟩ := hi
    exact Or.inr (Or.inr (Or.inl ⟨hp, h1⟩))
  | tits =>
    rcases hi with hp | hp
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, trivial⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, trivial⟩))))
  | suzuki m =>
    obtain ⟨hp, h1⟩ := hi
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, h1⟩)))))
  | reeF4 m =>
    obtain ⟨hp, h1⟩ := hi
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, h1⟩)))))
  | _ => exact absurd hi (by simp [Bal207Index])

theorem bal207PlusFamExc_of_parts {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    (h1 : Bal207PlusFamU62 G) (h2 : Bal207PlusFam3D42 G) (h3 : Bal207PlusFamF42 G)
    (h4 : Bal207PlusFamTitsThree G) (h5 : Bal207PlusFamTitsFive G) (h6 : Bal207PlusFamRee32 G)
    (h7 : Bal207PlusFamSz32 G) : Bal207PlusFamExc G := by
  intro X _ _ hX p K B A ctx hK hIH
  obtain ⟨d, hd, e⟩ := hK
  rcases famExcNoG2_cases hd with h | h | h | h | h | h | h
  · exact h1 X hX p K B A ctx ⟨d, h, e⟩ hIH
  · exact h2 X hX p K B A ctx ⟨d, h, e⟩ hIH
  · exact h3 X hX p K B A ctx ⟨d, h, e⟩ hIH
  · exact h4 X hX p K B A ctx ⟨d, h, e⟩ hIH
  · exact h5 X hX p K B A ctx ⟨d, h, e⟩ hIH
  · exact h6 X hX p K B A ctx ⟨d, h, e⟩ hIH
  · exact h7 X hX p K B A ctx ⟨d, h, e⟩ hIH

@[expose] def IsA6Quot {X : Type} [Group X] (J : Subgroup X) : Prop :=
  Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* ↥(alternatingGroup (Fin 6)))

@[expose] def IsA6Narrow {X : Type} [Group X] (J : Subgroup X) : Prop :=
  IsA6Quot J ∧ ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J)

@[expose] def IsThreeCoverA6 {X : Type} [Group X] (J : Subgroup X) : Prop :=
  IsA6Quot J ∧ 3 ∣ Nat.card ↥(Subgroup.center ↥J)

@[expose] def IsU33Idx : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => r = 2 ∧ q.p = 3 ∧ q.exponent = 1
  | _ => False

@[expose] def IsSU38Idx : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => r = 2 ∧ IsTwoPow q 3
  | _ => False

@[expose] def IsU33Comp {X : Type} [Group X] (J : Subgroup X) : Prop := IsLieQuot ↥J IsU33Idx

@[expose] def IsSU38Comp {X : Type} [Group X] (J : Subgroup X) : Prop := IsLieQuot ↥J IsSU38Idx

@[expose] def IsL28Comp {X : Type} [Group X] (J : Subgroup X) : Prop :=
  IsLieQuot ↥J IsL2EightIndex

theorem isLieQuot_or_iff {Y : Type*} [Group Y] {P Q : TauCeti.LieTypeIndex → Prop} :
    IsLieQuot Y (fun d => P d ∨ Q d) ↔ IsLieQuot Y P ∨ IsLieQuot Y Q := by
  constructor
  · rintro ⟨d, hd | hd, e⟩
    · exact Or.inl ⟨d, hd, e⟩
    · exact Or.inr ⟨d, hd, e⟩
  · rintro (⟨d, hd, e⟩ | ⟨d, hd, e⟩)
    · exact ⟨d, Or.inl hd, e⟩
    · exact ⟨d, Or.inr hd, e⟩

theorem isSmallTwistedIdx_iff (d : TauCeti.LieTypeIndex) :
    IsSmallTwistedIdx d ↔ IsU33Idx d ∨ IsSU38Idx d := by
  cases d <;> simp [IsSmallTwistedIdx, IsU33Idx, IsSU38Idx, and_or_left]

theorem isBalSmall_cases {X : Type} [Group X] {J : Subgroup X} (h : IsBalSmall J) :
    IsA6Narrow J ∨ IsThreeCoverA6 J ∨ IsU33Comp J ∨ IsSU38Comp J ∨ IsL28Comp J := by
  rcases h with h | h | h
  · by_cases hZ : 3 ∣ Nat.card ↥(Subgroup.center ↥J)
    · exact Or.inr (Or.inl ⟨h, hZ⟩)
    · exact Or.inl ⟨h, hZ⟩
  · have e : IsSmallTwistedIdx = fun d => IsU33Idx d ∨ IsSU38Idx d :=
      funext fun d => propext (isSmallTwistedIdx_iff d)
    rw [e, isLieQuot_or_iff] at h
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

@[expose] def Bal207PlusSmallIn (G : ∀ (S : Type) [Group S], MulAut S → Prop)
    (S : ∀ {X : Type} [Group X], Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → Bal207PlusIH G A → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → S J →
        B ≤ Subgroup.normalizer (J : Set X) → IsStronglyLocallyOneBalanced 3 B a J

@[expose] def Bal207PlusSmallA6 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusSmallIn G (@IsA6Narrow)

@[expose] def Bal207PlusSmallL28 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusSmallIn G (@IsL28Comp)

@[expose] def Bal207PlusSmallU33 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusSmallIn G (@IsU33Comp)

@[expose] def Bal207PlusSmallSU38 (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  Bal207PlusSmallIn G (@IsSU38Comp)

@[expose] def Bal207PlusNoThreeCover (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → Bal207PlusIH G A → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → ¬ IsThreeCoverA6 J

@[expose] def Bal207PlusNoSmallFive (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 5 K B A → Bal207PlusIH G A → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 5 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → ¬ IsBalSmall J

@[expose] def Bal207PlusSmallComp (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B A : Subgroup X),
    Bal207PlusCtx G p K B A → Bal207PlusIH G A → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) → IsBalSmall J → IsStronglyLocallyOneBalanced p B a J

theorem bal207PlusSmallComp_of_parts {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    (hA6 : Bal207PlusSmallA6 G) (hL28 : Bal207PlusSmallL28 G) (hU33 : Bal207PlusSmallU33 G)
    (hSU38 : Bal207PlusSmallSU38 G) (hNC : Bal207PlusNoThreeCover G)
    (hF5 : Bal207PlusNoSmallFive G) : Bal207PlusSmallComp G := by
  intro X _ _ hX p K B A ctx hIH a haA ha1 J hJ hBJ hS
  rcases bal207PlusHyp_p ctx.hyp with rfl | rfl
  · rcases isBalSmall_cases hS with h | h | h | h | h
    · exact hA6 X hX K B A ctx hIH a haA ha1 J hJ h hBJ
    · exact absurd h (hNC X hX K B A ctx hIH a haA ha1 J hJ)
    · exact hU33 X hX K B A ctx hIH a haA ha1 J hJ h hBJ
    · exact hSU38 X hX K B A ctx hIH a haA ha1 J hJ h hBJ
    · exact hL28 X hX K B A ctx hIH a haA ha1 J hJ h hBJ
  · exact absurd hS (hF5 X hX K B A ctx hIH a haA ha1 J hJ)

theorem bal207Plus_engine {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X]
    [Finite X] (hX : CFSG.Open.IsKGroup X) (hSmall : Bal207PlusSmallComp G) {p : ℕ}
    {K B A : Subgroup X} (ctx : Bal207PlusCtx G p K B A) (hIH : Bal207PlusIH G A)
    (hDvd : p ∣ Nat.card ↥K) (hloc : IsCompLocallyBalanced p 1 A K)
    (hFam : Bal207PlusFamClauses p K B A) : IsStronglyBalancedIn p B K := by
  obtain ⟨hb1, hb2, a0, ha0A, ha01, hc⟩ := hFam
  have hBel : CFSG.Open.IsElemAbelian p B := ctx.scp.2.1
  have hSCK : IsSCp p (K ⊔ B) B :=
    ⟨le_sup_right, hBel, fun E _ hEel hBE => ctx.scp.2.2 E le_top hEel hBE⟩
  have hbc : Bal207Clauses p K B A := by
    refine ⟨fun a haA ha1 J hJ => ⟨hb1 a haA ha1 J hJ, ?_⟩, a0, ha0A, ha01, hc⟩
    by_cases hs : IsBalSmall J
    · exact hSmall X hX p K B A ctx hIH a haA ha1 J hJ (hb1 a haA ha1 J hJ) hs
    · exact hb2 a haA ha1 J hJ hs
  exact i202Full_holds X p ctx.prime ctx.odd K B A ctx.comp.2.2 hDvd ctx.norm hBel hSCK ctx.le
    ctx.noncyc hloc hbc.1 hbc.2

theorem bal207PlusBody_of_inputs (G : ∀ (S : Type) [Group S], MulAut S → Prop)
    (hDvd : Bal207Dvd) (hDvdD4 : Bal207PlusDvdD4Eight) (hLB : Bal207LocalBal)
    (hLBD4 : Bal207PlusLocalBalD4Eight) (hRank : Bal207Rank) (hRankD4 : Bal207PlusRankD4Eight)
    (hSz : Bal207SzCyclic) (hSmall : Bal207PlusSmallComp G) (hSp : Bal207PlusFamSp G)
    (hUni : Bal207PlusFamUni G) (hOrth : Bal207PlusFamOrth G) (hExc : Bal207PlusFamExc G)
    (hG2 : Bal207PlusFamG28 G) (hD4 : Bal207PlusFamD4Eight G) :
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → Bal207PlusBody G X := by
  have key : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      Nat.card X ≤ n → Bal207PlusBody G X := by
    intro n
    induction n with
    | zero =>
      intro X _ _ _ hn
      have := Nat.card_pos (α := X)
      omega
    | succ n ih =>
      intro X _ _ hX hn p K B hp hp2 hcomp hSC hBN hyp
      have hyp0 := hyp
      have hBel : CFSG.Open.IsElemAbelian p B := hSC.2.1
      have hIHof : ∀ A : Subgroup X, A ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
          Bal207PlusIH G A := by
        intro A hdisj a haA ha1
        have haC := not_mem_centralizer_of_inf_eq_bot hdisj haA ha1
        have hlt := card_centralizer_singleton_lt (K := K) haC
        exact ih _ (hX.subgroup (Subgroup.centralizer ({a} : Set X))) (by omega)
      obtain ⟨d, ⟨e⟩, hd⟩ := hyp
      rcases hd with ⟨hi, hg2⟩ | ⟨hp3, hD4i, hNT⟩
      · have hK : IsLieQuot ↥K (Bal207Index p) := ⟨d, hi, ⟨e⟩⟩
        rcases hRank X hX p K B hp hp2 hcomp hSC hBN hK with
          ⟨A, hAB, hnc, hdisj, hsup⟩ | ⟨hp5, hszK, hcyc⟩
        · have ctx : Bal207PlusCtx G p K B A :=
            ⟨hp, hp2, hcomp, hSC, hBN, hyp0, hAB, hnc, hdisj, hsup⟩
          have hIH := hIHof A hdisj
          have hAel : CFSG.Open.IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hBel hAB
          have hloc := hLB X hX p K A hp hp2 hcomp hK (hAB.trans hBN) hAel
          have hFam : Bal207PlusFamClauses p K B A := by
            by_cases hs : IsSpIdx d.1
            · exact hSp X hX p K B A ctx ⟨d, ⟨hi, hs⟩, ⟨e⟩⟩ hIH
            by_cases hu : IsUniIdx d.1
            · exact hUni X hX p K B A ctx ⟨d, ⟨hi, hu⟩, ⟨e⟩⟩ hIH
            by_cases ho : IsOrthIdx d.1
            · exact hOrth X hX p K B A ctx ⟨d, ⟨hi, ho⟩, ⟨e⟩⟩ hIH
            by_cases hg : IsG2EightIndex d.1
            · have hp3 := bal207Index_g2 hi hg
              subst hp3
              exact hG2 X hX K B A ctx ⟨d, hg, ⟨e⟩⟩ (hg2 hg) hIH
            · exact hExc X hX p K B A ctx ⟨d, ⟨⟨hi, hs, hu, ho⟩, hg⟩, ⟨e⟩⟩ hIH
          exact bal207Plus_engine hX hSmall ctx hIH (hDvd X p K hp hcomp hK) hloc hFam
        · subst hp5
          exact hSz X hX K B hcomp hSC hBN hszK hcyc
      · subst hp3
        have hK : IsLieQuot ↥K IsD4EightIdx := ⟨d, hD4i, ⟨e⟩⟩
        obtain ⟨A, hAB, hnc, hdisj, hsup⟩ := hRankD4 X hX K B hcomp hSC hBN hK
        have ctx : Bal207PlusCtx G 3 K B A :=
          ⟨hp, hp2, hcomp, hSC, hBN, hyp0, hAB, hnc, hdisj, hsup⟩
        have hIH := hIHof A hdisj
        have hAel : CFSG.Open.IsElemAbelian 3 A := CFSG.Open.IsElemAbelian.mono hBel hAB
        have hloc := hLBD4 X hX K A hcomp hK (hAB.trans hBN) hAel
        exact bal207Plus_engine hX hSmall ctx hIH (hDvdD4 X K hcomp hK) hloc
          (hD4 X hX K B A ctx hK hNT hIH)
  intro X _ _ hX
  exact key _ X hX le_rfl

end CFSG.HardMathSupport.Dickson.Bal207
