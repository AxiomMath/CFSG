module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def IsLThreeFourIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ q.p = 2 ∧ q.exponent = 2

inductive GL83Type24 (p : ℕ) : TauCeti.CFSGIndex → Prop
  | linTwo {d : TauCeti.ValidLieTypeIndex} {n : ℕ} (hn : 2 ≤ n) (hd : IsLinTwoIndex p n d) :
      GL83Type24 p (.lie d)
  | unitary {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) : GL83Type24 p (.lie d)
  | altTwoP (h : 5 ≤ 2 * p) : GL83Type24 p (.alternating (2 * p) h)
  | ree {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex p d) : GL83Type24 p (.lie d)
  | linTwoEight {d : TauCeti.ValidLieTypeIndex} (hp : p = 3) (hd : IsLinTwoIndex 2 3 d) :
      GL83Type24 p (.lie d)
  | mEleven (hp : p = 3) : GL83Type24 p (.sporadic .M11)
  | linThreeFour {d : TauCeti.ValidLieTypeIndex} (hp : p = 3) (hd : IsLThreeFourIndex d) :
      GL83Type24 p (.lie d)
  | suzuki {d : TauCeti.ValidLieTypeIndex} (hp : p = 5) (hd : d.1 = .suzuki 2) :
      GL83Type24 p (.lie d)
  | tits {d : TauCeti.ValidLieTypeIndex} (hp : p = 5) (hd : d.1 = .tits) : GL83Type24 p (.lie d)
  | mcl (hp : p = 5) : GL83Type24 p (.sporadic .McL)
  | fiTwentyTwo (hp : p = 5) : GL83Type24 p (.sporadic .Fi22)
  | jFour (hp : p = 11) : GL83Type24 p (.sporadic .J4)

@[expose] def GL83OuterType24 (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
    ((p = 3 ∧ IsLinTwoIndex 2 3 d) ∨ (p = 5 ∧ d.1 = .suzuki 2))

inductive PPointType (p : ℕ) : TauCeti.CFSGIndex → Prop
  | linTwo {d : TauCeti.ValidLieTypeIndex} {n : ℕ} (hn : 2 ≤ n) (hd : IsLinTwoIndex p n d) :
      PPointType p (.lie d)
  | altTwoP (h : 5 ≤ 2 * p) (hp : p = 3 ∨ p = 5) : PPointType p (.alternating (2 * p) h)
  | unitary {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
      (hn : d.1.fieldExponent = 1) : PPointType p (.lie d)
  | linTwoEight {d : TauCeti.ValidLieTypeIndex} (hp : p = 3) (hd : IsLinTwoIndex 2 3 d) :
      PPointType p (.lie d)
  | mEleven (hp : p = 3) : PPointType p (.sporadic .M11)
  | linThreeFour {d : TauCeti.ValidLieTypeIndex} (hp : p = 3) (hd : IsLThreeFourIndex d) :
      PPointType p (.lie d)
  | suzuki {d : TauCeti.ValidLieTypeIndex} (hp : p = 5) (hd : d.1 = .suzuki 2) :
      PPointType p (.lie d)
  | tits {d : TauCeti.ValidLieTypeIndex} (hp : p = 5) (hd : d.1 = .tits) : PPointType p (.lie d)
  | mcl (hp : p = 5) : PPointType p (.sporadic .McL)
  | jFour (hp : p = 11) : PPointType p (.sporadic .J4)

inductive PPointExcluded (p : ℕ) : TauCeti.CFSGIndex → Prop
  | altTwoP (h : 5 ≤ 2 * p) (hp : 7 ≤ p) : PPointExcluded p (.alternating (2 * p) h)
  | fiTwentyTwo (hp : p = 5) : PPointExcluded p (.sporadic .Fi22)
  | monster (hp : p = 11 ∨ p = 13) : PPointExcluded p (.sporadic .M)
  | unitary {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
      (hn : 2 ≤ d.1.fieldExponent) : PPointExcluded p (.lie d)
  | ree {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex p d) : PPointExcluded p (.lie d)

theorem GL83Type24.cases {p : ℕ} (hp : p.Prime) {i : TauCeti.CFSGIndex} (h : GL83Type24 p i) :
    PPointType p i ∨ PPointExcluded p i := by
  cases h with
  | linTwo hn hd => exact Or.inl (.linTwo hn hd)
  | @unitary d hd =>
    by_cases hn : d.1.fieldExponent = 1
    · exact Or.inl (.unitary hd hn)
    · refine Or.inr (.unitary hd ?_)
      obtain ⟨q, -, hq⟩ := hd
      have hq1 : d.1.fieldExponent = q.exponent := by rw [hq]; simp
      have := q.exponent_pos
      omega
  | altTwoP h =>
    have h2 : 3 ≤ p := by omega
    by_cases h7 : 7 ≤ p
    · exact Or.inr (.altTwoP h h7)
    · have : p = 3 ∨ p = 5 := by
        interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)
      exact Or.inl (.altTwoP h this)
  | ree hd => exact Or.inr (.ree hd)
  | linTwoEight hp3 hd => exact Or.inl (.linTwoEight hp3 hd)
  | mEleven hp3 => exact Or.inl (.mEleven hp3)
  | linThreeFour hp3 hd => exact Or.inl (.linThreeFour hp3 hd)
  | suzuki hp5 hd => exact Or.inl (.suzuki hp5 hd)
  | tits hp5 hd => exact Or.inl (.tits hp5 hd)
  | mcl hp5 => exact Or.inl (.mcl hp5)
  | fiTwentyTwo hp5 => exact Or.inr (.fiTwentyTwo hp5)
  | jFour hp11 => exact Or.inl (.jFour hp11)

@[expose] def GL83ComponentPCoreTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CatalogSimpleSections X → ∀ (p : ℕ) (R : Sylow p X)
    (K : Subgroup X), p.Prime → p ≠ 2 → 3 ≤ Open.pRank p (R : Subgroup X) →
    IsComponentOf K ⊤ → ¬ K ≤ GLBWeakCore p (R : Subgroup X) → CFSG.pCore p K = ⊥

@[expose] def GL83NongenerationList : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CatalogSimpleSections X → ∀ (p : ℕ) (R : Sylow p X)
    (K : Subgroup X), p.Prime → p ≠ 2 → 3 ≤ Open.pRank p (R : Subgroup X) →
    IsComponentOf K ⊤ → K.Normal → (R : Subgroup X) ⊓ centralizer (K : Set X) ≠ ⊥ →
    ¬ K ≤ GLBCore p 2 (R : Subgroup X) →
    ∃ i : TauCeti.CFSGIndex, Nonempty (K ⧸ center K ≃* i.Group) ∧ GL83Type24 p i ∧
      (GL83OuterType24 p i ∨
        ∀ g ∈ (R : Subgroup X), g ^ p = 1 → g ∈ K ⊔ centralizer (K : Set X))

@[expose] def GL83SignalizerAut : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ) (i : TauCeti.CFSGIndex), p.Prime → p ≠ 2 →
    GL83Type24 p i → Nonempty (K ≃* i.Group) → ∀ B Y : Subgroup (MulAut K),
      IsElemAbelian p B → Nat.card B = p ^ 2 → p.Coprime (Nat.card Y) →
      B ≤ normalizer (Y : Set (MulAut K)) →
      (B ≤ (MulAut.conj : K →* MulAut K).range ∨ GL83OuterType24 p i) →
      B ≤ centralizer (Y : Set (MulAut K))

end CFSG.LocalAnalysis.RankFourTheoremC
