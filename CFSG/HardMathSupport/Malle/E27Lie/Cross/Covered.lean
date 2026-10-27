module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.IndexUnitary
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.IndexSymplectic
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearTwo
public import CFSG.HardMathSupport.Foote.E27.LieTwo.TypeASmall
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddIndex
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.RankIndex

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding TauCeti

@[expose] def InnerCoveredA (i : LieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : PrimePower), i = .A r q ∧ q.p ≠ 3 ∧
    (r = 1 ∨ (3 ≤ r ∧ 4 ≤ q.p ^ q.exponent) ∨ (4 ≤ r ∧ q.p ^ q.exponent = 2) ∨
      r = 2 ∨ (r = 3 ∧ q.p ^ q.exponent = 2))

@[expose] def InnerCoveredTwistedA (i : LieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : PrimePower), i = .twistedA r q ∧ q.p ≠ 3 ∧
    (r = 2 ∨ (4 ≤ q.p ^ q.exponent ∧ 3 ≤ r) ∨ (q.p ^ q.exponent = 2 ∧ 9 ≤ r))

@[expose] def InnerCoveredSp (i : LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : PrimePower), i = .C r q ∧ q.p ≠ 3 ∧ 4 ≤ q.p ^ q.exponent ∧ 2 ≤ r) ∨
  (∃ q : PrimePower, i = .B 2 q ∧ q.p ≠ 3) ∨
  (∃ (r : ℕ) (q : PrimePower), i = .B r q ∧ q.p = 2 ∧ 4 ≤ q.p ^ q.exponent ∧ 3 ≤ r)

@[expose] def InnerCoveredOrthOdd (i : LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : PrimePower), i = .B r q ∧ q.p ≠ 2 ∧ q.p ≠ 3 ∧ 3 ≤ r) ∨
  (∃ (r : ℕ) (q : PrimePower), i = .D r q ∧ q.p ≠ 2 ∧ q.p ≠ 3) ∨
  (∃ (r : ℕ) (q : PrimePower), i = .twistedD r q ∧ q.p ≠ 2 ∧ q.p ≠ 3)

@[expose] def InnerCovered (i : LieTypeIndex) : Prop :=
  InnerCoveredA i ∨ InnerCoveredTwistedA i ∨ InnerCoveredSp i ∨ InnerCoveredOrthOdd i ∨
    IdxBCent i ∨ IdxDCent i ∨ IdxTwistedDCent i

theorem false_of_innerCovered {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (d : ValidLieTypeIndex) (hd : InnerCovered d.1)
    (e : Nonempty (↥K ≃* (CFSGIndex.lie d).Group)) : False := by
  obtain ⟨i, hv⟩ := d
  rcases hd with ⟨r, q, rfl, hp3, hr⟩ | ⟨r, q, rfl, hp3, hr⟩ |
    (⟨r, q, rfl, hp3, hq4, hr⟩ | ⟨q, rfl, hp3⟩ | ⟨r, q, rfl, hp2, hq4, hr⟩) |
    (⟨r, q, rfl, hp2, hp3, hr⟩ | ⟨r, q, rfl, hp2, hp3⟩ | ⟨r, q, rfl, hp2, hp3⟩) | hd
  · rcases hr with rfl | hr | hr | rfl | ⟨rfl, hq2⟩
    · exact false_of_typeA_one h hz hv e hp3
    · exact false_of_typeA h hz hv e hp3 (Or.inl hr)
    · exact false_of_typeA h hz hv e hp3 (Or.inr hr)
    · exact false_of_typeA_two h hz hv e hp3
    · exact h.false_of_typeA_two_small hz hv e hq2 (Or.inr rfl)
  · rcases hr with rfl | hr
    · exact false_of_typeTwistedA_two h hz hv e hp3
    refine false_of_typeTwistedA h hz hv e hp3 ?_
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩
  · exact false_of_typeC h hz hv e hp3 hq4 hr
  · exact false_of_typeB2 h hz hv e hp3
  · exact false_of_typeB_even h hz hv e hp2 hq4 hr
  · exact false_of_typeB_odd h hz hv e hp2 hp3 hr
  · exact false_of_typeD_odd h hz hv e hp2 hp3
  · exact false_of_typeTwistedD_odd h hz hv e hp2 hp3
  · exact false_of_even_classical h hz ⟨i, hv⟩ hd e

end CFSG.HardMathSupport.Malle.E27Lie
