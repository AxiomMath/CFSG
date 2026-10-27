module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I71
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.CardLemma
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Linear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerAssembly
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Orth

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower (outTowerAt_orthogonal)
open CFSG.RankThree.PartTwo.Census

section Certificates



private theorem five_le_of_prime_ne_two_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  by_contra h
  have h4 : p = 4 := by omega
  subst h4
  exact absurd hp (by norm_num)

theorem outTwoTowerAt_lie (d : TauCeti.ValidLieTypeIndex) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexc : p = 3 → ∀ q : TauCeti.PrimePower, d.1 = .D 4 q → q.p = 2) :
    OutTwoTowerAt (TauCeti.CFSGIndex.lie d).Group p := by
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hexcl : ∀ (d' : TauCeti.LieTypeIndex) (hv' : d'.Valid), IsExceptionalLieIndex d' →
      OutTwoTowerAt (TauCeti.CFSGIndex.lie ⟨d', hv'⟩).Group p := fun d' hv' h =>
    outTwoTowerAt_of_outTowerAt (exceptionalTowers.lie ⟨d', hv'⟩ h p hp hp2)
  cases d with
  | A m q =>
    have hm1 : 1 ≤ m := hrange.1
    rcases Nat.lt_or_ge m 2 with h1 | hm2
    · obtain rfl : m = 1 := by omega
      exact outTwoTowerAt_of_outTowerAt (outTowerAt_catA_one hv)
    · exact outTwoTowerAt_catA hm2 hv hp hp2
  | twistedA m q => exact outTwoTowerAt_cat_twistedA hv hp hp2
  | B r q =>
    have hr2 : 2 ≤ r := hrange.1
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · obtain rfl : r = 2 := by omega
      exact outTwoTowerAt_of_outTowerAt (outTowerAt_catB_two hv)
    · by_cases hq2 : q.p = 2
      · exact outTwoTowerAt_of_outTowerAt (outTowerAt_catB_even hr3 hq2 hv)
      · exact outTwoTowerAt_of_outTowerAt (outTowerAt_of_statedOdd_all
          (statedClassicalModel_typeB_odd r q hv hq2 hr3 (MulEquiv.refl _)))
  | C r q => exact outTwoTowerAt_of_outTowerAt (outTowerAt_catC hv)
  | D r q =>
    by_cases hp3 : p = 3
    · subst hp3
      have hr4 : 4 ≤ r := hrange
      have hmod := statedClassicalModel_typeD r q hv (MulEquiv.refl _)
      by_cases hq2 : q.p = 2
      · exact outTwoTowerAt_of_statedPlus_charTwo hq2 hmod hp hp2
      · have h5 : 5 ≤ r := by
          rcases Nat.eq_or_lt_of_le hr4 with h4 | h5
          · subst h4
            exact absurd (hexc rfl q rfl) hq2
          · exact h5
        exact outTwoTowerAt_of_outTowerAt (outTowerAt_of_statedPlus_odd_three hq2 h5 hmod)
    · exact outTwoTowerAt_of_outTowerAt (outTowerAt_orthogonal (d := ⟨.D r q, hv⟩)
        (Or.inr (Or.inl ⟨r, q, rfl⟩)) hp (five_le_of_prime_ne_two_three hp hp2 hp3))
  | twistedD r q =>
    by_cases hp3 : p = 3
    · subst hp3
      have hmod := statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)
      by_cases hq2 : q.p = 2
      · exact outTwoTowerAt_of_statedMinus_charTwo hq2 hmod hp hp2
      · exact outTwoTowerAt_of_outTowerAt (outTowerAt_of_statedMinus_odd_three hq2 hmod)
    · exact outTwoTowerAt_of_outTowerAt (outTowerAt_orthogonal (d := ⟨.twistedD r q, hv⟩)
        (Or.inr (Or.inr ⟨r, q, rfl⟩)) hp (five_le_of_prime_ne_two_three hp hp2 hp3))
  | E6 q => exact hexcl _ hv trivial
  | E7 q => exact hexcl _ hv trivial
  | E8 q => exact hexcl _ hv trivial
  | F4 q => exact hexcl _ hv trivial
  | G2 q => exact hexcl _ hv trivial
  | twistedE6 q => exact hexcl _ hv trivial
  | trialityD4 q => exact hexcl _ hv trivial
  | suzuki m => exact hexcl _ hv trivial
  | reeG2 m => exact hexcl _ hv trivial
  | reeF4 m => exact hexcl _ hv trivial
  | tits => exact hexcl _ hv trivial

theorem kdOut_holds : KDOut := by
  intro S _ _ _ hnab hcat p hp hp2 P T hP hT hPT
  obtain ⟨i, ⟨e⟩⟩ := hcat
  by_cases hexc : p = 3 ∧ IsPOmegaEightPlusOdd S
  · exact Or.inr hexc
  · left
    have key : OutTwoTowerAt S p := by
      refine OutTwoTowerAt.of_mulEquiv e ?_
      cases i with
      | cyclic r hr =>
        exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
      | alternating n hn =>
        exact outTwoTowerAt_of_card_outer_le_four hp hp2
          (CFSG.RankThree.PartOne.card_outer_alternating_le_four hn)
      | sporadic s => exact outTwoTowerAt_of_outTowerAt (exceptionalTowers.sporadic s p hp hp2)
      | lie d =>
        refine outTwoTowerAt_lie d hp hp2 fun hp3 q hq => ?_
        by_contra hq2
        obtain ⟨d, hv⟩ := d
        change d = .D 4 q at hq
        subst hq
        exact hexc ⟨hp3, q, hv, hq2, ⟨e⟩⟩
    exact commutator_le_inner_of_outTwoTower hp hp2 key hP hT hPT

end Certificates

end CFSG.LocalAnalysis.GLTheoremA
