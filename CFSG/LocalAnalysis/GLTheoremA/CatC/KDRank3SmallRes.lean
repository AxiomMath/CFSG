module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallL3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs

namespace KDRank3SmallRes

theorem kdRank3Small_of_residuals
    (hExistRest : ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → IsRank3Small d.1 →
        (∀ q : TauCeti.PrimePower, d.1 ≠ TauCeti.LieTypeIndex.A 2 q) →
        ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6)
    (hF1 : ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → IsRank3Small d.1 →
        ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
          ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S →
          Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S) = 3 ^ 2 →
          SmallF1 S E)
    (hF2 : ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → IsRank3Small d.1 →
        ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
          ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S →
          Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S) = 3 ^ 2 →
          SmallF2 S E)
    (hF3 : ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → IsRank3Small d.1 → SmallF3 S) :
    KDRank3Small := by
  unfold KDRank3Small
  intro S _ _ d hd hsmall E hE hcard hnot hE0
  unfold Rank3Concl
  have hExist : ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
    by_cases hA : ∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.A 2 q
    · obtain ⟨q, hq⟩ := hA
      obtain ⟨idx, hv⟩ := d
      subst hq
      exact KDRank3SmallL3.exists_six_of_A2 q hv hsmall hd.some
    · exact hExistRest S d hd hsmall (fun q hq => hA ⟨q, hq⟩)
  refine ⟨hExist, fun T hT hN hc => ?_⟩
  exact twoSub_eq_bot hE hcard hnot hE0 (hF1 S d hd hsmall E hE hcard hnot hE0)
    (hF2 S d hd hsmall E hE hcard hnot hE0) (hF3 S d hd hsmall) T hT hN hc

end KDRank3SmallRes

end CFSG.LocalAnalysis.GLTheoremA
