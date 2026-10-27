module

public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.RankThree.PartOne.S11c.Sec66G2
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure

theorem card_eq_two_pow_of_p_eq_two {q : TauCeti.PrimePower} (hd : q.p = 2) :
    q.card = 2 ^ q.exponent := by
  rw [TauCeti.PrimePower.card_def, hd]

theorem outPNice_three_of_idxB {X : Type} [Group X] (h : IsLieOf IdxB X) : OutPNice 3 X := by
  obtain ⟨⟨d, hv⟩, hd', ⟨e⟩⟩ := h
  cases d with
  | B r q =>
    change q.p = 2 at hd'
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd'] at hm
      exact outPNice_PSp_two Nat.prime_three hm
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd'
        (by omega) e
      rw [hd'] at hm
      obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hm
      exact outPNice_PSp_ge_three Nat.prime_three (by omega) hm
  | _ => exact hd'.elim

theorem outPNice_three_of_idxD {X : Type} [Group X] (h : IsLieOf IdxD X)
    (h4 : ∀ m : ℕ, ¬ StatedClassicalModel X .POmegaPlus 4 2 m) : OutPNice 3 X := by
  obtain ⟨⟨d, hv⟩, hd', ⟨e⟩⟩ := h
  cases d with
  | D r q =>
    change q.p = 2 at hd'
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd' e
    rw [hd'] at hm
    obtain ⟨⟨-, -, hn4⟩, -⟩ := id hm
    by_cases hr : r = 4
    · subst hr
      exact absurd hm (h4 _)
    · exact outPNice_POmegaPlus_ge_five Nat.prime_three (by norm_num) (by omega) hm
  | _ => exact hd'.elim

theorem outPNice_three_of_idxTwistedD {X : Type} [Group X] (h : IsLieOf IdxTwistedD X) :
    OutPNice 3 X := by
  obtain ⟨⟨d, hv⟩, hd', ⟨e⟩⟩ := h
  cases d with
  | twistedD r q =>
    change q.p = 2 at hd'
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd' e
    rw [hd'] at hm
    obtain ⟨⟨-, -, hn4⟩, -⟩ := id hm
    exact outPNice_POmegaMinus Nat.prime_three (by norm_num) hn4 hm
  | _ => exact hd'.elim

theorem outPNice_three_of_idxG2
    {X : Type} [Group X] (h : IsLieOf IdxG2 X) : OutPNice 3 X := by
  obtain ⟨⟨d, hv⟩, hd', ⟨e⟩⟩ := h
  cases d with
  | G2 q =>
    change q.p = 2 at hd'
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd'
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd'
      (GaloisField q.p q.exponent) hK
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hcard : q.card = 2 ^ q.exponent := card_eq_two_pow_of_p_eq_two hd'
    have hm : 2 ≤ q.exponent := by
      by_contra hm
      have h1 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hL : CFSG.Blueprint.LieModel X .G2 0 2 q.exponent :=
      (CFSG.RankThree.PartOne.Sec66T.lieModel_untwisted_iff
        CFSG.RankThree.PartOne.Sec66T.untwistedTag_G2).mpr ⟨rfl,
        CFSG.RankThree.PartOne.Sec66T.admissible_G2 hm, GaloisField q.p q.exponent, inferInstance,
        inferInstance, hK.trans hcard, ⟨e.trans b.symm⟩⟩
    rcases hL with ⟨ht, -⟩ | ⟨-, -, hch⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · simp [CFSG.Blueprint.classicalTags] at ht
    · exact outPNice_G2 Nat.prime_three hch
    · simp [CFSG.Blueprint.reeTitsTags] at ht
    · simp at ht
  | _ => exact hd'.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
