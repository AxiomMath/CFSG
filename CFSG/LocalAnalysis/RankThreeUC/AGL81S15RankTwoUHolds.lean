module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUCases
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUConj
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUKFact
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open KFactsPair

theorem exists_elemAbelian_le_gnA_twistedA {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hc : CFSG.Quasithin.IsC118Pair T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ Ls) Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {m : ℕ} (hm : m = 3 ∨ m = 4) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Q.card - 1)
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center ↥Ls)) :
    ∃ E : Subgroup (X ⧸ gnC T), IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      (E ≤ gnA T T₁ Ls ∨ E ≤ gnA T T₂ Ls) := by
  classical
  let U : Subgroup ↥Ls := (gnImg T T ⊓ Ls).subgroupOf Ls
  have hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · rw [show (U.subgroupOf (⊤ : Subgroup ↥Ls)).index = U.index from
        Subgroup.relIndex_top_right _]
      exact hS.2.2
  have hsc : HasScalarTorus ↥Ls q U := by
    rcases hm with rfl | rfl
    · exact hasScalarTorus_of_twistedA_three (L := ↥Ls) (U := U) (hv := hv)
        hQ e hq hq2 hdvd hqZ hUmax
    · exact hasScalarTorus_of_twistedA_four (L := ↥Ls) (U := U) (hv := hv)
        hQ e hq hq2 hdvd hqZ hUmax
  obtain ⟨E, hELs, hEU, hE, hcard, hscal, hinvol⟩ :=
    exists_scalarTorus_of_hasScalarTorus (Ls := Ls) hinv hsc
  exact ⟨E, hE, hcard,
    le_gnA_of_scalarTorus hT hc hinv hq hq2 hELs hEU hE.2 hscal hinvol⟩

private theorem K517_4b_rank_two_twistedA_of
    {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {m : ℕ} (hm : m = 3 ∨ m = 4) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid}
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Q.card - 1) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  by_cases hqZ : q ∣ Nat.card (Subgroup.center ↥Ls)
  · exact hGood.centre Ls hY hinv q hq hqZ
  · have hodd : Odd (Q.card - 1) := by
      rw [TauCeti.PrimePower.card_def, hQ]
      exact Nat.Even.sub_odd Nat.one_le_two_pow
        (Nat.even_pow.mpr ⟨even_two, Q.exponent_pos.ne'⟩) odd_one
    have hq2 : q ≠ 2 := Odd.ne_two_of_dvd_nat hodd hdvd
    have hS : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
        hX.sylow hY.1.2.1
    obtain ⟨E, hE, hcard, hdisj⟩ :=
      exists_elemAbelian_le_gnA_twistedA hX.sylow hGood.c118 hS hinv hm hQ
        (hv := hv) e hq hq2 hdvd hqZ
    rcases hdisj with h | h
    · exact Or.inl (one_lt_mS_of_isElemAbelian_le_gnA hq h hE hcard)
    · exact Or.inr (one_lt_mS_of_isElemAbelian_le_gnA hq h hE hcard)

theorem K517_4b_rank_two_twistedA_three :
    ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
      GNSetting X T → GNGood T T₁ T₂ →
      ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q) →
        IsRankTwoPlus d.1 → IsRankTwoType d.1 →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ q : ℕ, q.Prime → q ∣ indexQ d.1 - 1 →
          1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hd _ hRT he q hq hqQ
  obtain ⟨Q, hdQ⟩ := hd
  obtain ⟨d1, hd1⟩ := d
  change d1 = .twistedA 3 Q at hdQ
  subst d1
  obtain ⟨e⟩ := he
  have hQ : Q.p = 2 := hRT
  exact K517_4b_rank_two_twistedA_of hX hGood hY hinv (m := 3) (Or.inl rfl)
    hQ (hv := hd1) e hq (by simpa only [indexQ] using hqQ)

theorem K517_4b_rank_two_twistedA_four :
    ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
      GNSetting X T → GNGood T T₁ T₂ →
      ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, d.1 = .twistedA 4 Q) →
        IsRankTwoPlus d.1 → IsRankTwoType d.1 →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ q : ℕ, q.Prime → q ∣ indexQ d.1 - 1 →
          1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hd _ hRT he q hq hqQ
  obtain ⟨Q, hdQ⟩ := hd
  obtain ⟨d1, hd1⟩ := d
  change d1 = .twistedA 4 Q at hdQ
  subst d1
  obtain ⟨e⟩ := he
  have hQ : Q.p = 2 := hRT
  exact K517_4b_rank_two_twistedA_of hX hGood hY hinv (m := 4) (Or.inr rfl)
    hQ (hv := hd1) e hq (by simpa only [indexQ] using hqQ)

theorem K517_4b_rank_two_unitary :
    ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
      GNSetting X T → GNGood T T₁ T₂ →
      ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        (∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q ∨ d.1 = .twistedA 4 Q) →
        IsRankTwoPlus d.1 → IsRankTwoType d.1 →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ q : ℕ, q.Prime → q ∣ indexQ d.1 - 1 →
          1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hd hR2 hRT he q hq hqQ
  obtain ⟨Q, hdQ | hdQ⟩ := hd
  · exact K517_4b_rank_two_twistedA_three X T T₁ T₂ hX hGood Ls hY hinv d ⟨Q, hdQ⟩ hR2 hRT he
      q hq hqQ
  · exact K517_4b_rank_two_twistedA_four X T T₁ T₂ hX hGood Ls hY hinv d ⟨Q, hdQ⟩ hR2 hRT he
      q hq hqQ

end CFSG.LocalAnalysis.RankThreeUC.S15

end
