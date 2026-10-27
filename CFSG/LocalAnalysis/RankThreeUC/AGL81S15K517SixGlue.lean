module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixSurv
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixSUKill
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541Even
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenFam
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem coveredByTwo_gnA {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls)) :
    CoveredByTwo Ls (gnImg T T ⊓ Ls) (gnA T T₁ Ls) (gnA T T₂ Ls) := by
  intro P hP
  have hO : pElementSubgroup 2 P ≤ Ls := (pElementSubgroup_le P).trans hP.1
  rcases hg.parabolic Ls hLs hchev P hP with h | h
  · left
    exact le_inf (h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _))) hO
  · right
    exact le_inf h hO

end CFSG.LocalAnalysis.RankThreeUC.S15

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.QuasithinUnique KFactsPair
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank

section Ctx

variable {X : Type} [Group X] [Finite X]

structure K6Ctx (T T₁ T₂ : Subgroup X) (Ls : Subgroup (X ⧸ gnC T)) : Prop where
  sylow : IsSylowTwoOf (gnImg T T ⊓ Ls) Ls
  cov : CoveredByTwo Ls (gnImg T T ⊓ Ls) (gnA T T₁ Ls) (gnA T T₂ Ls)
  s₁ : gnImg T T ⊓ Ls ≤ gnA T T₁ Ls
  s₂ : gnImg T T ⊓ Ls ≤ gnA T T₂ Ls
  r₁ : CFSG.Open.pRank 3 (gnA T T₁ Ls) ≤ 1
  r₂ : CFSG.Open.pRank 3 (gnA T T₂ Ls) ≤ 1
  rank : 2 < CFSG.Open.pRank 3 Ls
  quasi : CFSG.Open.IsQuasisimple ↥Ls
  oddCenter : Odd (Nat.card (Subgroup.center ↥Ls))

@[expose] def K6Concl (T T₁ T₂ : Subgroup X) (Ls : Subgroup (X ⧸ gnC T)) : Prop :=
  IsUFourOdd ↥Ls ∨
    (CFSG.Open.pRank 3 Ls = 3 ∧ (HasLThreeCore (gnA T T₁ Ls) ∨ HasLThreeCore (gnA T T₂ Ls)))

variable {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}

theorem le_normalizer_of_pair_char {Ti : Subgroup X} (hle : Ti ≤ T)
    (hc : (Ti.subgroupOf T).Characteristic) : T ≤ Subgroup.normalizer (Ti : Set X) := by
  haveI := hc
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 inferInstance

theorem K6Ctx.of_gn (hX : GNSetting X T) (hgood : GNGood T T₁ T₂)
    (hY : GNYComponent T T₁ T₂ Ls) (hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls))
    (hrk : 2 < CFSG.Open.pRank 3 Ls) (hm₁ : mS T T₁ 3 Ls = 1) (hm₂ : mS T T₂ 3 Ls = 1) :
    K6Ctx T T₁ T₂ Ls := by
  have hpair := hgood.pair
  have hT₁ : T₁ ≤ T := hpair.le_center.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hTN₁ := le_normalizer_of_pair_char hT₁ hpair.char₁
  have hTN₂ := le_normalizer_of_pair_char hpair.le₂ hpair.char₂
  refine ⟨CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
    hY.1.2.1, coveredByTwo_gnA hgood hY.1 hchev,
    inf_le_inf_right Ls (Subgroup.map_mono hTN₁),
    inf_le_inf_right Ls (Subgroup.map_mono hTN₂), hm₁.le, hm₂.le, hrk, hY.1.2.2,
    K541Proof.odd_card_center_of_component hX hY.1⟩

end Ctx

section Rank

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}

theorem pRank_Ls_eq (hT : LieOddRankTable) (ctx : K6Ctx T T₁ T₂ Ls) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsRankTwoPlus d.1)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 3 Ls = mRankChev d.1 3 (Nat.card (Subgroup.center ↥Ls)) := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ls]
  exact hT.chev ↥Ls ctx.quasi d (K517ChevGenQ.classical_of_rankTwoPlus hd) ⟨e⟩ 3 Nat.prime_three
    (by norm_num)

theorem false_of_mRank_le (hT : LieOddRankTable) (ctx : K6Ctx T T₁ T₂ Ls)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsRankTwoPlus d.1)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hm : mRankChev d.1 3 (Nat.card (Subgroup.center ↥Ls)) ≤ 2) : False := by
  have h := pRank_Ls_eq hT ctx hd e
  have := ctx.rank
  omega

theorem odd_exponent_of_not_dvd {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (h : ¬ 3 ∣ Q.card - 1) :
    Odd Q.exponent := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  obtain ⟨k, hk⟩ := hne
  apply h
  rw [TauCeti.PrimePower.card_def, hQ, hk, ← two_mul, pow_mul]
  have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) k
  simpa using this

theorem not_dvd_indexQ (h4b : K517_4b) (hX : GNSetting X T) (hgood : GNGood T T₁ T₂)
    (hY : GNYComponent T T₁ T₂ Ls) (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {d : TauCeti.ValidLieTypeIndex} (hd : IsRankTwoPlus d.1)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hm₁ : mS T T₁ 3 Ls = 1) (hm₂ : mS T T₂ 3 Ls = 1) : ¬ 3 ∣ indexQ d.1 - 1 := fun h3 =>
  (h4b X T T₁ T₂ hX hgood Ls hY hinv d hd ⟨e⟩ 3 Nat.prime_three h3).elim
    (fun h => by omega) (fun h => by omega)

theorem center_eq_bot_of_ksmOdd (hK : KSMOdd) (ctx : K6Ctx T T₁ T₂ Ls)
    {d : TauCeti.ValidLieTypeIndex} (hIn : In1512 d.1) (hA2 : ∀ Q, d.1 ≠ .A 2 Q)
    (hTA3 : ∀ Q, d.1 ≠ .twistedA 3 Q) (hTA4 : ∀ Q, d.1 ≠ .twistedA 4 Q)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Subgroup.center ↥Ls = ⊥ :=
  Subgroup.eq_bot_of_card_eq _
    ((hK.1 ↥Ls ctx.quasi d hIn hA2 hTA3 ⟨e⟩ ctx.oddCenter).2 hTA4)

end Rank

section Families

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {k : ℕ} (h : Nat.card F = 2 ^ k) :
    CharP F 2 := by
  haveI := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem k6_A (hT : LieOddRankTable) (ctx : K6Ctx T T₁ T₂ Ls) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A l Q).Valid) (hd : IsRankTwoPlus (.A l Q))
    (hnodd : Odd Q.exponent)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie ⟨.A l Q, hv⟩).Group) : False := by
  by_cases hl5 : 5 ≤ l
  · have hQ : Q.p = 2 := hd.1
    haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
    haveI : CharP (GaloisField Q.p Q.exponent) 2 := CharP.congr Q.p hQ
    exact false_of_sl ctx.sylow ctx.cov inf_le_right inf_le_right ctx.r₁ ctx.r₂ hl5
      ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL l Q hv).symm.trans e.symm)
  · have hl2 : 2 ≤ l := hd.2
    refine false_of_mRank_le hT ctx hd e ?_
    rcases (by omega : l = 2 ∨ l = 3 ∨ l = 4) with rfl | rfl | rfl
    · exact ((mRank3_cases hd _).1.2 hnodd).le.trans (by norm_num)
    · exact ((mRank3_cases hd _).2.1.2 hnodd).le
    · exact ((mRank3_cases hd _).2.1.2 hnodd).le

theorem k6_G2 (hT : LieOddRankTable) (ctx : K6Ctx T T₁ T₂ Ls) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 Q).Valid) (hd : IsRankTwoPlus (.G2 Q))
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 Q, hv⟩).Group) : False :=
  false_of_mRank_le hT ctx hd e ((mRank3_cases hd _).2.1.2 trivial).le

theorem k6_D (ctx : K6Ctx T T₁ T₂ Ls) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D l Q).Valid) (hd : IsRankTwoPlus (.D l Q))
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie ⟨.D l Q, hv⟩).Group) : False := by
  have hQ : Q.p = 2 := hd.1
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even l Q hv hQ e
  rw [hQ] at hmodel
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hmodel
  haveI := charP_two_of_card hcard
  exact false_of_spinPlus ctx.sylow ctx.cov inf_le_right inf_le_right ctx.r₁ ctx.r₂ hd.2 e'

theorem k6_B (hT : LieOddRankTable) (hK : KSMOdd) (ctx : K6Ctx T T₁ T₂ Ls) {l : ℕ}
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B l Q).Valid) (hd : IsRankTwoPlus (.B l Q))
    (hnodd : Odd Q.exponent)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie ⟨.B l Q, hv⟩).Group) :
    K6Concl T T₁ T₂ Ls := by
  have hQ : Q.p = 2 := hd.1
  have hl2 : 2 ≤ l := hd.2
  rcases (by omega : l = 2 ∨ l = 3 ∨ 4 ≤ l) with rfl | rfl | hl4
  · exact (false_of_mRank_le hT ctx hd e ((mRank3_cases hd _).2.1.2 trivial).le).elim
  · have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 Q hv hQ
      (by norm_num) e
    rw [hQ] at hmodel
    obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hmodel
    haveI := charP_two_of_card hcard
    have hZ := center_eq_bot_of_ksmOdd hK ctx (d := ⟨.B 3 Q, hv⟩) hQ
      (fun _ h => TauCeti.LieTypeIndex.noConfusion h)
      (fun _ h => TauCeti.LieTypeIndex.noConfusion h)
      (fun _ h => TauCeti.LieTypeIndex.noConfusion h) e
    refine Or.inr ⟨?_, hasLThreeCore_sp_three ctx.sylow ctx.cov inf_le_right inf_le_right ctx.s₁
      ctx.s₂ ctx.r₁ ctx.r₂ hcard hnodd hZ e'⟩
    rw [pRank_Ls_eq hT ctx hd e]
    exact (mRank3_cases hd _).2.2.1.2 trivial
  · exfalso
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even l Q hv hQ
      (by omega) e
    rw [hQ] at hmodel
    obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hmodel
    haveI := charP_two_of_card hcard
    exact false_of_sp ctx.sylow ctx.cov inf_le_right inf_le_right ctx.r₁ ctx.r₂ hl4 e'

end Families

section TwistedD

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}

theorem k6_TD (hT : LieOddRankTable) (hK : KSMOdd) (ctx : K6Ctx T T₁ T₂ Ls) {l : ℕ}
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedD l Q).Valid)
    (hd : IsRankTwoPlus (.twistedD l Q)) (hnodd : Odd Q.exponent)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD l Q, hv⟩).Group) :
    K6Concl T T₁ T₂ Ls := by
  have hQ : Q.p = 2 := hd.1
  have hl4 : 4 ≤ l := hd.2
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even l Q hv hQ e
  rw [hQ] at hmodel
  obtain ⟨-, F, hF, hFfin, hcard, b, c, hirr, ⟨e'⟩⟩ := hmodel
  haveI := charP_two_of_card hcard
  rcases Nat.eq_or_lt_of_le hl4 with rfl | hl5
  · have hZ := center_eq_bot_of_ksmOdd hK ctx (d := ⟨.twistedD 4 Q, hv⟩) hQ
      (fun _ h => TauCeti.LieTypeIndex.noConfusion h)
      (fun _ h => TauCeti.LieTypeIndex.noConfusion h)
      (fun _ h => TauCeti.LieTypeIndex.noConfusion h) e
    refine Or.inr ⟨?_, hasLThreeCore_spinMinus_four hirr ctx.sylow ctx.cov inf_le_right
      inf_le_right ctx.s₁ ctx.s₂ ctx.r₁ ctx.r₂ hcard hnodd hZ e'⟩
    rw [pRank_Ls_eq hT ctx hd e]
    exact (mRank3_cases hd _).2.2.1.2 trivial
  · exfalso
    exact false_of_spinMinus hirr ctx.sylow ctx.cov inf_le_right inf_le_right ctx.r₁ ctx.r₂ hl5 e'

end TwistedD

section TwistedA

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}

theorem k6_TA (hKSMU4 : KSMU4) (ctx : K6Ctx T T₁ T₂ Ls) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA l Q).Valid) (hd : IsRankTwoPlus (.twistedA l Q))
    (hnodd : Odd Q.exponent)
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA l Q, hv⟩).Group) :
    K6Concl T T₁ T₂ Ls := by
  have hQ : Q.p = 2 := hd.1
  have hl3 : 3 ≤ l := hd.2
  rcases Nat.eq_or_lt_of_le hl3 with rfl | hl4
  · have hc := hKSMU4 ↥Ls ctx.quasi ⟨.twistedA 3 Q, hv⟩ ⟨Q, hQ, rfl⟩ ⟨e⟩ ctx.oddCenter
    exact Or.inl ⟨⟨.twistedA 3 Q, hv⟩, Q, hQ, hnodd, rfl,
      ⟨K541Proof.equiv_of_center_card_one hc e⟩⟩
  · exfalso
    have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA l Q hv e
    rw [hQ] at hmodel
    obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hmodel
    haveI : CharP F 2 := charP_two_of_card (k := Q.exponent * 2) (by rw [hcard, pow_mul])
    have h3 : 3 ∣ 2 ^ Q.exponent + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hnodd
    exact false_of_su ctx.quasi ctx.sylow ctx.cov inf_le_right inf_le_right ctx.r₁ ctx.r₂ hcard h3
      (by omega) e'

end TwistedA

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open K517Six KFactsPair CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Main

set_option linter.unusedSectionVars false


theorem k517_6_of_inputs (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (h4b : K517_4b) : K517_6 := by
  intro X _ _ T T₁ T₂ hX hgood Ls hY hinv hchev hrk hm₁ hm₂
  have ctx := K6Ctx.of_gn hX hgood hY hchev hrk hm₁ hm₂
  obtain ⟨-, hsh⟩ := hgood.shape Ls hY
  rcases hsh with ⟨hcl, hr1⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hcl with ⟨d, hdcl, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd7, ⟨e⟩⟩
    · have hd : IsRankTwoPlus d.1 := isRankTwoPlus_of_classical hdcl e hr1
      have hnd := not_dvd_indexQ h4b hX hgood hY hinv hd e hm₁ hm₂
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A l Q => exact (k6_A hT ctx hv hd (odd_exponent_of_not_dvd hd.1 hnd) e).elim
      | twistedA l Q => exact k6_TA hKSMU4 ctx hv hd (odd_exponent_of_not_dvd hd.1 hnd) e
      | B l Q => exact k6_B hT hKSMOdd ctx hv hd (odd_exponent_of_not_dvd hd.1 hnd) e
      | C l Q => exact hd.elim
      | D l Q => exact (k6_D ctx hv hd e).elim
      | twistedD l Q => exact k6_TD hT hKSMOdd ctx hv hd (odd_exponent_of_not_dvd hd.1 hnd) e
      | E6 Q => exact hd.elim
      | E7 Q => exact hd.elim
      | E8 Q => exact hd.elim
      | F4 Q => exact hd.elim
      | G2 Q => exact (k6_G2 hT ctx hv hd e).elim
      | twistedE6 Q => exact hd.elim
      | trialityD4 Q => exact hd.elim
      | suzuki Q => exact hd.elim
      | reeG2 Q => exact hd.elim
      | reeF4 Q => exact hd.elim
      | tits => exact hd.elim
    · exfalso
      have h1 := hT.alt ↥Ls ctx.quasi n (by omega) ⟨e⟩ 3 Nat.prime_three (by norm_num)
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ls] at h1
      have := ctx.rank
      rcases hn with rfl | rfl | rfl
      · exact hr1 (Or.inr ⟨e⟩)
      · omega
      · omega
    · exfalso
      obtain ⟨hl7, hu3⟩ := hT.small ↥Ls ctx.quasi 3 Nat.prime_three (by norm_num)
      have := ctx.rank
      rcases hd7 with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
      · have h1 := hl7 ⟨q, d, hq, hd, ⟨e⟩⟩
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ls] at h1
        simp at h1
        omega
      · have h1 := hu3 ⟨q, d, hq, hd, ⟨e⟩⟩
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ls] at h1
        simp at h1
        omega
  · exfalso
    have hrk' : 1 < CFSG.Open.pRank 3 (gnA T T₁ Ls) ∨ 1 < CFSG.Open.pRank 3 (gnA T T₂ Ls) := by
      rcases hn with rfl | ⟨h8, -⟩
      · exact hgood.alt7 Ls hY.1 hinv ⟨e⟩
      · exact hgood.altBig Ls hY.1 n h8 ⟨e⟩
    have h1 := ctx.r₁
    have h2 := ctx.r₂
    omega

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15
