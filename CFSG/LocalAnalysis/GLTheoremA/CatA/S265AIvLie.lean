module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAlpha
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInnMain
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner_le_innAutDerived)


theorem ivLieRow_holds : IvLieRow := by
  intro Ω _ _ S B T x D K cfg hK6 hr
  have hpre := cfg.std
  obtain ⟨d0, hdD, hdnot⟩ := S171.exists_y Nat.prime_three cfg.x1 hpre
  have hdB : d0 ∈ B := hpre.1 hdD
  have hdN : d0 ∈ Subgroup.normalizer (S : Set Ω) := cfg.inn.1 hdB
  have hd3 : d0 ^ 3 = 1 := hpre.2.1.2 d0 hdD
  have hLx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun l _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen l)
  have hKcomp : IsComponentOf K (S ⊓ Subgroup.centralizer ({d0} : Set Ω)) := by
    rw [← S171.L_cs_eq Nat.prime_three cfg.x1 hpre hdD hdnot hLx]
    exact hpre.2.2.2.2.2.1
  obtain ⟨e6⟩ := CatB.bridge_sp6two hK6
  have hc6 : Nat.card (PSimple 3 K) = 1451520 :=
    (Nat.card_congr e6.toEquiv).trans CatB.U4Sp8.card_sp_three
  have h3K : 3 ∣ Nat.card K :=
    (show 3 ∣ Nat.card (PSimple 3 K) by rw [hc6]; norm_num).trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))
  have hKglap : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({d0} : Set Ω)) K :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf hKcomp h3K
  have hqS := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three cfg.comp
  obtain ⟨labL, hLabQuot, hinDiag⟩ := I141F.innDiagKind_chevAut hdN hqS
    (S10.innDiagOn_mono cfg.inn (Subgroup.zpowers_le.2 hdB))
  have hcenPS : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hqS
  obtain ⟨hsPS, hncPS⟩ := chev_pSimple_simple_nonabelian Nat.prime_three cfg.comp
  have hLabPS : Y10F.HasLabel (PSimple 3 S) (· = labL) :=
    Y10F.hasLabel_of_equiv_centerQuot
      (@CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple _ _ hsPS hncPS).1
      ((QuotientGroup.quotientMulEquivOfEq hcenPS).trans QuotientGroup.quotientBot).symm hLabQuot
  have hαpow := chevAut_pow_eq_one 3 S hdN hd3
  have hαder : chevAut 3 S ⟨d0, hdN⟩ ∈ innAutDerived (PSimple 3 S) := by
    by_cases hB2 : labL.tag = .B2der
    · exact inner_le_innAutDerived _ (T171S.inner_of_hasLabel_B2der hLabPS hcenPS hB2 hαpow)
    by_cases hG2 : labL.tag = .G2der
    · exact inner_le_innAutDerived _ (T171S.inner_of_hasLabel_G2der hLabPS hcenPS hG2 hαpow)
    by_cases hTw : labL.tag = .twF4der
    · exact inner_le_innAutDerived _ (T171S.inner_of_hasLabel_twF4der hLabPS hcenPS hTw hαpow)
    exact I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcenPS ⟨hB2, hG2, hTw⟩
      hinDiag
  have hαne : chevAut 3 S ⟨d0, hdN⟩ ≠ 1 := fun h1 =>
    hdnot ((cfg.centB d0 hdB).1 ((chevAut_eq_one_iff Nat.prime_three cfg.comp hdN).1 h1))
  have hd3p := isPGroup_zpowers_of_pow_eq_one hd3
  obtain ⟨eKJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hdN hd3p hKglap
  have hC : H1431c.CompOfType (PSimple 3 S) (chevAut 3 S ⟨d0, hdN⟩) S9.isSp6two := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hK6
    exact ⟨_, glaPComponent_chevTransfer Nat.prime_three hdN hd3p hKglap,
      ⟨i, hi, ⟨eKJ.symm.trans f⟩⟩⟩
  rcases cfg.chev with ⟨i, hi, ⟨eS⟩⟩ | ⟨i, hi, ⟨eS⟩⟩
  · cases i with
    | lie d =>
      have hchar : d.1.characteristic = 2 := hi
      have hf := (H1431c.lieSInn_holds (PSimple 3 S) hsPS hncPS d hchar ⟨eS⟩ _ hαder hαpow
        hαne).1 hC
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hrk : GLATwoLocalRank 3 ↥(S ⊔ B) ≤ 4 :=
        (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le Nat.prime_three
          (S ⊔ B)).trans ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1
            (cfg.rank.trans (by rw [hr, hpre.2.2.1]; norm_num)))
      have hRk := CFSG.HardMathSupport.Dickson.Sec6.I1431.rkY_of_ambient hrk cfg.elem cfg.xB
        cfg.x1 (Subgroup.mem_centralizer_iff.2 fun g _ => cfg.xcen g)
      rcases (H1431c.lieSTwo_holds (PQuot 3 S) hqS (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3)
        hRk d hchar hf ⟨eS⟩ _ hαder hαpow hαne).1 hC with h | h
      · exact Or.inl ⟨.lie d, h, ⟨eS⟩⟩
      · exact Or.inr ⟨.lie d, h, ⟨eS⟩⟩
    | _ => exact hi.elim
  ·
    have h1 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c.card_le_of_ambiguousChev_two
      hi eS
    have h2 : Nat.card (PSimple 3 (chevTransfer 3 S K)) ∣ Nat.card (PSimple 3 S) :=
      (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_quotient_dvd_card _).trans
        (Subgroup.card_subgroup_dvd_card _))
    rw [← Nat.card_congr eKJ.toEquiv, hc6] at h2
    have h3 := Nat.le_of_dvd Nat.card_pos h2
    omega

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
