module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291A3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Zero
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Np
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Constr
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Center

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt exists_char_pow_card
  mem_of_pow_eq_one_of_not_dvd_card_outer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)
open CFSG.AGLEmbedding (CatalogSimpleSections)

namespace L6KD291

theorem not_dvd_card_outer_alternating {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Type}
    [Group L] [Finite L] {n : ℕ} (hn5 : 5 ≤ n) (e : L ≃* alternatingGroup (Fin n)) :
    ¬ p ∣ Nat.card (Outer L) := by
  intro hd
  by_cases hn6 : n = 6
  · subst hn6
    have h2 : IsPGroup 2 (Outer L) :=
      CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six.of_equiv
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm
    haveI : Finite (Outer L) := inferInstance
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk] at hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
    omega
  · have h2 := outer_card_dvd_two_of_equiv_outside_six (by omega) e
    have := Nat.le_of_dvd (by norm_num) (hd.trans h2)
    omega

theorem exists_index_of_outer (hΔ : KDInndiagP5) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type}
    [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (hs : IsSimpleGroup L)
    (hn : ∃ a b : L, a * b ≠ b * a) (hc : IsCatalogGroup L) (hlu : ¬ IsLinearOrUnitaryAt p L)
    (hC : centralizer (L : Set Y) = ⊥) {x : Y} (hxL : x ∉ L) (hxo : orderOf x = p) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hxp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  refine exists_index_prime_of_focal_ne P fun hF => hxL ?_
  have hle := focalSubgroup_le_of_kdInndiag hΔ hp hp5 L hs hn hc hlu hC P
  rw [hF] at hle
  exact hle (hP (mem_zpowers x))

end L6KD291

section Data


namespace L6KD291

theorem inner_ident (hOut : SporadicOutOdd) (hR : SporadicCentralizerRank)
    (hAt : ∀ d : TauCeti.ValidLieTypeIndex, CrossAt d) (hDef : KD291DefCharL) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hs : IsSimpleGroup L) (hn : ∃ a b : L, a * b ≠ b * a) (hc : IsCatalogGroup L)
    (hl : ¬ IsLinearOrUnitaryAt p L) (hcen : centralizer (L : Set Y) = ⊥)
    (h3 : 3 ≤ Open.pRank p (⊤ : Subgroup Y)) {x : Y} (hxL : x ∈ L) (hxo : orderOf x = p)
    (hx2 : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) :
    StatedClassicalModel ↥L .PSp 2 p 1 ∨ ChevalleyExceptionalModel ↥L .G2 p 1 := by
  obtain ⟨i, ⟨e⟩⟩ := id hc
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hn
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn5 =>
    exfalso
    haveI := hs
    exact i294Alt_false hp hp5 L hn hn5 e hcen h3 hxL hxo hx2
  | sporadic s => exact (spor_false hOut hR hp hp5 L s e hcen h3 hxL hxo hx2).elim
  | lie m =>
    by_cases hch : m.1.characteristic = p
    · haveI : Fact p.Prime := ⟨hp⟩
      have hp1 : 1 < p := hp.one_lt
      have hL3 := le_pRank_L_of_defChar hp hp5 L m hch e hcen (by norm_num : 3 ≤ 4) h3
      have hxo' : orderOf (⟨x, hxL⟩ : ↥L) = p := by
        rw [← Subgroup.orderOf_coe]
        exact hxo
      have h5 : CFSG.Open.pRank p (centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) ≤
          CFSG.Open.pRank p (centralizer ({x} : Set Y)) := by
        refine (CFSG.SectionRank.pRank_le_map hp1 L.subtype L.subtype_injective _).trans
          (CFSG.SectionRank.pRank_mono hp1 ?_)
        rintro _ ⟨y, hy, rfl⟩
        have hy' : y ∈ centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := hy
        rw [Subgroup.mem_centralizer_singleton_iff] at hy'
        exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
      exact (hDef p hp hp5 ↥L hs hn ⟨m, hch, ⟨e⟩⟩ hL3 ⟨x, hxL⟩ hxo' (h5.trans hx2)).2
    · exact (cross_false hAt hp hp5 L hs hn hc m hch e hl hcen h3 hxL hxo hx2).elim

end L6KD291

theorem kdL64I291_of_data (hMult : KDMultP5) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hΔ : KDInndiagP5) (hOut : SporadicOutOdd) (hR : SporadicCentralizerRank)
    (hAt : ∀ d : TauCeti.ValidLieTypeIndex, CrossAt d) (hDef : KD291DefCharL)
    (hOuterLie : KD291OuterLie) (hOuterLin : KD291OuterLin) (hOuterUni : KD291OuterUni) :
    KDL64I291 := by
  intro p hprime hp5 Y _ _ hcat hcore L hL hLu h3 x hxo hxc
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp1 : 1 < p := hprime.one_lt
  have hLn : L.Normal := I291.normal_of_unique hL hLu
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLbot : L ≠ ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3.kd291_ne_bot_of_quasisimple L hq
  have hZp : IsPGroup p (center ↥L) := I291.isPGroup_center hcore hL
  have hcatQ : IsCatalogGroup (↥L ⧸ center ↥L) := hcat.isCatalogGroup_center_quotient hL
  have hxp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  have hxQ : x ∈ (Q : Subgroup Y) := hQ (mem_zpowers x)
  have hQrank : 3 ≤ Open.pRank p (Q : Subgroup Y) := by
    rw [(CFSG.SectionRank.pRank_sylow Q).1]
    exact h3
  obtain ⟨w, hwQ, hwo, hwc, hwu⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3.kd291_step0a hprime Q hxQ hxo hQrank hxc.le
  have hxp1 : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwo
    exact hprime.one_lt.ne hwo
  have cfg : K62B.Cfg p (Q : Subgroup Y) x w :=
    { prime := hprime
      five_le := hp5
      sylow := CFSG.ABGLocalTools.isSylowOf_iff.2
        ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
      x_mem := hxQ
      z_mem := hwQ
      x_pow := hxp1
      z_pow := hwo ▸ pow_orderOf_eq_one w
      z_ne_one := hw1
      z_central := hwc
      center_le := hwu
      rank_cent := fun E hEQ hE hEc => by
        obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hE
        have hEC : E ≤ centralizer ({x} : Set Y) := fun e he =>
          Subgroup.mem_centralizer_singleton_iff.2 (hEc e he)
        have hkr := CFSG.SectionRank.le_pRank hp1 hEC hE hk
        rw [hk]
        exact Nat.pow_le_pow_right hprime.pos (hkr.trans hxc.le)
      core := hcore
      catalog := hcat }
  by_cases hlu : IsLinearOrUnitaryAt p (↥L ⧸ center ↥L)
  ·
    have hZero := L6KD291.zero_of_cfg cfg hL hLu
    refine ⟨hZero.omega_le, Or.inl ?_⟩
    rcases hlu with ⟨n, K, _, _, hpn, hpK, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, hpn, hpq, ⟨e⟩⟩
    · by_cases hin : ∃ B : GL (Fin n) K,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K B =
          CFSG.LocalAnalysis.RankFourTheoremC.l212in_descend
            (e.trans (CFSG.LocalAnalysis.RankFourTheoremC.l212in_projectiveSLEquivStated n K).symm)
            (CFSG.LocalAnalysis.RankFourTheoremC.odC L x)
      · have hnp := L6KD291.linear_n_eq_p hGA hp5 L hq hZp hxo hxc.le hpn hpK e hin
        subst hnp
        exact Or.inl ⟨K, inferInstance, inferInstance, hpK, ⟨e⟩⟩
      · exfalso
        have := hOuterLin p hprime hp5 Y L hq hZp n K hpn hpK e x hxo hin
        omega
    · obtain ⟨r, m, hr, hchar, -, hKr⟩ := exists_char_pow_card K
      haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
        refine (Nat.dvd_prime_pow hr).1 ?_
        rw [← hKr, hKq]
        exact dvd_pow_self q two_ne_zero
      subst hqf
      by_cases hin : ∃ B : CFSG.ComponentClassification.CatalogueBUnitaryIsometry.Uid
          (CFSG.LieType.BorelTits.unitaryInvolution K r f) n,
          CFSG.LocalAnalysis.RankFourTheoremC.l212in_suPhi hKq B =
            CFSG.LocalAnalysis.RankFourTheoremC.l212in_descend e
              (CFSG.LocalAnalysis.RankFourTheoremC.odC L x)
      · have hnp := L6KD291.unitary_n_eq_p hGA hp5 L hq hZp hxo hxc.le hpn hKq hpq e hin
        subst hnp
        exact Or.inr (Or.inl ⟨r ^ f, K, inferInstance, inferInstance, hKq, hpq, ⟨e⟩⟩)
      · exfalso
        have := hOuterUni p hprime hp5 Y L hq hZp n r f K hpn hKq hpq e x hxo hin
        omega
  ·
    have hZ : center ↥L = ⊥ := by
      by_contra hZne
      exact hlu (hMult p hprime hp5 ↥L hq hcatQ hZne hZp)
    obtain ⟨hsimp, hnonab, hcatL⟩ := hcat.isSimpleGroup_of_center_eq_bot hL hZ
    have hpc := I291.pCore_eq_bot cfg hL hLn hZ
    have hC := I291.centralizer_eq_bot hcore hpc hL hLu hZ
    have hnlu : ¬ IsLinearOrUnitaryAt p ↥L := fun h => hlu (I291.isLinearOrUnitaryAt_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm h)
    refine ⟨fun y hy _ => ?_, ?_⟩
    · rw [hpc, Subgroup.mem_bot] at hy
      rw [hy]
      exact L.one_mem
    · by_cases hxL : x ∈ L
      · left
        have e0 : ↥L ≃* (↥L ⧸ center ↥L) :=
          ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
        rcases L6KD291.inner_ident hOut hR hAt hDef hprime hp5 L hsimp hnonab hcatL hnlu hC h3 hxL
          hxo hxc.le with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e0 h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e0.symm h))))
      · right
        have hxp1 : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
        have hL2pp : P64IsL2pp p ↥L := by
          obtain ⟨i, ⟨e⟩⟩ := id hcatL
          cases i with
          | cyclic r hr =>
            exfalso
            obtain ⟨a, b, hab⟩ := hnonab
            exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
          | alternating n hn5 =>
            exact (hxL (mem_of_pow_eq_one_of_not_dvd_card_outer hprime L hC
              (L6KD291.not_dvd_card_outer_alternating hprime hp5 hn5 e) hxp1)).elim
          | sporadic s =>
            have hout : ¬ p ∣ Nat.card (Outer ↥L) := by
              have h1 := hOut s p hprime (by omega)
              rwa [← Nat.card_congr
                (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv] at h1
            exact (hxL (mem_of_pow_eq_one_of_not_dvd_card_outer hprime L hC hout hxp1)).elim
          | lie m =>
            exact hOuterLie p hprime hp5 Y L hsimp hnonab hnlu ⟨m, ⟨e⟩⟩ hC h3 x hxL hxo hxc.le
        exact ⟨hL2pp,
          L6KD291.exists_index_of_outer hΔ hprime hp5 L hsimp hnonab hcatL hnlu hC hxL hxo⟩

end Data

section CertificateInstances


theorem kdL64I291_of_kdata (hDef : KD291DefCharL) (hOuterLie : KD291OuterLie)
    (hOuterLin : KD291OuterLin) (hOuterUni : KD291OuterUni) : KDL64I291 :=
  kdL64I291_of_data (kdMultP5_of_tables
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds kdInndiagP5_holds
    sporadicOutOdd_holds
    (sporadicCentralizerRank_of_data sporadicRankTable_holds
      (sporadicClassWitness_of_pairs sporadicClassWitnessAt_Co1_five sporadicClassWitnessAt_HN_five
        sporadicClassWitnessAt_Ly_five sporadicClassWitnessAt_B_five sporadicClassWitnessAt_M_five
        sporadicClassWitnessAt_M_seven))
    (crossAt_all
      (crossE7SevenSplit_of_rank
        RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
        crossRankE7SevenSplit_holds)
      (crossE8FiveFour_of_rank
        RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
        crossRankE8FiveFour_holds))
    hDef hOuterLie hOuterLin hOuterUni

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
