module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.RowHyps
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankNT1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512F

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open scoped commutatorElement

section Rows1314

variable {X : Type} [Group X] [Finite X]

theorem not_dvd_card_centre_of_in1512 (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K))) {d : TauCeti.ValidLieTypeIndex} (hd : In1512 d.1)
    (e : Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h5 : ∀ Q, d.1 = .twistedA 4 Q → p ≠ 5) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hpz
  by_cases hA2 : ∃ Q, d.1 = .A 2 Q
  · obtain ⟨Q, hQ⟩ := hA2
    have hQ2 : Q.p = 2 := by
      have := hd
      rw [hQ] at this
      exact this
    rcases Nat.even_or_odd Q.exponent with hev | hodd'
    · have h3 := (hKSML3 K hK d e hodd).2 ⟨Q, hQ2, hev, hQ⟩
      have := Nat.le_of_dvd (by norm_num) (hpz.trans h3)
      omega
    · have h1 := (hKSML3 K hK d e hodd).1 (Or.inl ⟨Q, hQ2, hodd', hQ⟩)
      rw [h1] at hpz
      exact hp.one_lt.ne' (Nat.dvd_one.1 hpz)
  by_cases hU3 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q
  · obtain ⟨Q, hQ⟩ := hU3
    have hQ2 : Q.p = 2 := by
      have := hd
      rw [hQ] at this
      exact this
    have h1 := hKSMU4 K hK d ⟨Q, hQ2, hQ⟩ e hodd
    rw [h1] at hpz
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpz)
  push Not at hA2 hU3
  have hmain := hKSMOdd.1 K hK d hd hA2 hU3 e hodd
  by_cases hU5 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 4 Q
  · obtain ⟨Q, hQ⟩ := hU5
    have h3 := hmain.1 ⟨Q, hQ⟩
    exact h5 Q hQ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hpz.trans h3))
  · push Not at hU5
    have h1 := hmain.2 hU5
    rw [h1] at hpz
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpz)

theorem normal_of_lie (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) {G : Type} [Group G]
    [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) {p : ℕ}
    (hp : p ∈ sigmaM G M) (hp5 : 5 ≤ p)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {d : TauCeti.ValidLieTypeIndex} (hd : In1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (h5 : ∀ Q, d.1 = .twistedA 4 Q → p ≠ 5) (h2 : 2 ≤ CFSG.Open.pRank p L) : Ls.Normal := by
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift ctx.gn hLs.1 hL
  obtain ⟨e'⟩ := e
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hZ := not_dvd_card_centre_of_in1512 hKSMOdd hKSMU4 hKSML3 hK (centre_barO2_odd hL.1) hd
    ⟨eQ.trans e'⟩ hpP hp5 h5
  exact (lift_normal_of_two_le_pRank hL hpP hp2 (ctx.rank_odd p hpP hp2) h2 hZ).2

theorem false_of_dvd_sub_one (hK4b : K517_4b) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T))) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsRankTwoPlus d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ indexQ d.1 - 1)
    (h₁ : CFSG.Open.pRank q (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank q (Subgroup.normalizer (T₂ : Set X)) ≤ 1) : False := by
  rcases hK4b X T T₁ T₂ hX hg Ls hLs hinv d hd e q hq hdvd with h | h
  · have := two_le_pRank_normalizer_of_gnA T T₁ Ls hq hq2 h
    omega
  · have := two_le_pRank_normalizer_of_gnA T T₂ Ls hq hq2 h
    omega

theorem exists_other_of_isUFour_gen (hK4a : K517_4a) (hK518 : K518) (hKSMU4 : KSMU4) {G : Type}
    [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂)
    {p : ℕ} (hp : p ∈ sigmaM G M) (hp5 : 5 ≤ p)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hU : IsUFour (fun Q => p ∣ Q + 1) ↥Ls) :
    ∃ Is : Subgroup (↥M ⧸ gnC (T.subgroupOf M)),
      GNYComponent (T.subgroupOf M) T₁ T₂ Is ∧ Is ≠ Ls ∧ p ∣ Nat.card ↥Is := by
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hU' := hU
  obtain ⟨Q, hQ2, hdvd, d, hd, ⟨e⟩⟩ := hU
  have hbot : Subgroup.center ↥Ls = ⊥ := lift_inf_gnC_le_pCore_of_U4_aux2 hQ2 hd e
  have eLsq : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot.trans e)
  have hZs : ¬ p ∣ Nat.card (Subgroup.center ↥Ls) := by
    rw [hbot, Subgroup.card_bot]
    exact fun h => hpP.one_lt.ne' (Nat.dvd_one.1 h)
  have hdr : IsRankTwoPlus d.1 := by
    rw [hd]
    exact ⟨hQ2, le_refl 3⟩
  have hdv : p ∣ indexQ d.1 ^ 2 - 1 := by
    rw [hd]
    exact dvd_sq_sub_one_of_dvd_add_one_s15 hdvd
  obtain ⟨hp1, hp2'⟩ := hK4a ↥M (T.subgroupOf M) T₁ T₂ ctx.gn (S15CtxGen.good ctx) Ls hLs d
    hdr ⟨eLsq⟩ p hpP hdv
  have hinv := gnImg_le_normalizer_of_dvd_gnA (IsGNPair.le_normalizer₁ ctx.pair) hpP hp2
    (ctx.rank_N₁ p hp) hLs.1 hZs hp1
  obtain ⟨m1, n1⟩ := mS_mN_eq_one_of_dvd hpP hp2 (ctx.rank_N₁ p hp) Ls hp1
  obtain ⟨m2, n2⟩ := mS_mN_eq_one_of_dvd hpP hp2 (ctx.rank_N₂ p hp) Ls hp2'
  obtain ⟨hC, hle⟩ := hK518 ↥M (T.subgroupOf M) T₁ T₂ ctx.gn (S15CtxGen.good ctx) p hpP hp2 Ls
    L hLs hL hinv m1 m2 n1 n2
  by_contra hnone
  push Not at hnone
  have hle' := hle hnone
  have hy := not_pElementSubgroup_le_centre hpP
    (inf_le_right : gnA (T.subgroupOf M) T₁ Ls ≤ Ls) hZs hp1
  have hnorm : Ls.Normal := normal_of_pElement_le_comap_at hpP hLs.1 hle' hy
  have hdata := u4DataAt_of_lift hKSMU4 hpP ctx.gn hLs.1 hnorm hL hC hle' hy hU'
  exact ctx.noU4 p hp (u4Shape_of_u4DataAt M p hdata)

theorem exists_other_of_isUFour (hK4a : K517_4a) (hK518 : K518) (hKSMU4 : KSMU4) {G : Type}
    [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂)
    {p : ℕ} (hp : p ∈ sigmaM G M) (hp5 : 5 ≤ p)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hU : IsUFour (fun Q => p ∣ Q + 1) ↥Ls) (h2 : 2 ≤ CFSG.Open.pRank p L) :
    ∃ Is : Subgroup (↥M ⧸ gnC (T.subgroupOf M)),
      GNYComponent (T.subgroupOf M) T₁ T₂ Is ∧ Is ≠ Ls ∧ p ∣ Nat.card ↥Is :=
  exists_other_of_isUFour_gen hK4a hK518 hKSMU4 (S15CtxGen.of_ctx2 ctx) hp hp5 hLs hL hU

theorem three_dvd_card_gnA_of_gnYComponent {T T₁ T₂ : Subgroup X} (hthree : GNThree T T₁ T₂)
    {I : Subgroup (X ⧸ gnC T)} (hI : GNYComponent T T₁ T₂ I) : 3 ∣ Nat.card (gnA T T₁ I) := by
  obtain ⟨y, hyA, hyZ, k, hk⟩ := exists_pElement_not_mem 3 _ _ (hthree I hI).1
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ one_mem _)
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.1 (by simpa using hk))
  have h1 : orderOf y ∣ Nat.card (gnA T T₁ I) := by
    rw [← Subgroup.orderOf_mk y hyA]
    exact orderOf_dvd_natCard _
  rw [hk] at h1
  exact (dvd_pow_self 3 hk1).trans h1

theorem pRank_center_barO2_le_zero {L : Subgroup X} {q : ℕ} (hq : q.Prime)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center ↥(barO2 L))) :
    CFSG.Open.pRank q ((Subgroup.center ↥(barO2 L)).map (barO2 L).subtype) ≤ 0 := by
  by_contra hlt
  push Not at hlt
  have h1 := (one_le_pRank_iff_dvd _ hq).1 hlt
  rw [Subgroup.card_map_of_injective (barO2 L).subtype_injective] at h1
  exact hZ h1

theorem sl3_of_pRank_three_eq_one (hT : LieOddRankTable) (hK541 : K541) {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hshape : GNShape T T₁ T₂) {Is : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hIs : GNYComponent T T₁ T₂ Is) (hL : LiftOf T L Is) (h1 : CFSG.Open.pRank 3 L = 1) :
    ∃ m : ℕ, Odd m ∧ 0 < m ∧
      Nonempty (↥Is ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 m)) := by
  have hcomm := (hshape Is hIs).1
  rcases rankDatum hT hX hshape hIs hL with ⟨d, hdr, ⟨e⟩, hr⟩ | ⟨n, hn, e, hr⟩ | ⟨n, hn, e, hr⟩ |
    ⟨⟨d, q, hq, hd, ⟨e⟩⟩, -⟩ | ⟨⟨d, q, hq, hd, e⟩, hr⟩
  · have hval : mRankChev d.1 3 (Nat.card (Subgroup.center ↥(barO2 L))) = 1 :=
      (hr 3 Nat.prime_three (by norm_num)).symm.trans h1
    have hrank1 : RankOneList d.1 := ((mRank3_cases hdr _).1).1 hval
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A l Q =>
      rcases l with _ | _ | _ | l
      · exact (hrank1 : False).elim
      · exact (hrank1 : False).elim
      · have hQ : Q.p = 2 := hdr.1
        exact ⟨Q.exponent, hrank1, Q.exponent_pos,
          hK541 X T hX Is hIs.1 hcomm Q.exponent (isLThreeOfExp_of_A2 hQ rfl e)⟩
      · exact (hrank1 : False).elim
    | _ => exact (hrank1 : False).elim
  · exfalso
    have h := hr 3 Nat.prime_three (by norm_num)
    rcases hn with rfl | rfl <;> omega
  · exfalso
    have h := hr 3 Nat.prime_three (by norm_num)
    rcases hn with rfl | ⟨h8, -⟩ <;> omega
  · exact ⟨1, odd_one, one_pos,
      hK541 X T hX Is hIs.1 hcomm 1 (Or.inl ⟨rfl, d, q, hq, hd, ⟨e⟩⟩)⟩
  · exfalso
    have h := hr 3 Nat.prime_three (by norm_num)
    simp at h
    omega

theorem false_of_other_component_isUFour_gen (hT : LieOddRankTable) (hKSMU4 : KSMU4) (hK541 : K541)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) (hLift : RowLifts G M T T₁ T₂) {p : ℕ} (hp : p ∈ sigmaM G M)
    (hp5 : 5 ≤ p) {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hU : IsUFour (fun Q => p ∣ Q + 1) ↥Ls) {Is : Subgroup (↥M ⧸ gnC (T.subgroupOf M))}
    (hIs : GNYComponent (T.subgroupOf M) T₁ T₂ Is) (hne : Is ≠ Ls) (hpI : p ∣ Nat.card ↥Is)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3) : False := by
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  obtain ⟨LI, hLI⟩ := hLift Is hIs
  obtain ⟨Q, hQ2, hdvd, d, hd, ⟨e⟩⟩ := hU
  have hbot : Subgroup.center ↥Ls = ⊥ := lift_inf_gnC_le_pCore_of_U4_aux2 hQ2 hd e
  have eLsq : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot.trans e)
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift ctx.gn hLs.1 hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hZL : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
    hKSMU4 ↥(barO2 L) hK d ⟨Q, hQ2, hd⟩ ⟨eQ.trans eLsq⟩ (centre_barO2_odd hL.1)
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barO2 L)) := by
    rw [hZL]
    omega
  have hclass : IsClassicalOrG2Index d.1 := by
    rw [hd]
    exact hQ2
  have hrk := pRank_lift_eq_chev hT ctx.gn hLs.1 hL hclass ⟨eLsq⟩ Nat.prime_three (by norm_num)
  rw [hd] at hrk
  have hm3 := u4_three_rank hQ2 (Nat.card (Subgroup.center ↥(barO2 L)))
  have h3I : 3 ∣ Nat.card ↥Is :=
    (three_dvd_card_gnA_of_gnYComponent ctx.gnThree hIs).trans
      (Subgroup.card_dvd_of_le inf_le_right)
  have h3LI : 3 ∣ Nat.card ↥LI := by
    have h := Subgroup.card_map_dvd LI (toStar (T.subgroupOf M))
    rw [hLI.2] at h
    exact h3I.trans h
  have h1LI : 1 ≤ CFSG.Open.pRank 3 LI := one_le_pRank_of_dvd _ Nat.prime_three h3LI
  have hneL : L ≠ LI := by
    intro h
    apply hne
    rw [← hLI.2, ← h, hL.2]
  have hsum := pRank_add_le_pRank_sup hL.1 hLI.1 hneL Nat.prime_three (by norm_num)
    (pRank_center_barO2_le_zero Nat.prime_three hZ3)
  have hX3 : CFSG.Open.pRank 3 (L ⊔ LI) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans h3
  have hL2 : CFSG.Open.pRank 3 L = 2 := by omega
  have hLI1 : CFSG.Open.pRank 3 LI = 1 := by omega
  have hEven : Even Q.exponent := hm3.2 (by omega)
  obtain ⟨m, hm, hm0, ⟨eS⟩⟩ := sl3_of_pRank_three_eq_one hT hK541 ctx.gn ctx.shape hIs hLI hLI1
  have hpdiv : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 m)) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpI
  have hpd := dvd_of_dvd_card_SL3 hpP hp2 hm0 hpdiv
  have hp2n : p ∣ 2 ^ Q.exponent + 1 := by
    rw [← hQ2, ← TauCeti.PrimePower.card_def]
    exact hdvd
  exact not_dvd_of_even_odd hEven hm hpP hp2 hp2n hpd

theorem false_of_other_component_isUFour (hT : LieOddRankTable) (hKSMU4 : KSMU4) (hK541 : K541)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (hLift : RowLifts G M T T₁ T₂) {p : ℕ} (hp : p ∈ sigmaM G M)
    (hp5 : 5 ≤ p) {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hU : IsUFour (fun Q => p ∣ Q + 1) ↥Ls) {Is : Subgroup (↥M ⧸ gnC (T.subgroupOf M))}
    (hIs : GNYComponent (T.subgroupOf M) T₁ T₂ Is) (hne : Is ≠ Ls) (hpI : p ∣ Nat.card ↥Is) :
    False :=
  false_of_other_component_isUFour_gen hT hKSMU4 hK541 (S15CtxGen.of_ctx2 ctx) hLift hp hp5
    hLs hL hU hIs hne hpI (ctx.rank_odd 3 Nat.prime_three (by norm_num))

theorem rowNotDvdSubOne_of_ctx2 (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    (hK4b : K517_4b) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) :
    RowNotDvdSubOne G M T T₁ T₂ := by
  intro p hp hp5 Ls L hLs hL h2 d hdr hd h5 e hdvd
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hinv := gnImg_le_normalizer_of_normal
    (normal_of_lie hKSMOdd hKSMU4 hKSML3 ctx hp hp5 hLs hL hd e h5 h2)
  exact false_of_dvd_sub_one hK4b ctx.gn (S15Ctx2.good ctx) hLs hinv hdr e hpP hp2 hdvd
    (ctx.rank_N₁ p hp) (ctx.rank_N₂ p hp)

theorem rowNotDvdSubOne_of_ctxGen (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    (hK4a : K517_4a) (hK4b : K517_4b) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) :
    RowNotDvdSubOne G M T T₁ T₂ := by
  intro p hp hp5 Ls L hLs hL h2 d hdr hd h5 e hdvd
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  obtain ⟨⟨eQ⟩, hzdvd, -⟩ := centre_of_lift ctx.gn hLs.1 hL
  have hZbar : ¬ p ∣ Nat.card (Subgroup.center ↥(barO2 L)) :=
    not_dvd_card_centre_of_in1512 hKSMOdd hKSMU4 hKSML3 hL.1.component.2.2
      (centre_barO2_odd hL.1) hd ⟨eQ.trans e.some⟩ hpP hp5 h5
  have hZs : ¬ p ∣ Nat.card (Subgroup.center ↥Ls) := fun h => hZbar (h.trans hzdvd)
  have hdv : p ∣ indexQ d.1 ^ 2 - 1 :=
    hdvd.trans (Nat.sub_one_dvd_pow_sub_one (indexQ d.1) 2)
  have hp1 : p ∣ Nat.card (gnA (T.subgroupOf M) T₁ Ls) :=
    (hK4a ↥M (T.subgroupOf M) T₁ T₂ ctx.gn (S15CtxGen.good ctx) Ls hLs d hdr e p hpP hdv).1
  have hinv := gnImg_le_normalizer_of_dvd_gnA (IsGNPair.le_normalizer₁ ctx.pair) hpP hp2
    (ctx.rank_N₁ p hp) hLs.1 hZs hp1
  exact false_of_dvd_sub_one hK4b ctx.gn (S15CtxGen.good ctx) hLs hinv hdr e hpP hp2 hdvd
    (ctx.rank_N₁ p hp) (ctx.rank_N₂ p hp)

end Rows1314

end CFSG.LocalAnalysis.RankThreeUC.S15
