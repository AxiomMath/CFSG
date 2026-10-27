module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KCoverSU6
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KParU7
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1512List
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512H
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixGlue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15

theorem mem_sigmaSet_of_four_le_pRank {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) {L : Subgroup ↥M} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (h4 : 4 ≤ CFSG.Open.pRank q L) : q ∈ sigmaSet G M := by
  by_contra hqσ
  have hmono : CFSG.Open.pRank q L ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥M) :=
    CFSG.SectionRank.pRank_mono hq.one_lt le_top
  have h3 := ctx.rank_odd_off q hq hq2 hqσ
  omega

theorem false_of_res1512_lin (hK4b : K517_4b) (hKSMRes : KSMRes)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {d : TauCeti.ValidLieTypeIndex} (hres : Res1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hr : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L))))
    {l : ℕ} {Q : TauCeti.PrimePower} (hdl : d.1 = .A l Q) : False := by
  have hresA : Res1512 (.A l Q) := hdl ▸ hres
  have hresA' := hresA
  obtain ⟨-, -, hQ2, hodd, -⟩ := hresA'
  obtain ⟨q, hq, hq2, hqd, hq4⟩ :=
    exists_prime_four_le_of_res1512_A hresA (Nat.card (Subgroup.center ↥(barO2 L)))
  have hq4' : 4 ≤ CFSG.Open.pRank q L := by
    rw [hr q hq hq2, hdl]
    exact hq4
  have hqσ : q ∈ sigmaSet G M := mem_sigmaSet_of_four_le_pRank ctx hq hq2 hq4'
  have h3M : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3 :=
    ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11
  have hL2 : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [hr 3 Nat.prime_three (by norm_num), hdl]
    exact two_le_mRankChev_three_of_res1512 hresA _
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift ctx.gn hLs.1 hL
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barO2 L)) :=
    hKSMRes ↥(barO2 L) hL.1.component.2.2 d l Q hQ2 (Or.inl ⟨hdl, hodd⟩)
      ⟨eQ.trans e.some⟩ (centre_barO2_odd hL.1)
  have hinv : gnImg (T.subgroupOf M) (T.subgroupOf M) ≤
      Subgroup.normalizer (Ls : Set (↥M ⧸ gnC (T.subgroupOf M))) :=
    gnImg_le_normalizer_of_normal
      (lift_normal_of_two_le_pRank hL Nat.prime_three (by norm_num) h3M hL2 hZ3).2
  have hdvd : q ∣ CFSG.LocalAnalysis.RankThreeUC.S15.KFactsPair.indexQ d.1 - 1 := by
    rw [hdl]
    exact hqd
  exact false_of_dvd_sub_one hK4b ctx.gn (S15CtxGen.good ctx) hLs hinv
    (hdl.symm ▸ isRankTwoPlus_of_res1512 hresA) e hq hq2 hdvd
    (ctx.rank_N₁ q hqσ) (ctx.rank_N₂ q hqσ)

theorem false_of_res1512_u5 {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls)
    {d : TauCeti.ValidLieTypeIndex} (hres : Res1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hr : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L))))
    {Q : TauCeti.PrimePower} (hdQ : d.1 = .twistedA 4 Q) : False := by
  have hresQ : Res1512 (.twistedA 4 Q) := hdQ ▸ hres
  have hresQ' := hresQ
  obtain ⟨-, -, hQ2, -, -⟩ := hresQ'
  obtain ⟨q, hq, hq2, hqd, hq4⟩ :=
    exists_prime_four_le_of_res1512_twistedA hresQ (Nat.card (Subgroup.center ↥(barO2 L)))
  have hq4' : 4 ≤ CFSG.Open.pRank q L := by
    rw [hr q hq hq2, hdQ]
    exact hq4
  have hqσ : q ∈ sigmaSet G M := mem_sigmaSet_of_four_le_pRank ctx hq hq2 hq4'
  have hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) := by
    obtain ⟨e'⟩ := e
    exact Or.inl ⟨d, by rw [hdQ]; exact hQ2, ⟨e'⟩⟩
  obtain ⟨P, hP, hrk⟩ :=
    KParU5_holds ↥M (T.subgroupOf M) ctx.gn Ls hLs.1 d Q hQ2 hdQ e
  have h2 : 2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P) := hrk q hq hqd
  rcases one_lt_mN_of_minOverBorel (S15CtxGen.good ctx) hLs.1 hchev hP hq hq2 h2 with h | h
  · exact (Nat.not_lt.2 (ctx.rank_N₁ q hqσ)) h
  · exact (Nat.not_lt.2 (ctx.rank_N₂ q hqσ)) h

theorem false_of_res1512_u6 {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls)
    {d : TauCeti.ValidLieTypeIndex} (hres : Res1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hr : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L))))
    {Q : TauCeti.PrimePower} (hdQ : d.1 = .twistedA 5 Q) : False := by
  have hresQ : Res1512 (.twistedA 5 Q) := hdQ ▸ hres
  have hresQ' := hresQ
  obtain ⟨-, -, hQ2, hev, -⟩ := hresQ'
  obtain ⟨q, hq, hq2, hqd, hq4⟩ :=
    exists_prime_four_le_of_res1512_twistedA hresQ (Nat.card (Subgroup.center ↥(barO2 L)))
  have hq4' : 4 ≤ CFSG.Open.pRank q L := by
    rw [hr q hq hq2, hdQ]
    exact hq4
  have hqσ : q ∈ sigmaSet G M := mem_sigmaSet_of_four_le_pRank ctx hq hq2 hq4'
  have hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) := by
    obtain ⟨e'⟩ := e
    exact Or.inl ⟨d, by rw [hdQ]; exact hQ2, ⟨e'⟩⟩
  have hcov : CoveredByTwo Ls (gnImg (T.subgroupOf M) (T.subgroupOf M) ⊓ Ls)
      (gnA (T.subgroupOf M) T₁ Ls) (gnA (T.subgroupOf M) T₂ Ls) :=
    coveredByTwo_gnA (S15CtxGen.good ctx) hLs.1 hchev
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (gnImg (T.subgroupOf M) (T.subgroupOf M) ⊓ Ls) Ls :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
      ctx.gn.sylow hLs.1.2.1
  have h2 := KCoverSU6_holds (↥M ⧸ gnC (T.subgroupOf M)) Ls
    (gnImg (T.subgroupOf M) (T.subgroupOf M) ⊓ Ls)
    (gnA (T.subgroupOf M) T₁ Ls) (gnA (T.subgroupOf M) T₂ Ls)
    hLs.1.2.2 hsyl hcov inf_le_right inf_le_right d Q hQ2 hev hdQ e q hq hqd
  rcases h2 with h | h
  · have h3 : 1 < CFSG.Open.pRank q (Subgroup.normalizer (T₁ : Set ↥M)) :=
      two_le_pRank_normalizer_of_gnA (T.subgroupOf M) T₁ Ls hq hq2 (by omega)
    exact (Nat.not_lt.2 (ctx.rank_N₁ q hqσ)) h3
  · have h3 : 1 < CFSG.Open.pRank q (Subgroup.normalizer (T₂ : Set ↥M)) :=
      two_le_pRank_normalizer_of_gnA (T.subgroupOf M) T₂ Ls hq hq2 (by omega)
    exact (Nat.not_lt.2 (ctx.rank_N₂ q hqσ)) h3

theorem false_of_res1512_u7 {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls)
    {d : TauCeti.ValidLieTypeIndex} (hres : Res1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hr : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L))))
    {Q : TauCeti.PrimePower} (hdQ : d.1 = .twistedA 6 Q) : False := by
  have hresQ : Res1512 (.twistedA 6 Q) := hdQ ▸ hres
  have hresQ' := hresQ
  obtain ⟨-, -, hQ2, -, -⟩ := hresQ'
  obtain ⟨q, hq, hq2, hqd, hq4⟩ :=
    exists_prime_four_le_of_res1512_twistedA hresQ (Nat.card (Subgroup.center ↥(barO2 L)))
  have hq4' : 4 ≤ CFSG.Open.pRank q L := by
    rw [hr q hq hq2, hdQ]
    exact hq4
  have hqσ : q ∈ sigmaSet G M := mem_sigmaSet_of_four_le_pRank ctx hq hq2 hq4'
  have hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) := by
    obtain ⟨e'⟩ := e
    exact Or.inl ⟨d, by rw [hdQ]; exact hQ2, ⟨e'⟩⟩
  obtain ⟨P, hP, hrk⟩ :=
    KParU7_holds ↥M (T.subgroupOf M) ctx.gn Ls hLs.1 d Q hQ2 hdQ e
  have h2 : 2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P) := hrk q hq hqd
  rcases one_lt_mN_of_minOverBorel (S15CtxGen.good ctx) hLs.1 hchev hP hq hq2 h2 with h | h
  · exact (Nat.not_lt.2 (ctx.rank_N₁ q hqσ)) h
  · exact (Nat.not_lt.2 (ctx.rank_N₂ q hqσ)) h

theorem false_of_res1512 (hK4b : K517_4b) (hKSMRes : KSMRes)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {d : TauCeti.ValidLieTypeIndex} (hres : Res1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hr : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L)))) : False := by
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | A l Q =>
    exact false_of_res1512_lin hK4b hKSMRes ctx h11 hLs hL hres e hr rfl
  | twistedA l Q =>
    have hl : l = 4 ∨ l = 5 ∨ l = 6 := by
      have h := hres
      obtain ⟨h4, h6, -⟩ := h
      omega
    rcases hl with rfl | rfl | rfl
    · exact false_of_res1512_u5 ctx hLs hres e hr rfl
    · exact false_of_res1512_u6 ctx hLs hres e hr rfl
    · exact false_of_res1512_u7 ctx hLs hres e hr rfl
  | _ => exact hres.elim

theorem row1512Datum_of_ctxGen (hT : LieOddRankTable) (hK4b : K517_4b) (hKSMRes : KSMRes)
    {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) : Row1512Datum G M T T₁ T₂ := by
  intro Ls L hLs hL
  exact rankDatum1512_of_rankDatum_gen (rankDatum hT ctx.gn ctx.shape hLs hL)
    ((CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans
      (ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11))
    (fun d hres e hr => false_of_res1512 hK4b hKSMRes ctx h11 hLs hL hres e hr)

theorem row1512_of_ctxGen (hT : LieOddRankTable) (hK4b : K517_4b) (hKSMRes : KSMRes)
    (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSMAlt : KSMAlt) (hK541 : K541)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) : Row1512 G M T T₁ T₂ :=
  row1512_of_datum hKSMOdd hKSMU4 hKSMAlt hK541 ctx
    (row1512Datum_of_ctxGen hT hK4b hKSMRes ctx h11)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
