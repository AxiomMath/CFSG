module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.RowHyps
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C5
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KParU5Holds

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15

theorem not_mem_sigma_five_of_u5 {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hc : Q.card = 4) (hd : d.1 = .twistedA 4 Q)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    5 ∉ sigmaM G M := by
  intro h5
  rcases two_le_mN_of_u5 KParU5_holds ctx.gn (S15CtxGen.good ctx) hLs.1 hQ hc hd e with h | h
  · exact (Nat.not_lt.2 (ctx.rank_N₁ 5 h5)) h
  · exact (Nat.not_lt.2 (ctx.rank_N₂ 5 h5)) h

theorem row1512_of_datum (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSMAlt : KSMAlt) (hK541 : K541)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) (h12 : Row1512Datum G M T T₁ T₂) :
    Row1512 G M T T₁ T₂ := by
  intro Ls L hLs hL
  have h5 : ∀ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 →
      Q.card = 4 → d.1 = .twistedA 4 Q →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      CFSG.Open.pRank 5 L ≤ 3 := by
    intro d Q hQ hc hd e
    by_cases hσ : 5 ∈ sigmaM G M
    · exact absurd hσ (not_mem_sigma_five_of_u5 ctx hLs hQ hc hd e)
    · have hσ' : 5 ∉ sigmaSet G M := by
        simpa [sigmaM_eq_sigmaSet] using hσ
      exact (CFSG.SectionRank.pRank_mono Nat.prime_five.one_lt le_top).trans
        (ctx.rank_odd_off 5 Nat.prime_five (by norm_num) hσ')
  refine ⟨isGroupOf1512_of_datum_gen hKSMOdd hKSMU4 hKSMAlt hK541 ctx.gn ctx.shape hLs hL
    (h12 Ls L hLs hL) h5, ?_⟩
  intro hU h5σ
  obtain ⟨d, Q, hQ, hc, hd, e⟩ := quotCenter_of_isUFiveFour hU
  exact not_mem_sigma_five_of_u5 ctx hLs hQ hc hd e h5σ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
