module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.BorelDataP
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Data
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Abelian
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcEndgame
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Ctx
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.Yardstones.Md8ed6d263d89 Subgroup

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G}

theorem four_le_pRank_inf_centralizer_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) :
    4 ≤ Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  by_contra hlt
  have hlt3 : Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ≤ 3 := by omega
  have hQ3 : ∀ B : Subgroup G, B ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
      IsElemAbelian p B → Nat.card B ≤ p ^ 3 := by
    intro B hB hBel
    have hBp : IsPGroup p B := fun g => ⟨1, by simpa using Subtype.ext (hBel.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    have hkle : k ≤ Open.pRank p B :=
      le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp.out B) ⟨B, le_rfl, hBel, hk⟩
    have hmono : Open.pRank p B ≤
        Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp.out hB
    rw [hk]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)
  have hA4 : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian p A ∧
      Nat.card A = p ^ 4 := by
    have h4 : 4 ≤ Open.pRank p (P : Subgroup G) := four_le_pRank_sylow hloc.beta P
    obtain ⟨E, hEP, hE, hEc⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp.out (P : Subgroup G)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p
      (n := 4) (by rw [hEc]; exact pow_dvd_pow p h4)
    refine ⟨K.map E.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨a, -, rfl⟩
      exact hEP a.2
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
      · obtain ⟨a', -, ha⟩ := a.2
        obtain ⟨b', -, hb⟩ := b.2
        apply Subtype.ext
        show (a : G) * (b : G) = (b : G) * (a : G)
        rw [← ha, ← hb]
        exact congrArg Subtype.val (hE.1.is_comm.comm a' b')
      · obtain ⟨a', -, rfl⟩ := hz
        exact congrArg Subtype.val (Subtype.ext (hE.2 a' a'.2) : a' ^ p = 1)
    · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  obtain ⟨y0, hy0Q, hy0c, hy0p, hy0x⟩ :=
    h.exists_central_of_not_mem_zpowers hp2 hK.h243 hG.glob hG.fc hloc
  exact PPointP.pGroupEndgame G p P P.isPGroup' x y0 h.elem.2.1 h.mem hy0Q hy0c hy0p hy0x hA4 hQ3
    fun D hDQ hD hDc => h.not_exists_conj_lines hp2 hK.h243 hK.h244 hK.hsig hG.glob hG.d1 hG.fc hloc
      hDQ hD hDc

theorem false_of_unitaryThree_or_linTwoSq_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x)
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} {i : TauCeti.CFSGIndex}
    (hf : PPointFacts p M x R K i)
    (hReq : (R : Subgroup (RedCent p x)) =
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)))
    (hi : IsUnitaryThreeType p i ∨ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      IsLinTwoIndex p 2 d) : False := by
  have hp2 : p ≠ 2 := by omega
  have hQ4 := four_le_pRank_inf_centralizer_p hp5 hK hG hloc h
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  have hOcop : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hR4 : 4 ≤ Open.pRank p (R : Subgroup (RedCent p x)) := by
    rw [hReq, pRank_map_mk_eq_pRank_map_subtype hp.out O hOcop,
      map_subgroupOf_eq_of_le (inf_le_right : (P : Subgroup G) ⊓ C ≤ C)]
    exact hQ4
  haveI : K.Normal := hf.red.normal
  obtain ⟨e⟩ := hf.equiv
  have hAut : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
    rcases hi with ⟨d, rfl, hd, hn⟩ | ⟨d, rfl, hd⟩
    · exact PPointFrobenius.pt_pRank_mulAut_unitary hd hn e
    · obtain ⟨e2⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
      have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt (MulAut.congr (e.trans e2))
      rw [h1]
      exact PPointFrobenius.pt_pRank_mulAut_psl2_sq hp2
  have h2 := pRank_le_one_add_pRank_mulAut hp.out hf.isCyclic (R : Subgroup (RedCent p x))
  omega

theorem exists_linTwo_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) :
    ∃ (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)) (d : TauCeti.ValidLieTypeIndex)
      (n : ℕ), PPointFacts p M x R K (.lie d) ∧ 3 ≤ n ∧ IsLinTwoIndex p n d ∧
      (R : Subgroup (RedCent p x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
          (centralizer ({x} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) ∧
      4 ≤ Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) := by
  obtain ⟨R, K, i, hf, hReq⟩ := PPointFrobenius.exists_pPointFacts_five hp5 hK.h243 hK.h244
    hK.hexcl hG.glob hG.d1 hG.fc hloc h
  have hdata : PPointData p P M x R K i := ⟨h, hf, hReq⟩
  have hQ4 := four_le_pRank_inf_centralizer_p hp5 hK hG hloc h
  rcases hType x R K i hdata with ⟨d, n, hn, rfl, hd⟩ | hU
  · refine ⟨R, K, d, n, hf, ?_, hd, hReq, hQ4⟩
    by_contra hlt
    have hn2 : n = 2 := by omega
    subst hn2
    exact false_of_unitaryThree_or_linTwoSq_p hp5 hK hG hloc h hf hReq (Or.inr ⟨d, rfl, hd⟩)
  · exact (false_of_unitaryThree_or_linTwoSq_p hp5 hK hG hloc h hf hReq (Or.inl hU)).elim

theorem exists_borelDataP (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) :
    ∃ (n : ℕ) (f : GaloisField p n → G) (W : Subgroup G), BorelDataP p P M x f W := by
  obtain ⟨R, K, d, n, hf, hn, hd, hReq, -⟩ := exists_linTwo_p hp5 hK hG hloc hType h
  obtain ⟨f, W, hB⟩ := exists_borelDataP_of_linTwo hp5 hloc h hn hf hd hReq
  exact ⟨n, f, W, hB⟩

theorem shape_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M) (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) :
    PtShape p P x := by
  obtain ⟨R, K, d, n, hf, hn, hd, hReq, -⟩ := exists_linTwo_p hp5 hK hG hloc hType h
  exact ⟨PPointP.IsPPoint.isMulCommutative_sylow_p hp5 hK.h243 hK.h244 hK.hsig hG.glob hG.d1
      hG.fc hloc h (by omega) hf hd hReq,
    PPointP.IsPPoint.weaklyClosed_p hp5 hK.h243 hK.h244 hK.hsig hG.glob hG.d1 hG.fc hloc h
      (by omega) hf hd hReq⟩

theorem isLinTwoType_of_pPointData {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G}
    (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G) (hloc : D1Local p P M)
    (hType : PTypeHyp p P M) {x : G} {R : Sylow p (RedCent p x)}
    {K : Subgroup (RedCent p x)} {i : TauCeti.CFSGIndex} (hd : PPointData p P M x R K i) :
    IsLinTwoType p i := by
  obtain ⟨hx, hf, hReq⟩ := hd
  rcases hType x R K i ⟨hx, hf, hReq⟩ with hL | hU
  · exact hL
  · exact (false_of_unitaryThree_or_linTwoSq_p hp5 hK hG hloc hx hf hReq (Or.inl hU)).elim

end CFSG.LocalAnalysis.RankFourTheoremC.P5
