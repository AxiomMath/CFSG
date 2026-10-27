module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointProp31
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointShear
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSmallTypes
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

namespace IsPPoint

variable {M : Subgroup G} {x : G}

theorem exists_linTwo_three {P : Sylow 3 G} (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (h313 : GL83NormalElementaryRankFour) (hUB : KFactUnitaryBorelMaximal)
    (hUI : KFactUnitaryInvolution) (hRB : KFactReeBorelMaximal) (hRI : KFactReeInvolution)
    (hKU9 : KFactUnitaryAutElemRank) (hM11 : KFactM11Three) (hS : D1Global G) (hD1 : D1For G)
    (hFC : FullCoreLocality G) (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) :
    ∃ (R : Sylow 3 (RedCent 3 x)) (K : Subgroup (RedCent 3 x)) (d : TauCeti.ValidLieTypeIndex)
      (n : ℕ), PPointFacts 3 M x R K (.lie d) ∧ 3 ≤ n ∧ IsLinTwoIndex 3 n d ∧
      (R : Subgroup (RedCent 3 x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
          (centralizer ({x} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) ∧
      4 ≤ Open.pRank 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨R, K, i, hf, hReq⟩ := h.exists_pPointFacts_three h243 h244 hUB hUI hRB hRI hS hD1 hFC hloc
  have hP4 : 4 ≤ Open.pRank 3 (P : Subgroup G) := four_le_pRank_sylow hloc.beta P
  obtain ⟨E, hEP, hEN, hEel, hEcard⟩ := h313 G (P : Subgroup G) P.isPGroup' hP4
  have hEC : E ≤ centralizer ({x} : Set G) :=
    h.le_centralizer_of_isElemAbelian (by norm_num) h243 h244 hsig hS hD1 hFC hloc hEP hEel
      (hEN h.mem)
  have hQ4 : 4 ≤ Open.pRank 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (le_inf hEP hEC) hEel hEcard
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : (3 : ℕ).Coprime (Nat.card O) := primeComplementCore_coprime 3
  have hR4 : 4 ≤ Open.pRank 3 (R : Subgroup (RedCent 3 x)) := by
    rw [hReq, pRank_map_mk_eq_pRank_map_subtype hp O hOcop,
      map_subgroupOf_eq_of_le (inf_le_right : (P : Subgroup G) ⊓ C ≤ C)]
    exact hQ4
  have hKn : K.Normal := hf.red.normal
  obtain ⟨e⟩ := hf.equiv
  rcases exists_linTwo_or_pRank_mulAut_le_two hKU9 hM11 hf.center_eq_bot hf.type e with
    ⟨d, n, rfl, hd, hn⟩ | hAut
  · refine ⟨R, K, d, n, hf, ?_, hd, hReq, hQ4⟩
    by_contra hlt
    have hn2 : n = 2 := by omega
    subst hn2
    exact card_ne_nine_of_isLinTwoIndex hd (by norm_num)
  · exfalso
    have := pRank_le_one_add_pRank_mulAut hp hf.isCyclic (R : Subgroup (RedCent 3 x))
    omega

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
