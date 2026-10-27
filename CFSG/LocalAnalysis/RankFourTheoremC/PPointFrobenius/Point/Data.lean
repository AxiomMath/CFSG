module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE.PtData
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankFourTheoremC CFSG.RankThreeCoreUniqueness.Helpers CFSG.Open
  CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

structure PtKFacts : Prop where
  ia : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction
  i713 : GL83.I_7_13_1
  ke : KEStatement

theorem exists_pPointFacts_five [Fact p.Prime] (hp5 : 5 ≤ p) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hexcl : PPointExclusionFive) (hS : D1Global G)
    (hD1 : CFSG.AGLEmbeddingD2.D1For G) (hFC : FullCoreLocality G)
    (hloc : CFSG.AGLEmbedding.D1Local p P M) (h : IsPPoint p P M x) :
    ∃ (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)) (i : TauCeti.CFSGIndex),
      PPointFacts p M x R K i ∧ (R : Subgroup (RedCent p x)) =
        (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨R, K, hRK, hReq⟩ := h.exists_pPointReduced hFC hloc
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  have hcat := h.catalogSimpleSections hS hp
  obtain ⟨i, ⟨e⟩, hi, hio⟩ := hRK.exists_equiv_type hp2 h243 h244 hcat hzc hzp
  refine ⟨R, K, i, ⟨hRK, hRK.center_eq_bot hp2 h243 hcat, hRK.isPGroup_centralizer hzc hzp,
    hRK.isCyclic_centralizer hzc hzp, ⟨e⟩, ?_, hio⟩, hReq⟩
  rcases hi.cases hp with hty | hex
  · exact hty
  · exfalso
    exact hexcl G hS hD1 hFC p P M hloc hp5 x h R K hRK i ⟨e⟩ hex

structure PtData (p n : ℕ) [Fact p.Prime] (P : Sylow p G) (M : Subgroup G) (x : G)
    (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)) : Prop where
  red : PPointReduced p M x R K
  equiv : Nonempty (K ≃* PSL(2, GaloisField p n))
  three_le : 3 ≤ n
  isPGroup : IsPGroup p (centralizer (K : Set (RedCent p x)))
  isCyclic : IsCyclic (centralizer (K : Set (RedCent p x)))
  R_eq : (R : Subgroup (RedCent p x)) =
    (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))

theorem pt_pRank_mulAut_psl2_sq [Fact p.Prime] (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSL2GF p 2))) ≤ 2 := by
  have hp : p.Prime := Fact.out
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  have hEp : IsPGroup p E := fun y => ⟨1, by
    have : (y : MulAut (PSL2GF p 2)) ^ p = 1 := hE.2 y y.2
    exact Subtype.ext (by simpa using this)⟩
  have hdvd : Nat.card E ∣ p ^ 2 * 2 := kFactL2AutPCard p 2 hp2 (by norm_num) E hEp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rw [hk] at hdvd ⊢
  exact Nat.le_of_dvd (pow_pos hp.pos 2) (hcop.dvd_of_dvd_mul_right hdvd)

theorem pt_pRank_mulAut_unitary {K : Type} [Group K] [Finite K] [Fact p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (hn : d.1.fieldExponent = 1) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (Fact.out : p.Prime).one_lt fun B _ hB => ?_
  have hB' := kFactUnitaryAutElemRank K p d hd ⟨e⟩ B hB
  rw [hn] at hB'
  simpa using hB'

theorem pt_data [Fact p.Prime] (hk : PtKFacts) (hG : FrobGlobal G) (hl : PtPoint p P M x) :
    ∃ (n : ℕ) (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)), PtData p n P M x R K := by
  obtain ⟨n, R, K, hred, he, h3, hpg, hcyc, hReq⟩ := pt_data_abelian hk.ia hk.i713 hk.ke hG hl
  exact ⟨n, R, K, ⟨hred, he, h3, hpg, hcyc, hReq⟩⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
