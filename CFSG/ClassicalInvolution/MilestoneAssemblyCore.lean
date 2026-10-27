module

public import CFSG.ClassicalInvolution.Generic.CoreAssembly
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalExc
public import CFSG.ClassicalInvolution.RouteD.GapsLocal
public import CFSG.ClassicalInvolution.RouteD.TypeUChain
public import CFSG.ClassicalInvolution.SmallCases.RankTwoBranch

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem pieceSU7 : PieceSU7 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨D, -, -⟩ := routeD_typeU S.odd S.five (m := m) (by omega) S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS.exists_two_components S.p1
  exact ⟨D⟩

theorem pieceNoA1_of_mfz (hMFZ : Gaps.FundNoncentral p) : PieceNoA1 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, hA⟩ := hshape
  obtain ⟨D, hc, i₁, ht, hr, hrest⟩ := hS
  obtain ⟨i, hi, hi2, -⟩ := Gaps.locImg_eq_range_of_involution hMFZ D (N := K)
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩ S.cls
  have hii : i = i₁ := Fin.ext (by have := i.isLt; have := i₁.isLt; omega)
  subst hii
  exact absurd ⟨ht ▸ hi, hr ▸ hi2⟩ hA

@[expose] def ChainPieceSL45 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 3 ≤ m → m ≤ 4 →
      LocalShapeA p f m (conjClass K) z →
      ∃ U : Fin (m + 2) → Subgroup G, (∀ i, U i ∈ conjClass K) ∧
        (∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
        ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
          ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (GaloisField p f) W
            (U i) (U j)

@[expose] def PieceSL3Big (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ¬ TwoSubgroupsFourGenerated G →
      LocalShapeT p f 1 .PSL 3 (conjClass K) z → LieSystem p f G (conjClass K)

theorem shapePiece_sl45_of_chain (h : ChainPieceSL45 p f) (a : ℕ) (t : StatedLieTag) (n : ℕ)
    (hshape : a = 1 ∧ t = .PSL ∧ 4 ≤ n ∧ n ≤ 5) : ShapePiece p f a t n := by
  intro G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn4, hn5⟩ := hshape
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hshapeA := localShapeA_of_T hS
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z S m (by omega) (by omega) hshapeA
  obtain ⟨D, -, -⟩ := routeD_typeA_of_chain S.odd S.five (m := m) (by omega) S.inClass
    (mem_conjClass_self K) (single_class K) S.conn S.cls hshapeA S.p1 U hUΩ hcomm hpair
  exact ⟨D⟩

theorem shapePiece_sl3 (hbig : PieceSL3Big p f) (hs4 : CITSectionalFour)
    (hup : SmallUpgrade p f) : ShapePiece p f 1 .PSL 3 := by
  intro G _ _ _ hnab K z S hS
  by_cases h4 : TwoSubgroupsFourGenerated G
  · refine hup G hnab S.odd S.five K z S.cls ?_
    by_cases h2 : CFSG.Open.twoRank G ≤ 2
    · exact citRankTwo G hnab z S.cls.orderOf_eq_two K S.cls.mem S.cls.subnormal
        (witness_of_isClassicalMember S.odd S.five S.cls)
        (not_isSolvable_of_isClassicalMember S.cls) h2
    · exact hs4 G hnab z S.cls.orderOf_eq_two K S.cls.mem S.cls.subnormal
        (witness_of_isClassicalMember S.odd S.five S.cls)
        (not_isSolvable_of_isClassicalMember S.cls) ⟨by omega, h4⟩
  · exact hbig G hnab K z S h4 hS

theorem rowSLs_of_parts (hbig : PieceSL3Big p f) (hs4 : CITSectionalFour) (hup : SmallUpgrade p f)
    (h : ChainPieceSL45 p f) : RowPiece p f ShapeSLs := by
  intro a t n hshape
  obtain ⟨ha, ht, hn3, hn5⟩ := hshape
  by_cases hn : n = 3
  · subst hn ha ht
    exact shapePiece_sl3 hbig hs4 hup
  · exact shapePiece_sl45_of_chain h a t n ⟨ha, ht, by omega, hn5⟩

structure CoreOpen (p f : ℕ) [Fact p.Prime] : Prop where
  sectional : CITSectionalFour
  disconnected : SmallDisconnected p f
  connectedA2 : SmallConnectedA2 p f
  typeC : SmallTypeC p f
  upgrade : SmallUpgrade p f
  bootTriple : BootTriple p f
  bootNoTriple : BootNoTriple p f
  sl6 : PieceSL6 p f
  slChain : ChainPieceSL45 p f
  sl3 : PieceSL3Big p f
  su6 : PieceSU6 p f
  sus : PieceSUs p f
  sp4P1 : PieceSp4P1 p f
  sp4NoOther : PieceSp4NoOther p f
  sp3 : PieceSp3 p f
  e7 : PieceE7 p f
  e8 : PieceE8 p f
  twinDChain : ChainPieceTwinD p f
  twinSL4 : PieceTwinSL4 p f
  twinB : PieceTwinB p f
  twinSp2 : PieceTwinSp2 p f
  twinTD : PieceTwinTD p f
  twinSU4 : PieceTwinSU4 p f
  multi : MultiPiece p f
  allA1 : PieceAllA1 p f
  exotic : PieceExotic p f

theorem coreStep_of_open (hMFZ : Gaps.FundNoncentral p) (h : CoreOpen p f) : CoreStep p f := by
  intro hp2 hq G _ _ _ hnab K z hz hBelow
  have hshape := shapePiece_of_rows pieceSL7 h.sl6 (rowSLs_of_parts h.sl3 h.sectional h.upgrade
    h.slChain) pieceSU7 h.su6 h.sus (pieceSp4_of_pieces h.sp4P1 h.sp4NoOther) h.sp3 h.e7 h.e8
    (pieceTwinD_of_chain h.twinDChain) h.twinSL4 h.twinB h.twinSp2 h.twinTD h.twinSU4
    (shapeExcluded_of_pieces h.allA1 (pieceNoA1_of_mfz hMFZ) h.exotic)
  by_cases h2 : CFSG.Open.twoRank G ≤ 2
  · exact h.upgrade G hnab hp2 hq K z hz
      (citRankTwo G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) h2)
  · have h3 : 3 ≤ CFSG.Open.twoRank G := by omega
    by_cases hgen : RouteD.DeltaConnected (conjClass K) ∧ BootData p f (conjClass K)
    · exact coreStep_generic h.bootTriple h.bootNoTriple hshape h.multi hnab hp2 hq hz hBelow
        hgen.1 hgen.2
    · exact coreStep_small h.sectional h.disconnected h.connectedA2 h.typeC h.upgrade hnab hp2 hq
        hz hBelow h3 hgen

theorem citInductiveU_of_open (hMFZ : Gaps.FundNoncentral p) (h : CoreOpen p f)
    (hexc : CFSG.ClassicalInvolution.ModelFacts.ClassicalMembersFundamentalExc p f) :
    CITInductiveU p f :=
  CFSG.ClassicalInvolution.ModelFacts.citInductiveU_of_coreStep_exc (coreStep_of_open hMFZ h) hexc

end CFSG.ClassicalInvolution.MilestoneAssembly
