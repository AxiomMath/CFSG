module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyRows

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem shapePiece_of_rows (h7 : PieceSL7 p f) (h6 : PieceSL6 p f)
    (hs : RowPiece p f ShapeSLs) (hu7 : PieceSU7 p f) (hu6 : PieceSU6 p f) (hus : PieceSUs p f)
    (hc4 : RowPiece p f ShapeSp4) (hc3 : PieceSp3 p f) (he7 : PieceE7 p f) (he8 : PieceE8 p f)
    (hd : RowPiece p f ShapeTwinD) (hd5 : PieceTwinSL4 p f) (hb : PieceTwinB p f)
    (hb4 : PieceTwinSp2 p f) (htd : PieceTwinTD p f) (htd5 : PieceTwinSU4 p f)
    (hx : ShapeExcluded p f) : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n := by
  intro a t n
  by_cases h : ShapeTable a t n
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact h7 a t n h
    · exact h6 a t n h
    · exact hs a t n h
    · exact hu7 a t n h
    · exact hu6 a t n h
    · exact hus a t n h
    · exact hc4 a t n h
    · exact hc3 a t n h
    · exact he7 a t n h
    · exact he8 a t n h
    · exact hd a t n h
    · exact hd5 a t n h
    · exact hb a t n h
    · exact hb4 a t n h
    · exact htd a t n h
    · exact htd5 a t n h
  · exact hx a t n h

theorem coreStep_generic (hb3 : BootTriple p f) (hb : BootNoTriple p f)
    (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n) (hmulti : MultiPiece p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hconn : RouteD.DeltaConnected (conjClass K))
    (hdata : BootData p f (conjClass K)) : LieSystem p f G (conjClass K) := by
  obtain ⟨hex, hp1⟩ : ExactMembers (conjClass K) ∧ LocalOddCentral (conjClass K) {z} := by
    by_cases hT : IndepTriple p f (conjClass K)
    · exact hb3 G hnab hp2 hq K z hz hBelow hconn hT
    · exact hb G hnab hp2 hq K z hz hBelow hconn hdata hT
  have S : RouteDSetup p f K z := mk_routeDSetup hp2 hq hz hBelow hconn hex hp1
  rcases exists_shape_or_multi S.ih (mem_conjClass_self K) hz
    (singleton_not_subset_center hnab hz.ne_one) with ⟨a, t, n, hs⟩ | hm
  · exact hshape a t n G hnab K z S hs
  · exact hmulti G hnab K z S hm

theorem coreStep_small (hs4 : CITSectionalFour) (hd : SmallDisconnected p f)
    (ha : SmallConnectedA2 p f) (hc : SmallTypeC p f) (hup : SmallUpgrade p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (h3 : 3 ≤ CFSG.Open.twoRank G)
    (hgen : ¬ (RouteD.DeltaConnected (conjClass K) ∧ BootData p f (conjClass K))) :
    LieSystem p f G (conjClass K) := by
  refine hup G hnab hp2 hq K z hz ?_
  by_cases h4 : TwoSubgroupsFourGenerated G
  · exact hs4 G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
      (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) ⟨h3, h4⟩
  · by_cases hΔ : CFSG.ClassicalInvolution.DeltaConnected K
    · have hB : ¬ BootData p f (conjClass K) := fun hB => hgen ⟨(deltaConnected_iff K).mp hΔ, hB⟩
      by_cases hA2 : A2Configuration z K
      · exact ha G hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
      · exact hc G hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
    · exact hd G hnab hp2 hq hBelow K z hz h3 h4 hΔ

theorem coreStep_of_pieces
    (hr2 : CITRankTwo) (hs4 : CITSectionalFour) (hd : SmallDisconnected p f)
    (ha : SmallConnectedA2 p f) (hc : SmallTypeC p f) (hup : SmallUpgrade p f)
    (hb3 : BootTriple p f) (hb : BootNoTriple p f)
    (hsl6 : PieceSL6 p f) (hsls : ChainPieceSLs p f) (hsu7 : PieceSU7 p f) (hsu6 : PieceSU6 p f)
    (hsus : PieceSUs p f) (hp1all : PieceSp4P1 p f) (hnoother : PieceSp4NoOther p f)
    (hsp3 : PieceSp3 p f) (he7 : PieceE7 p f) (he8 : PieceE8 p f) (hdchain : ChainPieceTwinD p f)
    (htsl4 : PieceTwinSL4 p f) (htb : PieceTwinB p f) (htsp2 : PieceTwinSp2 p f)
    (httd : PieceTwinTD p f) (htsu4 : PieceTwinSU4 p f)
    (hmulti : MultiPiece p f) (hx1 : PieceAllA1 p f) (hx2 : PieceNoA1 p f)
    (hx3 : PieceExotic p f) : CoreStep p f := by
  intro hp2 hq G _ _ _ hnab K z hz hBelow
  have hshape := shapePiece_of_rows pieceSL7 hsl6 (pieceSLs_of_chain hsls) hsu7 hsu6 hsus
    (pieceSp4_of_pieces hp1all hnoother) hsp3 he7 he8 (pieceTwinD_of_chain hdchain) htsl4 htb htsp2
    httd htsu4 (shapeExcluded_of_pieces hx1 hx2 hx3)
  by_cases h2 : CFSG.Open.twoRank G ≤ 2
  · exact hup G hnab hp2 hq K z hz
      (hr2 G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) h2)
  · have h3 : 3 ≤ CFSG.Open.twoRank G := by omega
    by_cases hgen : RouteD.DeltaConnected (conjClass K) ∧ BootData p f (conjClass K)
    · exact coreStep_generic hb3 hb hshape hmulti hnab hp2 hq hz hBelow hgen.1 hgen.2
    · exact coreStep_small hs4 hd ha hc hup hnab hp2 hq hz hBelow h3 hgen

structure CoreStepPieces (p f : ℕ) [Fact p.Prime] : Prop where
  rankTwo : CITRankTwo
  sectional : CITSectionalFour
  disconnected : SmallDisconnected p f
  connectedA2 : SmallConnectedA2 p f
  typeC : SmallTypeC p f
  upgrade : SmallUpgrade p f
  bootTriple : BootTriple p f
  bootNoTriple : BootNoTriple p f
  sl6 : PieceSL6 p f
  slChain : ChainPieceSLs p f
  su7 : PieceSU7 p f
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
  noA1 : PieceNoA1 p f
  exotic : PieceExotic p f

theorem CoreStepPieces.coreStep (h : CoreStepPieces p f) : CoreStep p f :=
  coreStep_of_pieces h.rankTwo h.sectional h.disconnected h.connectedA2 h.typeC h.upgrade
    h.bootTriple h.bootNoTriple h.sl6 h.slChain h.su7 h.su6 h.sus h.sp4P1 h.sp4NoOther h.sp3 h.e7
    h.e8 h.twinDChain h.twinSL4 h.twinB h.twinSp2 h.twinTD h.twinSU4 h.multi h.allA1 h.noA1
    h.exotic

end CFSG.ClassicalInvolution.Generic.CoreAssembly
