module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.RouteD.TypeCMain
public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem oddCoverSL3_of_five_le (hq : 5 ≤ p ^ f) : OddCoverSL3 (GaloisField p f) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  exact CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} (GaloisField.card p f hf)
    hq

theorem pieceSL7 : PieceSL7 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨D, -, -⟩ := routeD_typeA S.odd S.five (m := m) (by omega) S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls (localShapeA_of_T hS) S.p1
    (oddCoverSL3_of_five_le S.five)
  exact ⟨D⟩

theorem pieceSLs_of_chain (h : ChainPieceSLs p f) : RowPiece p f ShapeSLs := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn3, hn5⟩ := hshape
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hshapeA := localShapeA_of_T hS
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z S m (by omega) (by omega) hshapeA
  obtain ⟨D, -, -⟩ := routeD_typeA_of_chain S.odd S.five (m := m) (by omega) S.inClass
    (mem_conjClass_self K) (single_class K) S.conn S.cls hshapeA S.p1 U hUΩ hcomm hpair
  exact ⟨D⟩

theorem pieceSp4_of_pieces (h1 : PieceSp4P1 p f) (h2 : PieceSp4NoOther p f) :
    RowPiece p f ShapeSp4 := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hC : CSetupAll p f n (conjClass K) K z :=
    { odd := S.odd, five := S.five, three := by omega, inClass := S.inClass, exact := S.exact,
      mem := mem_conjClass_self K, cls := S.cls, single := single_class K,
      centerTriv := center_eq_bot hnab, shape := localShapeC_of_T hS,
      p1cl := fun _ _ y hy => h1 G hnab K z S n hn hS y hy.orderOf_eq_two, ih := S.ih,
      p1 := h1 G hnab K z S n hn hS, noOther := h2 G hnab K z S n hn hS }
  obtain ⟨D, -, -⟩ := routeD_typeC hC S.conn
  exact ⟨D⟩

theorem pieceSp4 : RowPiece p f ShapeSp4 := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hC : CSetup p f n (conjClass K) K z :=
    { odd := S.odd, five := S.five, three := by omega, inClass := S.inClass, exact := S.exact,
      mem := mem_conjClass_self K, cls := S.cls, single := single_class K,
      centerTriv := center_eq_bot hnab, shape := localShapeC_of_T hS,
      p1cl := Balance.localOddCentral_of_classicalMember S.odd (pos_of_five_le S.five) S.inClass
        ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) S.cls S.p1,
      ih := S.ih }
  obtain ⟨D, -, -⟩ := routeD_typeC_of_four hC hn S.conn
  exact ⟨D⟩

theorem pieceTwinD_of_chain (h : ChainPieceTwinD p f) : RowPiece p f ShapeTwinD := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaPlus (n + 2 - 2) (conjClass K) z := by rw [hn']; exact hS
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z S (n + 2) (by omega) hS'
  obtain ⟨D, -, -⟩ := routeD_typeD_of_chain S.odd S.five (n := n + 2) (by omega) S.inClass
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS' S.p1 U hUΩ hcomm hpair
  exact ⟨D⟩

section Small

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sl2Witness_of_isClassicalMember {K : Subgroup G} {z : G}
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h : IsClassicalMember p f K z) : SL2Witness K :=
  ⟨p, f, inferInstance, hp2, pos_of_five_le hq, h.nonempty_equiv⟩

theorem smallDisconnected_of_cit (hfc : FrameConnected p f) (h : CITDisconnected) :
    SmallDisconnected p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ
  have hnotE : ¬ HasEFrameRank4 K := fun hE =>
    hΔ (hfc G hnab hp2 hq K z hz hBelow hE)
  exact h G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
    (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz)
    ⟨⟨h3, h4, hnotE⟩, sl2Witness_of_isClassicalMember hp2 hq hz, hΔ⟩

theorem smallConnectedA2_of_cit (h : CITConnectedA2) : SmallConnectedA2 p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
  have hnotE : ¬ HasEFrameRank4 K := fun hE => hB (bootData_of_hasEFrameRank4 hz hE)
  exact h G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
    (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz)
    ⟨⟨h3, h4, hnotE⟩, sl2Witness_of_isClassicalMember hp2 hq hz, hΔ, hA2⟩

theorem smallTypeC_of_cit (h : CITTypeC) : SmallTypeC p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
  have hnotE : ¬ HasEFrameRank4 K := fun hE => hB (bootData_of_hasEFrameRank4 hz hE)
  exact h G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
    (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz)
    ⟨⟨h3, h4, hnotE⟩, sl2Witness_of_isClassicalMember hp2 hq hz, hΔ, hA2⟩

end Small

end CFSG.ClassicalInvolution.Generic.CoreAssembly
