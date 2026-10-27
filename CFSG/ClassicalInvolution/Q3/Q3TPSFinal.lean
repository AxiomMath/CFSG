module

public import CFSG.ClassicalInvolution.Q3.Q3TPSShort
public import CFSG.ClassicalInvolution.Q3.Q3TPSRow
public import CFSG.ClassicalInvolution.Q3.Q3TPChain
public import CFSG.ClassicalInvolution.Q3.Q3TPCtx
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.Q3.Q3TY3
public import CFSG.ClassicalInvolution.Q3.Q3TY1
public import CFSG.ClassicalInvolution.Q3.Q3WATwinDRow
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TP
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)
open CFSG.ClassicalInvolution.Generic.CoreAssembly (LinkedAtProduct)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)


theorem chainPiece3TwinSp2Pair_of_inputs (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3)
    (hL : Q3TY.TwinLinked3) : ChainPiece3TwinSp2Pair := by
  intro G _ _ _ hnab K z hR hshape
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨c⟩ := nonempty_tctxS3 yData3S_psp2 h3 hR hshape
  obtain ⟨T₁, hT₁, hT₁img⟩ := c.exists_twin
  have hT₁K : T₁ ≠ K := c.twin_ne hT₁ hT₁img.le
  have hT₁comm : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T₁ → Commutes T₁ N :=
    fun N hN hNT => c.commutes_T_of_ne hT₁ hT₁img.le hN hNT
  obtain ⟨R₀, hR₀, R₁, hR₁, hR₀₁, hnc⟩ := exists_noncommuting_fund_psp2
  obtain ⟨K₂, hK₂, hK₂K, hK₂Q, hK₂img⟩ := c.exists_member_of_fund hR₀
  obtain ⟨K₂', hK₂', -, -, hK₂'img⟩ := c.exists_member_of_fund hR₁
  have hK₂T : K₂ ≠ T₁ := by
    rintro rfl
    exact hK₂Q hT₁img.le
  have hne : K₂' ≠ K₂ := by
    rintro rfl
    exact hR₀₁ (Q3W.eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.hY.pow3 R₀ hR₀)
      (c.hY.pow3 R₁ hR₁) (hK₂img.symm.trans hK₂'img))
  have hnotcomm : ¬ Commutes K₂ K₂' := fun h =>
    hnc ((c.commutes_iff_fund hK₂ hK₂' hR₀ hK₂img hK₂'img).mp h)
  have hnotTwin : ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T := by
    rintro T hT rfl
    exact hnotcomm (hT.comm_T K₂' hK₂' hne)
  obtain ⟨w, hw⟩ := hR.inClass.classical K₂ hK₂.1
  have hzw : z ≠ w := by
    rintro rfl
    exact not_locImg_eq_map_fund3S c.hY hK₂ hw c.d.ψ c.d.ker_le hR₀ hK₂img
  have hKK₂ : Commutes K K₂ := c.commutes_K_of_ne hK₂ hK₂K
  obtain ⟨hP1x, hO3x⟩ := hP G K z hR K₂ hK₂.1 w hw hKK₂ hzw
  have hlink := hL G hnab K z hR .PSp 2 (Or.inl ⟨rfl, rfl⟩) hshape K₂ hK₂ hK₂K hnotTwin w hw
  obtain ⟨-, N, hN, p1, p2⟩ := exists_chain_of_twin_product3 h3 hnab hR hT₁ hT₁K hT₁comm hK₂ hK₂K
    hK₂T hw hzw hP1x hO3x hlink
  obtain ⟨Us, hKUs, hNUs, hsp⟩ := twinSp2ShortNodePair3 h3 G hnab K z hR hshape N K₂ hN.1 hK₂
    hK₂K hnotTwin hKK₂ p1 p2
  refine ⟨![K, N, K₂, Us], ?_, ?_, ?_, ?_⟩
  · exact hKΩ
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact hKK₂
      | exact hKUs
      | exact hNUs
  · intro i j hij hj
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact absurd hj (by decide)
      | exact p1
      | exact p2
  · intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hi (by decide)
      | exact absurd hj (by decide)
      | exact hsp

theorem piece3TwinSp2_of_inputs_pair (h3 : OddThreeFreeInput) (hW : Q3TW.WeakCT3OddMapPair 4)
    (hP : Q3TC.ProductP1Input3) (hL : Q3TY.TwinLinked3) : Piece3TwinSp2 :=
  piece3TwinSp2_of_chain_pair h3 hW (chainPiece3TwinSp2Pair_of_inputs h3 hP hL)

end CFSG.ClassicalInvolution.Q3.Q3TPS
