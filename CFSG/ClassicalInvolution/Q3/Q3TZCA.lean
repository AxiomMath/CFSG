module

public import CFSG.ClassicalInvolution.Q3.Q3TZTrans
public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs
public import CFSG.ClassicalInvolution.Q3.Q3TZClos

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TIV
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow TwinDatumOn)

section Statement


@[expose] def TwinPairMax3 (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ (R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)
    (x x' : (modelUniv tY nY 3 1 Nat.prime_three).K),
    TwinDatumOn tY (modelUniv tY nY 3 1 Nat.prime_three) R R' x x' →
      IsCoatom (G2D4Models.conjStabilizer
        ({R, R'} : Set (Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)))

end Statement

section CA

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}


theorem ca_of_twinPairMax3 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z)
    (hMax : TwinPairMax3 tY nY) {N : Subgroup G} (hNΩ : N ∈ conjClass3 K)
    (hNΦ : ∀ L ∈ phi3 K T z, Commutes N L) : N = K ∨ N = T := by
  classical
  have hconn : RouteD.DeltaConnected (conjClass3 K) :=
    (CoreAssembly.deltaConnected_iff K).mp hR.conn
  have hKiso : ∀ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ K → Commutes K L :=
    fun L hL hLK => hT.comm_K L hL hLK
  have hTiso : ∀ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ T → Commutes T L :=
    fun L hL hLT => hT.comm_T L hL hLT
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member hKiso hTiso
  obtain ⟨t, hJt⟩ := hR.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member3 h3 hnab hR hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT3 h3 hR hrow hshape hT clsT hJ hJK hJT hJt htz
  have hJΦ : J ∈ phi3 K T z := ⟨hJ, hJK, hJT⟩
  have hJ₂Φ : A.J₂ ∈ phi3 K T z := ⟨A.hJ₂z, A.hJ₂K, A.hJ₂T⟩
  have hNΩt : N ∈ centralizingMembers (conjClass3 K) {t} := ⟨hNΩ, fun n hn => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hNΦ J hJΦ n hn t hJt.mem⟩
  have hNJ : N ≠ J := fun h => not_commutes_self_of_mem3 hR J hJ.1 (by
    have := hNΦ J hJΦ
    rwa [h] at this)
  have hNJ₂ : N ≠ A.J₂ := fun h => not_commutes_self_of_mem3 hR A.J₂ A.hJ₂t.1 (by
    have := hNΦ A.J₂ hJ₂Φ
    rwa [h] at this)
  obtain ⟨y, hy, hyKN, hyψ⟩ := link_big'3 A.c (K := J) (T := A.J₂) (L := K) (L' := N) A.hJt
    A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso A.hKt hJK.symm A.hJ₂K.symm hNΩt hNJ hNJ₂
  have hyN : y ∈ normX3 K T z := mem_normX3_iff.mpr
    (conjSub_xGen_eq3 c hR.cls hT y (fun L hL => by
      rw [hyKN]
      exact hNΦ L hL))
  have hMaxA := hMax A.RK A.RT A.x A.x' A.hdat
  have hN : ∀ y' ∈ locLayer (conjClass3 K) t, (conjSub y' K = K ∨ conjSub y' K = T) →
      y' ∈ normX3 K T z := by
    intro y' _ h
    refine mem_normX3_iff.mpr (conjSub_xGen_eq3 c hR.cls hT y' (fun L hL => ?_))
    rcases h with h | h
    · rw [h]
      exact hT.comm_K L hL.1 hL.2.1
    · rw [h]
      exact hT.comm_T L hL.1 hL.2.2
  rcases transfer_max3 A hMaxA (normX3 K T z) hN with hall | hone
  · exact (false_of_normalizes3 hnab hconn c hR.cls hT hJ hJK hJT A hall).elim
  · have := hone y hyN hy hyψ
    rw [hyKN] at this
    exact this

end CA

section NC

variable {P : StatedLieTag → ℕ → Prop}


theorem twinYNoCentral3_of_twinPairMax3
    (hMax : ∀ tY nY, TwinRow tY nY → P tY nY → TwinPairMax3 tY nY) :
    Q3TIY.TwinYNoCentral3On P := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e M hM
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ N ∈ phi3 K T z, Commutes M N := fun N hN => hcon N hN.1 hN.2.1 hN.2.2
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  rcases ca_of_twinPairMax3 h3 hnab hR hrow hshape hT clsT (hMax tY nY hrow hP) hM.1 hcomm with
    h | h
  · rw [h] at hM
    exact twinElt_not_le_centralizer_left3 e hR.cls (hex K hKΩ) hKT hM.2
  · rw [h] at hM
    exact twinElt_not_le_centralizer_right3 e clsT (hex T hT.mem.1) hKT hM.2

end NC

end CFSG.ClassicalInvolution.Q3.Q3TZ
