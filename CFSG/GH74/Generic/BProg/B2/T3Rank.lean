module

public import CFSG.GH74.Generic.BProg.B2.NoSD
public import CFSG.GH74.Generic.BProg.B2.Thm2Comp
import CFSG.GH74.Generic.BProg.B2.T1Basic

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

namespace T3Rank

theorem Q_le_CMbar (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) {H : Subgroup G}
    (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K) : Q ≤ CMbar M K := by
  have hQM : Q ≤ M := Q_le_M hs
  have hHsub : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hH.2.1.2
  have hOK : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 M :=
    Thm2Comp.pPrimeCoreOf_le_of_isSubnormal_barIn hKM (hc1 ▸ hHsub)
  intro q hq
  have hqM : q ∈ M := hQM hq
  refine (Thm2Comp.mem_CMbar_iff hKM ⟨q, hqM⟩).2
    (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
  have hqC : q ∈ CxK x K := hs.sylowQ.le hq
  have hcomm : ⁅(k : G), q⁆ ∈ pPrimeCoreOf 2 K := (Subgroup.mem_inf.1 hqC).2.2.2 (k : G) hkK
  have := (Thm2Comp.comm_mem_pPrimeCoreOf_iff k ⟨q, hqM⟩).1 (hOK hcomm)
  exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem isSylowOf_CMbar (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) {H : Subgroup G}
    (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K) :
    IsSylowOf 2 Q (CMbar M K) :=
  isSylowOf_CMbar_of_le hs hKM (Q_le_CMbar hs hKM hH hc1)

end T3Rank

theorem pRank_CMbar_le_one (hNo : NoJPrimeNonSD) (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M)
    (hnSD : ¬ B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)) {H : Subgroup G} (hH : IsMinSubnormalIn K M H)
    (hc1 : barIn M H = barIn M K) : pRank 2 (CMbar M K) ≤ 1 := by
  have hsyl : IsSylowOf 2 Q (CMbar M K) := T3Rank.isSylowOf_CMbar hs hKM hH hc1
  have hr : pRank 2 ↥(CxK x K) ≤ 1 := (pRank_CxK_le_one_or_sd hNo hs).resolve_right hnSD
  calc pRank 2 ↥(CMbar M K) = pRank 2 ↥Q := Thm2Comp.pRank_eq_pRank_sylow hsyl
    _ ≤ pRank 2 ↥(CxK x K) :=
        CFSG.RankThree.PartOne.Quotient36.pRank_mono_subgroup one_lt_two hs.sylowQ.le
    _ ≤ 1 := hr

end CFSG.GH74.Generic.BProg.B2
