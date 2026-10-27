module

public import CFSG.GH74.GLS.C3.Layer1.Th2CaseISyl
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.St1Bal
public import CFSG.GH74.Generic.S3.Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

section Hl1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsTerminalPair.isQuasisimple {x : G} {K : Subgroup G} (h : IsTerminalPair 2 x K) :
    IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.2.1.1) h.2.1.2.1

theorem CxK_le_centralizer {x : G} {K : Subgroup G} (hK : IsQuasisimple ↥K) :
    CxK x K ≤ centralizer (K : Set G) := fun _ hc =>
  Subgroup.mem_centralizer_iff.2 fun k hk => (GLS.Th2.commute_of_mem_cSec hK hc.2 k hk).symm

omit [Finite G] in
theorem mem_CxK_self {x : G} {K : Subgroup G} (h : K ≤ centralizer ({x} : Set G)) :
    x ∈ CxK x K := by
  have hc : ∀ k ∈ K, x * k = k * x := fun k hk =>
    ((Subgroup.mem_centralizer_singleton_iff.1 (h hk))).symm
  have hxK : x ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (hc k hk).symm
  have hxO : x ∈ centralizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (hc k (pPrimeCoreOf_le_self _ hk)).symm
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, ?_, ?_, ?_⟩
  · exact Subgroup.centralizer_le_normalizer (K : Set G) hxK
  · exact Subgroup.centralizer_le_normalizer _ hxO
  · intro k hk
    have : ⁅k, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hc k hk).symm
    rw [this]
    exact one_mem _

theorem one_le_pRank_of_mem_order_two {X : Subgroup G} {x : G} (hx : x ∈ X) (hx2 : orderOf x = 2) :
    1 ≤ pRank 2 ↥X := by
  set x' : ↥X := ⟨x, hx⟩ with hx'
  have hxp : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2] at this
  have hx'p : x' ^ 2 = 1 := Subtype.ext (by simpa [hx'] using hxp)
  have hx'1 : x' ≠ 1 := by
    intro h
    have h1 : x = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hx2
    omega
  have hel : IsElementaryAbelian 2 (zpowers x') := IsElementaryAbelian.zpowers_of_pow_eq_one hx'p
  have hcard : Nat.card (zpowers x') = 2 ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx'p hx'1, pow_one]
  exact CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian one_lt_two hel hcard

end Hl1

end CFSG.GH74.Generic.BProg
