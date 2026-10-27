module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open

theorem commutes_of_isSimpleGroup_of_isSolvable {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [Group.IsSolvable Q] (a b : Q) : a * b = b * a := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · have hab := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    change _ ∈ commutator Q at hab
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact hab
  · have := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
    rw [h] at this
    exact absurd this (lt_irrefl _)

section Quasisimple

variable {G : Type} [Group G] [Finite G]

theorem false_of_isSylowTwoOf_le_centralizer {K P : Subgroup G} (hK : CFSG.IsQuasisimple ↥K)
    (hP : IsSylowTwoOf P K) (hPc : P ≤ Subgroup.centralizer (K : Set G)) : False := by
  have hPZ : P.subgroupOf K ≤ Subgroup.center ↥K := by
    intro x hx
    have hxP : (x : G) ∈ P := hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h := Subgroup.mem_centralizer_iff.mp (hPc hxP) (y : G) y.2
    exact Subtype.ext h
  have hnd : ¬ 2 ∣ (Subgroup.center ↥K).index :=
    fun h => hP.2.2 (h.trans (Subgroup.index_dvd_of_le hPZ))
  have hodd : Odd (Nat.card (↥K ⧸ Subgroup.center ↥K)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  have hsolv : Group.IsSolvable (↥K ⧸ Subgroup.center ↥K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.1
  obtain ⟨a, b, hab⟩ := hK.2.2
  exact hab (commutes_of_isSimpleGroup_of_isSolvable a b)

theorem not_le_normalizer_of_sylow_inf_le {H S K R : Subgroup G} (hS : IsSylowTwoOf S H)
    (hK : IsComponentIn K H) (hRH : R ≤ H) (hR : IsPGroup 2 R) (hSKR : S ⊓ K ≤ R) :
    ¬ H ≤ Subgroup.normalizer (R : Set G) := by
  intro hN
  have hRO : R ≤ pCoreOf 2 H :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 R H hRH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr hN) hR
  have hKc : K ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_pCoreOf_eq_bot hK)
  refine false_of_isSylowTwoOf_le_centralizer (K := K) (P := S ⊓ K)
    (BenderBranch.isQuasisimple_of_isComponentIn hK)
    (RankOneRecog.isSylowTwoOf_inf_of_subnormal hS hK.1 hK.2.2) ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hKc hy) x (hRO (hSKR hx))).symm

end Quasisimple

end CFSG.QuasithinUnique.Unc25G2
