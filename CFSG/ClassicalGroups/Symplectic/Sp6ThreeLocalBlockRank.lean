module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalBlockCommute
public import CFSG.Open.LocalVocabulary
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem two_ne_zero_of_five_le {r : ℕ} [CharP K r] (h5 : 5 ≤ r) : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K r] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

theorem six_ne_zero_of_five_le {r : ℕ} [CharP K r] (h5 : 5 ≤ r) (h3 : (3 : K) ≠ 0) :
    (6 : K) ≠ 0 := by
  have : (6 : K) = 2 * 3 := by norm_num
  rw [this]
  exact mul_ne_zero (two_ne_zero_of_five_le h5) h3

theorem one_le_pRank_of_mem_of_orderOf_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H : Subgroup G} {x : G} (hx : x ∈ H) (hxp : orderOf x = p) :
    1 ≤ CFSG.Open.pRank p H := by
  haveI := Fact.mk hp
  have hcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxp]
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.mpr hx)
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hcard) (by simp [hcard])

theorem two_le_pRank_of_block_mulSingle [Finite K] {p : ℕ} (hp : p.Prime) {z : SL(2, K)}
    (hz : orderOf z = p) {i j : Fin 3} (hij : i ≠ j) {H : Subgroup (StatedSp 3 K)}
    (hi : block (Pi.mulSingle i z) ∈ H) (hj : block (Pi.mulSingle j z) ∈ H) :
    2 ≤ CFSG.Open.pRank p H := by
  haveI := Fact.mk hp
  have hc : Commute (block (Pi.mulSingle i z)) (block (Pi.mulSingle j z)) :=
    (Pi.mulSingle_commute (f := fun _ : Fin 3 => SL(2, K)) hij z z).map block
  have hn : (block (Pi.mulSingle j z)) ∉ Subgroup.zpowers (block (Pi.mulSingle i z)) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow] at hk
    have h1 := block_injective hk
    have h2 := congrFun h1 j
    simp [Pi.mulSingle_eq_of_ne hij.symm] at h2
    rw [← h2, orderOf_one] at hz
    exact hp.one_lt.ne hz
  exact CFSG.GroupTheory.two_le_pRank_of_commute hi hj
    (by rw [orderOf_block_mulSingle, hz]) (by rw [orderOf_block_mulSingle, hz]) hc hn

theorem orderOf_unipotent_one [Finite K] {r : ℕ} (hr : r.Prime) [CharP K r] :
    orderOf (CFSG.SL2MinimalFaithful.unipotent (1 : K)) = r := by
  have h1 : CFSG.SL2MinimalFaithful.unipotent (1 : K) =
      CFSG.SL2MinimalFaithful.unipotentHom (Multiplicative.ofAdd (1 : K)) := rfl
  rw [h1, orderOf_injective _ CFSG.SL2MinimalFaithful.unipotentHom_injective,
    orderOf_ofAdd_eq_addOrderOf]
  exact (CharP.eq K ‹CharP K r› (CharP.addOrderOf_one K)).symm

theorem two_le_pRank_centralizer_c₀_weight_one [Finite K] {r : ℕ} (hr : r.Prime) [CharP K r]
    {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    2 ≤ CFSG.Open.pRank r (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0])} : Set (StatedSp 3 K))) := by
  have hz := orderOf_unipotent_one (K := K) hr
  have hmem : ∀ i : Fin 3, i ≠ 0 →
      block (Pi.mulSingle i (CFSG.SL2MinimalFaithful.unipotent (1 : K))) ∈
        Subgroup.centralizer ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0])} : Set (StatedSp 3 K)) := by
    intro i hi
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := commute_block_mulSingle_c₀ (i := i) hs
      (CFSG.SL2MinimalFaithful.unipotent (1 : K)) (Multiplicative.ofAdd ![1, 0, 0])
      (by fin_cases i <;> simp_all)
    exact hc.eq
  exact two_le_pRank_of_block_mulSingle hr hz (i := 1) (j := 2) (by decide)
    (hmem 1 (by decide)) (hmem 2 (by decide))

theorem one_le_pRank_centralizer_c₀_planeA [Finite K] {r : ℕ} (hr : r.Prime) [CharP K r]
    {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    1 ≤ CFSG.Open.pRank r (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0]), c₀ hs (Multiplicative.ofAdd ![0, 1, 0])} :
        Set (StatedSp 3 K))) := by
  have hz := orderOf_unipotent_one (K := K) hr
  refine one_le_pRank_of_mem_of_orderOf_eq hr
    (x := block (Pi.mulSingle 2 (CFSG.SL2MinimalFaithful.unipotent (1 : K)))) ?_
    (by rw [orderOf_block_mulSingle, hz])
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | rfl
  · exact (commute_block_mulSingle_c₀ hs _ _ (by simp)).symm.eq
  · exact (commute_block_mulSingle_c₀ hs _ _ (by simp)).symm.eq

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
