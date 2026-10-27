module

public import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
public import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def zGen (a : G) (T : Subgroup G) : Set G :=
  {w | ∃ K, IsRigidRankOneComp a K ∧ w ∈ T ⊓ K ∧ orderOf w = 2}

theorem zStruct (hquat : II4_4_quat) (hG : IsKProperSimple G) (hgen : Gen4 G) {a : G}
    {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({a} : Set G))) :
    ∀ c ∈ T ⊓ zStar (rigidProduct a), c ∈ Subgroup.closure (zGen a T) := by
  intro c hc
  have hmem : ∀ K z, IsRigidRankOneComp a K → QData T K z → z ∈ Subgroup.closure (zGen a T) :=
    fun K z hK hq => Subgroup.subset_closure ⟨K, hK, hq.mem, qdata_orderOf hq⟩
  by_cases hne : {K : Subgroup G | IsRigidRankOneComp a K}.Nonempty
  · obtain ⟨K₀, hK₀⟩ := hne
    by_cases hsingle : ∀ K', IsRigidRankOneComp a K' → K' = K₀
    · obtain ⟨z, hq, hZ⟩ := zStar_single hquat hG hK₀ hT hsingle
      rcases hZ c hc with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact hmem K₀ z hK₀ hq
    · push Not at hsingle
      obtain ⟨K₂, hK₂, hne⟩ := hsingle
      obtain ⟨z₁, z₂, q₁, q₂, hZ⟩ := zStar_two hquat hG hgen hK₀ hK₂ hne.symm hT
      have h1 := hmem K₀ z₁ hK₀ q₁
      have h2 := hmem K₂ z₂ hK₂ q₂
      rcases hZ c hc with h | h | h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact h1
      · rw [h]
        exact h2
      · rw [h]
        exact mul_mem h1 h2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : rigidProduct a = ⊥ := by
      unfold rigidProduct
      rw [hne, sSup_empty]
    have hc1 : c ∈ rigidProduct a := (Subgroup.mem_inf.1 hc.2).1
    rw [hbot, Subgroup.mem_bot] at hc1
    rw [hc1]
    exact one_mem _

theorem mem_cSec_of_mem_zStar (h44 : II4_44) (hquat : II4_4_quat) (hG : IsKProperSimple G)
    (hgen : Gen4 G) {a : G} {w : G} (hw : w ∈ zStar (rigidProduct a))
    (hw2 : ∃ n : ℕ, w ^ (2 ^ n) = 1) {K : Subgroup G} (hK : IsRigidRankOneComp a K) :
    w ∈ cSec K := by
  have hwC : w ∈ centralizer ({a} : Set G) :=
    rigidProduct_le_cent a (Subgroup.mem_inf.1 hw).1
  obtain ⟨T, hT, hwT⟩ := exists_isSylowOf_ge' (zpowers_le.2 hwC) (isPGroup_zpowers_of_pow_eq_one hw2)
  have hwT' : w ∈ T := hwT (mem_zpowers w)
  have hcl := zStruct hquat hG hgen hT w ⟨hwT', hw⟩
  have hle : Subgroup.closure (zGen a T) ≤ cSec K := by
    rw [Subgroup.closure_le]
    rintro x ⟨K', hK', hx, hx2⟩
    by_cases hKK : K' = K
    · subst hKK
      exact rr_inv_mem_cSec h44 hG hK' hx.2 hx2
    · exact le_cSec_of_ne (rr_pcomp hK') (rr_pcomp hK) hKK hx.2
  exact hle hcl

theorem lpFull (hLP : L292LP) (h44 : II4_44) (hquat : II4_4_quat) (hG : IsKProperSimple G)
    (hgen : Gen4 G) (h3 : 3 ≤ pRank 2 G) {a b : G} (hb : orderOf b = 2)
    (hab : b ∈ centralizer ({a} : Set G)) (hbK : ∀ K, IsRigidRankOneComp a K → b ∈ cSec K)
    {y : G} (hy : y ∈ zStar (rigidProduct a)) (hy2 : ∃ n : ℕ, y ^ (2 ^ n) = 1)
    (hyb : y ∈ centralizer ({b} : Set G)) : y ∈ zStar (rigidProduct b) := by
  have hyC : y ∈ centralizer ({a} : Set G) :=
    rigidProduct_le_cent a (Subgroup.mem_inf.1 hy).1
  have hyb' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 hyb
  have hb2 : ∃ n : ℕ, b ^ (2 ^ n) = 1 := ⟨1, by
    have := pow_orderOf_eq_one b
    rwa [hb, ← pow_one 2] at this⟩
  have hH : IsPGroup 2 ↥(zpowers y ⊔ zpowers b) := isPGroup_zpowers_sup hy2 hb2 hyb'
  have hHC : zpowers y ⊔ zpowers b ≤ centralizer ({a} : Set G) :=
    sup_le (zpowers_le.2 hyC) (zpowers_le.2 hab)
  obtain ⟨T, hT, hHT⟩ := exists_isSylowOf_ge' hHC hH
  have hyT : y ∈ T := hHT (Subgroup.mem_sup_left (mem_zpowers y))
  have hbT : b ∈ T := hHT (Subgroup.mem_sup_right (mem_zpowers b))
  have hcl := zStruct hquat hG hgen hT y ⟨hyT, hy⟩
  have hle : Subgroup.closure (zGen a T) ≤ zStar (rigidProduct b) := by
    rw [Subgroup.closure_le]
    rintro w ⟨K, hK, hwTK, hw2⟩
    have hwb : w * b = b * w := comm_of_mem_cSec hT.isPGroup hwTK.1 hbT hwTK.2 (hbK K hK)
    refine hLP G hG h3 a b K hK hb hab (hbK K hK) w (mem_zStar_of_involution h44 hG hK hwTK.2 hw2)
      ⟨1, ?_⟩ (Subgroup.mem_centralizer_singleton_iff.2 hwb)
    have := pow_orderOf_eq_one w
    rwa [hw2, ← pow_one 2] at this
  exact hle hcl

end CFSG.GH74.GLS.Bg.Pu5
