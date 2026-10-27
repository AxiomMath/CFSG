module

public import CFSG.GH74.Uniqueness.SU.SU14Rank3
public import CFSG.GH74.Uniqueness.SU.SU4P189
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.SU.SU4

theorem prop189_rank3 (hKI1 : K.KI1r3) (hKI2 : K.KI2) : Prop189Rank3Stmt := by
  intro G _ _ S U M V x z hc h hrank3
  have hSM : (S : Subgroup G) ≤ M := h.S_le
  have hSyl : IsSylowIn M (S : Subgroup G) := h.isSylowIn_M
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hxM : x ∈ M := hc.x_mem
  have hxS : x ∈ (S : Subgroup G) := hc.x_mem_S
  have hzS : z ∈ (S : Subgroup G) := hc.z_mem_S
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hc.hx ▸ pow_orderOf_eq_one x
  have hGH : SU0.GHGroup (Mbar M) :=
    SU0.GHGroup.of_kgh_quotient h.kgh h.maximal.1 (pPrimeCore 2 ↥M)
  have hO : pPrimeCore 2 (Mbar M) = ⊥ := GLS.pPrimeCore_quotient_eq_bot (↥M)
  obtain ⟨T, hT⟩ := exists_sylow_barImage M hSyl
  have hrank : Open.twoRank (Mbar M) = 3 :=
    (pRank_sylow_eq_twoRank_hbar S hSM).symm.trans hrank3
  have hmov : ∃ u ∈ M, u⁻¹ * z * u ∈ (S : Subgroup G) ∧ u⁻¹ * z * u ≠ z := by
    by_contra hcon
    push Not at hcon
    exact lemma188 G S U M V x z h hc ⟨hzS, fun u hu hu' => hcon u hu hu'⟩
  have hcenter : center (Mbar M) = ⊥ :=
    center_Mbar_eq_bot M hSyl hzS hc.z_unique hmov
  set xb := xbar M x hxM with hxbdef
  have hxbT : xb ∈ (T : Subgroup (Mbar M)) := by
    rw [hT]; exact (mem_barImage M).mpr ⟨⟨x, hxM⟩, hxS, rfl⟩
  have hxb1 : xb ≠ 1 := by
    intro h1
    have h0 : proj M ⟨x, hxM⟩ = proj M 1 := by rw [map_one]; exact h1
    have h2 := eq_of_proj_eq_of_isPGroup M hSp hSM (a := ⟨x, hxM⟩) (b := 1) hxS S.one_mem h0
    have h3 : x = 1 := congrArg Subtype.val h2
    have := hc.hx
    rw [h3, orderOf_one] at this
    omega
  have hxb2 : orderOf xb = 2 := by
    refine orderOf_eq_prime ?_ hxb1
    show (proj M ⟨x, hxM⟩) ^ 2 = 1
    rw [← map_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hx2)
    rw [this, map_one]
  obtain ⟨K', hK1, hK2, hK3, hK4, hK5⟩ := hc.K_ex
  have hV4 : IsFour M V := hc.iso.isFour
  have hVgen : V = zpowers x ⊔ zpowers z := by rw [hc.gen, closure_pair_eq]
  have hrk2 : Open.pRank 2 (centralizer ({xb} : Set (Mbar M))) = 2 :=
    pRank_centralizer_xbar M hxM hx2 hc.syl_c hV4 hVgen hK1 hK3 hK4 hK5
  obtain ⟨p, f, hp, hp2, hL, hPGL⟩ :=
    hKI1 (Mbar M) hGH hO hrank hcenter T xb hxbT hxb2 hrk2
  exact caseB_false M hKI2 h hp hp2 hL hxb2 hPGL

end CFSG.GH74.Uniqueness.SU.SU14
