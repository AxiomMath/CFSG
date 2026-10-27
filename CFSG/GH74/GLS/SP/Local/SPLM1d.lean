module

public import CFSG.GH74.GLS.SP.Local.SPLM1c

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

theorem splLeafM1 :
    ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D₃ : SPLNot3 G,
      SPLSetup D₃.toSPLNot0 → SPL2Set D₃.toSPLNot1 → SPL2Ct D₃.toSPLNot2 → SPL2Ord D₃.toSPLNot0 →
        SPL3M2 D₃ → ∃ D : SPLNot4 G, D.toSPLNot3 = D₃ ∧ SPL3M1 D := by
  intro G _ _ hG D₃ hs h1 hct hord h3
  obtain ⟨J, hJK, hJL2, hY₁J, hY₁s, hNY, hNH, hJB, hJgen⟩ := exists_J D₃ hs h1 h3
  have hzJ : D₃.z * D₃.w ∈ J := by
    have hmem : D₃.z * D₃.w ∈ normalizer (D₃.H₀ : Set G) ⊓ J := by
      rw [hNH]; exact Subgroup.mem_sup_right (mem_zpowers _)
    exact hmem.2
  refine ⟨⟨D₃, J⟩, rfl, ?_⟩
  obtain ⟨hbru, hBN, htBt⟩ := l5_core (⟨D₃, J⟩ : SPLNot4 G) hs h1 h3 h3.a_facts hJB
  exact
    { J_le := hJK
      J_L2 := hJL2
      Y₁_le := hY₁J
      Y₁_syl := hY₁s
      NJ_Y₁ := hNY
      NJ_H₀ := hNH
      M₁_eq := M₁_eq_union D₃ hs h1 h3 hbru
      tBt := htBt
      B_inf_N := hBN
      R₁_normal := M₁_le_normalizer_R₁ D₃ hs h1 h3
      R₁_eab := ⟨R₁_comm D₃ hs h3, R₁_exp D₃ hs h3⟩
      R₁_card := R₁_card_three D₃ hs h1 h3
      J₁_le := J₁_le_M₁ (⟨D₃, J⟩ : SPLNot4 G) hs h1 h3 hJgen
      R₁J₁_normal := R₁J₁_normal' (⟨D₃, J⟩ : SPLNot4 G) hs h1 h3 hJgen
      M₁_eq_RJH := M₁_eq_RJH' (⟨D₃, J⟩ : SPLNot4 G) hs h1 h3 hJgen hzJ
      M₁_eq_BJ := M₁_eq_BJ' (⟨D₃, J⟩ : SPLNot4 G) hs h1 h3 hJgen hzJ
      H_split := H_split' D₃ hs h1
      H₀_card := H₀_card' D₃ hs h1
      H₀_cen := fun i hi j hj => by
        have h := H₀_cen_J₁ (⟨D₃, J⟩ : SPLNot4 G) hs h1 h3 hJgen i hi j hj
        have : ⁅i, j⁆ = 1 := by
          rw [commutatorElement_def, h]; group
        rw [this]; exact Subgroup.one_mem _
      bruhat₁ := hbru }

end CFSG.GH74.GLS.SP.Local
