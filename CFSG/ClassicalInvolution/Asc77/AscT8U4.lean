module

public import CFSG.ClassicalInvolution.Asc77.AscT8U3
public import CFSG.ClassicalInvolution.Asc77.AscT8T11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance.Theorem5 (FuzzyFrameOn)

namespace T8U

section Main

variable (p f : ℕ) [Fact p.Prime]

theorem c27_alphaConst_proved (hD4 : Ih8D4Star p f) (h2 : C27_2 p f) (h4a : C27_4a p f) :
    T8T.C27_AlphaConst p f := by
  intro G _ _ _ Ω K hst hnt hdisc hμ z hz J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2'
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hnt' : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hst.trans hnt hM
  by_cases hframe : ∃ A₀, FuzzyFrameOn p f Ω A₀
  · exact alphaOf_eq_of_omegaNbr_frame hst hnt hframe hz h2' h1 hJ₂ hJ₁
  · exfalso
    obtain ⟨W₀, hW₀, hab₀, hE4₀⟩ := hμ
    have key : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
        Subgroup.centralizer ({z * s} : Set G) ≤ sigmaNorm Ω K := by
      intro M hM s hs'
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hst hnt hdisc z hz M hM s hs'
      obtain ⟨e⟩ := l7_5_2_proved p f hp hq G Ω hΩ W₀ hW₀ W' hstd.hW.1
      obtain ⟨hab', hE4'⟩ := T8T.muAbelian_notE4_transfer e hab₀ hE4₀
      have hx : z * s * (z * s) = 1 := T8.mul_self_zt hp hΩ hz hM hs'
      have hKx : T8.XMem Ω (z * s) K := T8.xMem_zt hstd
      have hcomp := h2 G Ω K M S' R' T' W' z s hstd hdisc
      have hconn := T8.dstarConnected_layerFamQ_of_abelian hD4 hstd hE4' hab'
      by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω M → ∀ z' : G,
          IsUniqueInvolution K' z' → z' ≠ z * s
      · exfalso
        apply hframe
        obtain ⟨K'', R'', z'', hF, hind⟩ := T8T.exists_triFrame_of_std8 hstd hE4' hab' hE8
        exact ⟨_, fuzzyFrameOn_of_triFrame hp hq hΩ hnt' hF hind⟩
      · push Not at hE8
        obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
        have hY : oddCoreOf (T8.layerJoin Ω (z * s)) ≤ sigmaNorm Ω K :=
          T8.oddCoreOf_layerJoin_le_of_zt hstd hK' (hzt ▸ hz')
        have hY1 : T8.layerJoin Ω (z * s) ≤ sigmaNorm Ω K :=
          T8.layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hcomp hY hconn
        exact T8.centralizer_le_sigmaNorm_of_layerJoin_le hstd hY1
    obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hst hnt hdisc z hz J₁ hJ₁ t₁ h1
    have hcomp := h2 G Ω K J₁ S' R' T' W' z t₁ hstd hdisc
    have htop : T8.H274 Ω K z = ⊤ := s26_H274_eq_top h4a hstd hdisc hcomp
    have hle : T8.H274 Ω K z ≤ sigmaNorm Ω K :=
      sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => key M hM s hs')
    rw [htop] at hle
    exact hdisc (dConnected_of_sigmaNorm_eq_top hst.mem hst.trans (top_le_iff.mp hle))

theorem thm8A_of_three_residuals (h13 : C26_13_sc p f) (hE : C27_8E4 p f)
    (hY : C27_Ysmall p f) : Thm8A p f := by
  have h26_2 : C26_2 p f := c26_2_of_c26_1_muZ2 (T8R.c26_1 p f) s26XMuZ2_proved
  have h26_13 : C26_13 p f := c26_13_of_sc h13
  have h2 : C27_2 p f := c27_2_of_c26_2_c26_13 h26_2 h26_13
  have h4a : C27_4a p f := c27_4a_of_min h2 c27_4M_proved
  exact thm8A_of_residuals_alphaConst p f h13 hE hY
    (c27_alphaConst_proved p f ih8D4Star h2 h4a)

end Main

end T8U

end CFSG.ClassicalInvolution.Asc77
