module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327p

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem inf_M_eq_T_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {hU : IsElemAbelian 2 (S.UH H)}
    {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))} (B : TwoBlocks hU H T K₁ K₂)
    (htop : commV K₁ ⊔ commV K₂ = ⊤) :
    H ⊓ Subgroup.normalizer (L : Set G) = T := by
  classical
  set M := Subgroup.normalizer (L : Set G) with hM
  have hTH : T ≤ H := hH.1.1
  have hTM : T ≤ M := S.T_le_NL
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hCU : H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H :=
    S.centralizer_UH_le_pCoreOf_all_F4 h331 h1222 h5172 hH hHZ hsolv
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := B.le_norm

  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨y₂, hy₂, hy₂3, hy₂1⟩ := S1417.exists_orderThree B.nat₂
  obtain ⟨t, htT, ht⟩ := B.swap
  have hJH := (E2_3_two_sylow_of_isSolvable hU (S.hyp501.minParabolic_of_isHStar_F4 h331 hH).1
    hsolv (fun p hp hp2 => by
      obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
      have : Fact p.Prime := ⟨hp⟩
      have h1 := hq p hp hp2
      rwa [← pRank_top_subtype]) (conjClosure_isTwoReducedIn_of_charTwo hsyl
        (S.charTwo_of_inH hH.1) le_rfl).2.2
    (S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ)).2
  rw [B.eqJ] at hJH
  obtain ⟨s₁, s₂, a₁, a₂, hd⟩ :=
    S1417.exists_sylowData hJH B.nat₁ B.nat₂ B.comm B.inf B.commV_inf htop
  have hs₁sq : s₁ ^ 2 = 1 := by
    rcases hd.inf₁ (s₁ ^ 2) (Subgroup.pow_mem _ hd.s₁_mem_S 2) (K₁.pow_mem hd.s₁_mem_L 2) with
      h | h
    · exact h
    · exfalso
      apply hd.s₁_ne
      have : s₁ * s₁ = s₁ * 1 := by rw [← sq, h, mul_one]
      exact mul_left_cancel this
  have hs₁T : s₁ ∈ autI hU T := autI_mono hU (thompsonJ_le_self T) hd.s₁_mem_S

  set Y := autI hU (twoResidual H ⊓ M) with hYdef
  have hYL : Y ≤ autI hU (twoResidual H) := autI_mono hU inf_le_left
  have hTY : autI hU T ≤ Subgroup.normalizer (Y : Set (MulAut (IntMod (S.UH H) hU))) := by
    intro g hg
    obtain ⟨t₀, ht₀T, rfl⟩ := (mem_autI hU).1 hg
    have hmem : ∀ (s : G) (hs : s ∈ T) (hsN : s ∈ Subgroup.normalizer (S.UH H : Set G)),
        ∀ φ ∈ Y, convI hU ⟨s, hsN⟩ * φ * (convI hU ⟨s, hsN⟩)⁻¹ ∈ Y := by
      intro s hs hsN φ hφ
      obtain ⟨x, hx, rfl⟩ := (mem_autI hU).1 hφ
      rw [← map_inv, ← map_mul, ← map_mul]
      refine (mem_autI hU).2 ⟨⟨s, hsN⟩ * x * (⟨s, hsN⟩)⁻¹, ⟨?_, ?_⟩, rfl⟩
      · show s * (x : G) * s⁻¹ ∈ twoResidual H
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H (hTH hs)) x).mp hx.1
      · show s * (x : G) * s⁻¹ ∈ M
        exact M.mul_mem (M.mul_mem (hTM hs) hx.2) (M.inv_mem (hTM hs))
    refine B6.mem_normalizer_of_forall_mem (fun φ hφ => hmem t₀ ht₀T t₀.2 φ hφ) fun φ hφ => ?_
    have := hmem (t₀ : G)⁻¹ (T.inv_mem ht₀T) (Subgroup.inv_mem _ t₀.2) φ hφ
    rw [show (⟨(t₀ : G)⁻¹, Subgroup.inv_mem _ t₀.2⟩ : ↥(Subgroup.normalizer (S.UH H : Set G))) =
      t₀⁻¹ from rfl, map_inv, inv_inv] at this
    exact this
  by_cases hY1 : Y = ⊥
  ·
    have hLM : twoResidual H ⊓ M ≤ T := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (S.UH H : Set G) := hHN (twoResidual_le H hx.1)
      have h1 : convI hU ⟨x, hxN⟩ = 1 := by
        have : convI hU ⟨x, hxN⟩ ∈ Y := convI_mem_autI hU hx hxN
        rwa [hY1, Subgroup.mem_bot] at this
      exact hOT (hCU ⟨twoResidual_le H hx.1, (convI_eq_one_iff hU _).1 h1⟩)
    refine le_antisymm (fun x hx => ?_) (le_inf hTH hTM)
    have hx' : x ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by
      rw [twoResidual_eq_oTwoUpper', ← eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl]; exact hx.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hTH.trans (le_normalizer_twoResidual H))]
      at hx'
    obtain ⟨l, hl, s, hs, rfl⟩ := hx'
    have hlM : l ∈ M := by
      have e : l = l * s * s⁻¹ := by group
      rw [e]; exact M.mul_mem hx.2 (M.inv_mem (hTM hs))
    exact T.mul_mem (hLM ⟨hl, hlM⟩) hs
  ·
    exfalso
    have hYeq := B.eq_of_normalized hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1 hs₁T hd.s₁_mem_L hs₁sq hd.s₁_ne
      htT ht hYL hY1 hTY
    have hLM : twoResidual H ≤ M := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (S.UH H : Set G) := hHN (twoResidual_le H hx)
      have h1 : convI hU ⟨x, hxN⟩ ∈ Y := by rw [hYeq]; exact convI_mem_autI hU hx hxN
      obtain ⟨y, hy, hyx⟩ := (mem_autI hU).1 h1
      have hu : (y : G)⁻¹ * x ∈ H ⊓ Subgroup.centralizer (S.UH H : Set G) := by
        refine ⟨H.mul_mem (H.inv_mem (twoResidual_le H hy.1)) (twoResidual_le H hx), ?_⟩
        have h2 : convI hU (y⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
        exact (convI_eq_one_iff hU _).1 h2
      have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
      rw [e]
      exact M.mul_mem hy.2 (hTM (hOT (hCU hu)))
    apply hH.2.1
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl, ← twoResidual_eq_oTwoUpper']
    exact sup_le hLM hTM

end Setting

end CFSG.Quasithin.H13.A5
