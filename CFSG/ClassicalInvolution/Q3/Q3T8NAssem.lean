module

public import CFSG.ClassicalInvolution.Q3.Q3T8N03

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

section Assem


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem fuzzyFrame3_of_triFrame {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}
    (hΩ : HypOmegaMod Ω) (hΩu : HypOmegaModU (.sl2 3 1) Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (hF : T8T.TriFrame Ω M x R)
    (hind : x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G)) :
    Q3NL.FuzzyFrame3 Ω (Subgroup.closure ({x 0, x 1, x 2} : Set G)) := by
  have hrange : Set.range x = ({x 0, x 1, x 2} : Set G) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hc01 := hF.comm hΩ 0 1
  have hc02 := hF.comm hΩ 0 2
  have hc12 := hF.comm hΩ 1 2
  have hcl : ∀ i, Q3.IsClassicalMember3 (M i) (x i) := fun i => by
    obtain ⟨w, hw⟩ := hΩu.classical (M i) (hF.mem i)
    have hwt : w = x i := (hw.isUniqueInvolution_sl2).eq (hF.inv i)
    subst hwt
    exact hw.toQ3 (by norm_num)
  refine ⟨M, x, fun i => ⟨hF.mem i, hcl i⟩, ?_,
    T8T.isElemAbelian_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) hc01 hc02 hc12,
    T8T.natCard_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) hc01 hc02 hc12 (hF.ne_one 0)
      (hF.ne_one 1) (hF.x_ne hnt (i := 0) (j := 1) (by decide)) (hF.ne_one 2) hind,
    fun i => hF.le_trivialOnQuot hΩ hnt i⟩
  rw [hrange]

theorem c27_alphaConst_proved3 (hα : AlphaFrame3) (h2 : C27_2) (h4 : C27_4) :
    T8T.C27_AlphaConst := by
  intro G _ _ _ Ω K hst hnt hdisc hμ z hz J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2'
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hnt' : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hst.trans hnt hM
  by_cases hframe : ∃ A₀ : Subgroup G, Q3NL.FuzzyFrame3 Ω A₀
  · exact hα G Ω K hst hnt hframe z hz J₂ hJ₂ J₁ hJ₁ t₂ t₁ h2' h1
  · exfalso
    obtain ⟨W₀, hW₀, hab₀, hE4₀⟩ := hμ
    have key : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
        Subgroup.centralizer ({z * s} : Set G) ≤ sigmaNorm Ω K := by
      intro M hM s hs'
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hst hnt hdisc z hz M hM s hs'
      obtain ⟨e⟩ := l7_5_2_proved G Ω hst.modU W₀ hW₀ W' hstd.hW.1
      obtain ⟨hab', hE4'⟩ := T8T.muAbelian_notE4_transfer e hab₀ hE4₀
      have hx : z * s * (z * s) = 1 := Q3CL.T8.mul_self_zt hΩ hz hM hs'
      have hKx : T8.XMem Ω (z * s) K := Layer.xMem_zt3 hstd
      have hKt : K ∈ Q3NL.tqMembers3 Ω (z * s) := hKx.mem_tqMembers3 hΩ hx
      have hs3 : Q3.Disc3.AscStand3 Ω K := hst.toStand3
      have hL : Layer.LayerHyp Ω (z * s) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
      have hcomp := h2 G Ω K M S' R' T' W' z s hstd hdisc
      have hconn := T8.dstarConnected_layerFam3_of_abelian hstd hE4' hab'
      by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω M → ∀ z' : G,
          IsUniqueInvolution K' z' → z' ≠ z * s
      · exfalso
        apply hframe
        obtain ⟨K'', R'', z'', hF, hind⟩ := T8T.exists_triFrame_of_std8 hstd hE4' hab' hE8
        exact ⟨_, fuzzyFrame3_of_triFrame hΩ hst.modU hnt' hF hind⟩
      · push Not at hE8
        obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
        have hY : oddCoreOf (Q3NL.exactLayer3 Ω (z * s)) ≤ sigmaNorm Ω K :=
          T8.oddCoreOf_layerJoin_le_of_zt hstd hK' (hzt ▸ hz')
        have hY1 : Q3NL.exactLayer3 Ω (z * s) ≤ sigmaNorm Ω K :=
          Layer.exactLayer3_le_sigmaNorm_of_lift hL hKt hcomp hY hconn
        exact Layer.centralizer_le_sigmaNorm_of_exactLayer3_le hstd hY1
    obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hst hnt hdisc z hz J₁ hJ₁ t₁ h1
    have htop : T8.H274 Ω K z = ⊤ := h4 G Ω K J₁ S' R' T' W' z t₁ hstd hdisc
    have hle : T8.H274 Ω K z ≤ sigmaNorm Ω K :=
      sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => key M hM s hs')
    rw [htop] at hle
    exact hdisc (dConnected_of_sigmaNorm_eq_top hst.mem hst.trans (top_le_iff.mp hle))

theorem c27_Oab3_of_inputs (hα : AlphaFrame3) (hH : T8T.Hyp51Tri) (h2 : C27_2) (h4 : C27_4) :
    C27_Oab3 :=
  c27_Oab_of_alphaNorm h2 h4 hH
    (c27_alphaNorm_of_alphaConst h2 hH (c27_alphaConst_proved3 hα h2 h4))

theorem c27_YnE4_of_core3 (h2 : C27_2) (hO : C27_Oab3) (hY : C27_Ysmall3) : C27_YnE43 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hcomp := h2 G Ω K J S R T W z t hs hdisc
  by_cases hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x
  · refine Layer.exactLayer3_le_sigmaNorm_of_lift hL hKt hcomp ?_
      (T8.dstarConnected_layerFam3_of_abelian hs hE4 hab)
    by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G,
        IsUniqueInvolution K' z' → z' ≠ z * t
    · exact hO G Ω K J S R T W z t hs hdisc hE4 hab hE8
    · push Not at hE8
      obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
      exact T8.oddCoreOf_layerJoin_le_of_zt hs hK' (hzt ▸ hz')
  · by_cases hconn : T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))
    · exact Layer.exactLayer3_le_sigmaNorm_of_lift hL hKt hcomp
        (T8.oddCoreOf_layerJoin_le_of_nonabelian hs hcomp hab) hconn
    · exact hY G Ω K J S R T W z t hs hdisc hE4 hab hconn

theorem c27_8nE4_of_YnE4 (h : C27_YnE43) : C27_8nE4 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  exact Layer.centralizer_le_sigmaNorm_of_exactLayer3_le hs
    (h G Ω K J S R T W z t hs hdisc hE4)

end Assem

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
