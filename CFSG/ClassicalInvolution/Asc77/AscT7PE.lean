module

public import CFSG.ClassicalInvolution.Asc77.AscT7PB
public import CFSG.ClassicalInvolution.Asc77.AscT7PD
public import CFSG.ClassicalInvolution.Asc77.AscT7NI

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
  CFSG.ClassicalInvolution.Disconnected

namespace T7P

section Transport

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

omit [Finite G] in
theorem dConnected_congr {Φ₁ Φ₂ : Set (Subgroup G)} {Y₁ Y₂ : Subgroup G} (hΦ : Φ₁ = Φ₂)
    (hY : Y₁ = Y₂) :
    DConnected (quotFamily (restrictFamily Φ₁ Y₁) (classicalInvolutionOddCore ↥Y₁)) ↔
      DConnected (quotFamily (restrictFamily Φ₂ Y₂) (classicalInvolutionOddCore ↥Y₂)) := by
  subst hΦ hY
  exact Iff.rfl

theorem sectionDConnected_iff_secFam (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    SectionDConnected Ω c ↔ DConnected (secFam Ω c) := by
  unfold SectionDConnected
  exact dConnected_congr
    ((sectionFamily_zpowers hΩ hc2).trans (centMembers_exactFamily Ω c).symm)
    (sectionHull_zpowers hΩ hc2)

end Transport

section Main

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


variable (p f) in
@[expose] def SpinSectionConn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W → u ∈ W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → dComp Ω K ≠ dstarComp Ω K →
        SectionConnected Ω u → SpinSection p f Ω u →
          rLayer Ω u ≤ sigmaGen Ω K ∨ rLayer Ω u ≤ rLayer Ω (t * z)

variable (p f) in
@[expose] def SpinSectionRecog : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W → u ∈ W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → dComp Ω K ≠ dstarComp Ω K →
        SectionConnected Ω u → SpinSection p f Ω u → False

theorem spinSectionConn_of_recog (h : SpinSectionRecog p f) : SpinSectionConn p f :=
  fun G _ _ _ Ω K K' z u J t W hH huW hα hne hconn hspin =>
    (h G Ω K K' z u J t W hH huW hα hne hconn hspin).elim

theorem c21_14_Y_conn_W_of_spinSectionConn (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hSpin : SpinSectionConn p f) : C21_14_Y_conn_W p f := by
  have hC3 : C21_3 p f := c21_3_of_hyp51 hHt hHu
  intro G _ _ _ Ω K K' z u J t W h huW hα hne hconn
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one h.hu2
  by_cases hD : SectionDConnected Ω u
  · exact Or.inl (Hyp21.rLayer_u_le_sigmaGen_of_dconn h hα hD)
  have hdisc : ¬ DConnected (secFam Ω u) := fun hc =>
    hD ((sectionDConnected_iff_secFam hΩ hc2).mpr hc)
  rcases Hyp21.zt_or_spin_of_not_dConnected h hdisc with htriv | htriv | hspin
  · exact Or.inl (h.rLayer_u_le_sigmaGen_of_trivial hα (c₀ := z) (Or.inl rfl) htriv
      fun R hR hRz => h.rSet_le_sigmaGen_of_le_centralizer hR hRz)
  · right
    have hY := h.rLayer_u_le_centralizer_tz_of_trivial hC3 hα htriv
    refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
    have hRY : R ≤ rLayer Ω u := le_iSup₂_of_le R hR (le_iSup_of_le hRc le_rfl)
    exact le_iSup₂_of_le R hR (le_iSup_of_le (hRY.trans hY) le_rfl)
  · exact hSpin G Ω K K' z u J t W h huW hα hne hconn hspin

theorem c21_14_Y_conn_W_of_spinRecog (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hSpin : SpinSectionRecog p f) : C21_14_Y_conn_W p f :=
  c21_14_Y_conn_W_of_spinSectionConn hHt hHu (spinSectionConn_of_recog hSpin)

theorem c21_14_Y_conn_W_iff_spinSectionConn (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) : C21_14_Y_conn_W p f ↔ SpinSectionConn p f :=
  ⟨fun hc G _ _ _ Ω K K' z u J t W h huW hα hne hconn _ =>
    hc G Ω K K' z u J t W h huW hα hne hconn,
    c21_14_Y_conn_W_of_spinSectionConn hHt hHu⟩

end Main

end T7P

end CFSG.ClassicalInvolution.Asc77
