module

public import CFSG.ClassicalInvolution.Asc77.AscT7NH
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RL

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
@[expose] def C21_14_Y_conn_W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W → u ∈ W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → dComp Ω K ≠ dstarComp Ω K →
        SectionConnected Ω u →
          rLayer Ω u ≤ sigmaGen Ω K ∨ rLayer Ω u ≤ rLayer Ω (t * z)

theorem c21_14_Y_ne_W_of_conn_W (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hc : C21_14_Y_conn_W p f) : C21_14_Y_ne_W p f := by
  intro G _ _ _ Ω K K' z u J t W h huW hα hne
  by_cases hconn : SectionConnected Ω u
  · exact hc G Ω K K' z u J t W h huW hα hne hconn
  · exact ((c21_14_Y_disc_of_hyp51 hHt hHu) G Ω K K' z u J t W h hconn).2 hα

theorem c21_normCent_of_conn_W (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hc : C21_14_Y_conn_W p f) : C21_NormCent p f :=
  c21_normCent_of_Y_ne (c21_3_of_hyp51 hHt hHu) (c21_14_Y_ne_W_of_conn_W hHt hHu hc)

theorem c21_14_Y_conn_W_of_normCent (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hN : C21_NormCent p f) : C21_14_Y_conn_W p f := by
  intro G _ _ _ Ω K K' z u J t W h _ hα hne _
  rcases c21_14_alt_rest_of (c21_3_of_hyp51 hHt hHu) (c21_14_Y_disc_of_hyp51 hHt hHu) hN
    G Ω K K' z u J t W h hα (fun hh => hne hh.1) with h1 | h2
  · exact Or.inl h1
  · refine Or.inr (iSup₂_le fun R hR => iSup_le fun hRC => ?_)
    exact le_iSup₂_of_le R hR (le_iSup_of_le (fun x hx => h2 (hRC hx)) le_rfl)

theorem c21_14_Y_conn_W_iff_normCent (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) :
    C21_14_Y_conn_W p f ↔ C21_NormCent p f :=
  ⟨c21_normCent_of_conn_W hHt hHu, c21_14_Y_conn_W_of_normCent hHt hHu⟩

theorem c21_14_alt_rest_iff_normCent (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) :
    C21_14_alt_rest p f ↔ C21_NormCent p f :=
  have hC3 := c21_3_of_hyp51 hHt hHu
  ⟨c21_normCent_of_alt_rest hC3, c21_14_alt_rest_of hC3 (c21_14_Y_disc_of_hyp51 hHt hHu)⟩

variable (p f) in
theorem c21_2_final_T (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (hc : C21_14_Y_conn_W p f) : C21_2 p f :=
  c21_2_final_S p f hNT hHt hHu (c21_normCent_of_conn_W hHt hHu hc)

theorem thm7A_of_inputs₉
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (hc : C21_14_Y_conn_W p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (h234 : C23_4 p f) (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (h248 : C24_8 p f) (h249 : C24_9 p f) (hchain24 : C24_chain p f)
    (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f :=
  thm7A_of_inputs₈ hHt hHu (c21_normCent_of_conn_W hHt hHu hc) hH22z hH22u
    h224σ h224c h228 hchain22 h234 h235 h237 hΓ hnoZ hgen hchain23 h248 h249 hchain24 h2519 h2521

end CFSG.ClassicalInvolution.Asc77
