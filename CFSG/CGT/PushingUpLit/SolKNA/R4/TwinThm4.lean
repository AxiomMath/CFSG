module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinMainB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Sec
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

theorem thm4TwinRes2C_of_four_le {r n : ℕ} (hr : 4 ≤ r) : Thm4TwinRes2C r n :=
  thm4TwinRes2C_of_res2CD fun G _ _ hG J L hm hgen u v hu hv hinu hinv hvJ h4 => by
    have := hm.hyp.le_three_of_not_mem_normalizer hm.memJ hm.memL hu hv hinu hinv hvJ
    omega

theorem thm4TwinThmA_all (r : ℕ) : Thm4TwinThmA r := by
  intro G _ _ Δ h J hJ u hu hno A hA x hx
  have hr3 : 3 ≤ r := h.three_le hJ
  have hle : J ≤ Subgroup.normalizer (A : Set G) := by
    rw [← h.gen hJ, Subgroup.closure_le]
    rintro y ⟨hyJ, hy2⟩
    have hy2' : IsPGroup 2 ↥((Subgroup.zpowers y).subgroupOf J) :=
      hy2.comap_of_injective _ (Subgroup.subtype_injective _)
    obtain ⟨S, hS⟩ := hy2'.exists_le_sylow
    have hyS : y ∈ (S : Subgroup J).map J.subtype :=
      ⟨⟨y, hyJ⟩, hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)), rfl⟩
    have hd := h.q8Datum hJ hu S
    have hq : Nonempty (↥(S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))) := by
      obtain ⟨e⟩ := h.quat J hJ _ (isSylow2In_map_sylow J S)
      exact ⟨((S : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans e⟩
    exact mem_normalizer_iff_conjSub_eq.mpr
      (thmA_twinK hd (exists_S₀_pairK hd hr3 hq) (inv_in_S₀K hd hr3 hq)
        (fun _ _ hs hsA => exists_sq_of_conjSub_neK hd hr3 hq hs hsA)
        (h.hypOmegaGen_conjClass hJ) h.odd hno hA hyS)
  exact mem_normalizer_iff_conjSub_eq.mp (hle hx)

theorem thm4RTwinBelow_of_res2F'_of_four_le {r n : ℕ} (hr : 4 ≤ r)
    (h2f : Thm4TwinRes2F' r n) : Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_residuals (thm4TwinThmA_all r) (thm4TwinRes2C_of_four_le hr)
    (thm4TwinRes2F_of_res2F' (thm4TwinThmA_all r) h2f)

structure F2ConfigR (r : ℕ) {G : Type} [Group G] [Finite G] (J L L₀ : Subgroup G) : Prop where
  min : TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L
  gen : omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤
  noInvO2 : TL4.NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L)
  isComp : CFSG.IsComponent L₀
  normal : L₀.Normal
  layerEq : layer G = L₀
  fittingEq : generalizedFitting G = L₀ ⊔ pCore 2 G
  pCoreEq : pCore 2 G = Subgroup.center G
  centralizerEq : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G
  invMem : ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
    IsUniqueInvolution K z → z ∈ L₀

@[expose] def Thm4TwinEdgelessModelR (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L L₀ : Subgroup G,
    F2ConfigR r J L L₀ → ∀ W : Subgroup G, J ≤ W → IsSubnormal W ⊤ →
      (⨆ x : W, conjSub (x : G) J) = W → ¬ PhilipHall.Frame.HasTwin (J.subgroupOf W) →
        TightEdgeless (J.subgroupOf W) → False

section Cit3

theorem F2ConfigR.exists_edgeless_section {r n : ℕ} (hr : 4 ≤ r) (h4 : NoQ16E4)
    (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n) {G : Type} [Group G] [Finite G]
    (hG : Nat.card G < n) {J L L₀ : Subgroup G} (hc : F2ConfigR r J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) :
    ∃ W : Subgroup G, K ≤ W ∧ IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : G) K) = W ∧
      ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W) ∧ TightEdgeless (K.subgroupOf W) := by
  set Δ := CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L
  have hm := hc.min
  obtain ⟨z, hz⟩ := (hm.hyp.hyp.omega1 K hK).1
  obtain ⟨W, hKW, hWs, hWg⟩ := F2.exists_section K
  refine ⟨W, hKW, hWs, hWg, ?_⟩
  have hO : classicalInvolutionOddCore ↥W = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hm.hyp.odd W hWs
  have hlt : Nat.card W < n := lt_of_le_of_lt (Subgroup.card_le_card_group W) hG
  have hΔW : TwinT4Hyp r ↥W (restrictFamily Δ W) := hm.hyp.restrict W hO
  set R : Subgroup ↥W := K.subgroupOf W with hR
  set t : ↥W := ⟨z, hKW hz.mem⟩
  have hRΔ : R ∈ restrictFamily Δ W := subgroupOf_mem_restrictFamily hK hKW
  have hut : IsUniqueInvolution R t := isUniqueInvolution_subgroupOf hz hKW
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  have hd : Q8TwinDatum R S t := hΔW.q8Datum hRΔ hut S
  have hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    obtain ⟨e⟩ := hΔW.quat R hRΔ _ (isSylow2In_map_sylow R S)
    exact ⟨((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).trans e⟩
  have htc : tightCore R = R := hΔW.tightCore_eq hRΔ
  have hΩR : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := by
    rw [htc]; exact hypOmegaGen_conjClass_section hm.hyp.hyp hK hKW
  have hAR : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [htc, ← restrictFamily_conjFamily hKW]
    exact aEmpty_restrict hm.hyp.hyp (conjFamily_subset hm.hyp.hyp.conjInvariant hK W) hKW
      (hm.hyp.aEmpty K hK)
  have hconj : ∀ g : ↥W, (conjSub g R).map W.subtype = conjSub (g : G) K := by
    intro g
    have hle : conjSub (g : G) K ≤ W := by
      have := conjSub_mono (n := (g : G)) hKW
      rwa [conjSub_eq_self_of_mem g.2] at this
    rw [hR, conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenW : (⨆ g : ↥W, conjSub g R) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hWg
  have hgenR : TightSelfGen R := by
    show (⨆ g : ↥W, conjSub g (tightCore R)) = ⊤
    rw [htc]; exact hgenW
  have hnoO2 : ¬ TightInO2 t := fun h => hc.noInvO2 K hK z hz (F2.tightInO2_of_subnormal hWs _ h)
  have hout := datumOutcomeR_of_IH hr hT hB hlt hd hq hgenR hO htc hΩR hAR
  by_cases htw : PhilipHall.Frame.HasTwin R
  · exfalso
    rcases hout.1 htw with h | h
    · exact hnoO2 h
    · exact hnoO2 (tightInO2_of_twinE4' hr h4 hd hq h)
  · refine ⟨htw, ?_⟩
    rcases hout.2 htw with h | ⟨hedge, -⟩ | ⟨hedge, -⟩ | h
    · exact absurd h hnoO2
    · exact hedge
    · exact hedge
    · obtain ⟨Q, _, f, hfs, hf2, -, hQ⟩ := h
      exact absurd (tightInO2_of_twinE4' hr h4 hd hq ⟨Q, inferInstance, f, hfs, hf2, hQ⟩) hnoO2

theorem thm4TwinRes2F'_of_edgelessModelR {r n : ℕ} (hr : 4 ≤ r) (h4 : NoQ16E4)
    (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n) (hE : Thm4TwinEdgelessModelR r n) :
    Thm4TwinRes2F' r n := by
  intro G _ _ hG J L hm hgen hno L₀ hL₀ hn hlay hfit hZ hC hmem
  have hc : F2ConfigR r J L L₀ := ⟨hm, hgen, hno, hL₀, hn, hlay, hfit, hZ, hC, hmem⟩
  obtain ⟨W, hJW, hWs, hWg, htw, hedge⟩ :=
    hc.exists_edgeless_section hr h4 hT hB hG (Or.inl (CoreAssembly.mem_conjClass_self J))
  exact hE G hG J L L₀ hc W hJW hWs hWg htw hedge

theorem thm4RTwinBelow_of_edgelessModelR {r n : ℕ} (hr : 4 ≤ r) (h4 : NoQ16E4)
    (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n) (hE : Thm4TwinEdgelessModelR r n) :
    Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_res2F'_of_four_le hr (thm4TwinRes2F'_of_edgelessModelR hr h4 hT hB hE)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
