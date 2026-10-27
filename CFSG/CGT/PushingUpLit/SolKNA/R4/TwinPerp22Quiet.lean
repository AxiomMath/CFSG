module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnHyp51
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth
public import CFSG.ClassicalInvolution.Q3.Q3AM710Cls
public import CFSG.ClassicalInvolution.SmallCases.A7Q3B
public import CFSG.ClassicalInvolution.SmallCases.A7T22H51
public import CFSG.ClassicalInvolution.SmallCases.A7T22ZStar

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

namespace Perp22

section Count


open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem three_le_ncard_twinSet (d : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    3 ≤ (twinSet Ω K).ncard := by
  have hsub : ({K, K', K₃} : Set (Subgroup G)) ⊆ twinSet Ω K := by
    intro M hM
    rcases hM with rfl | rfl | rfl
    · exact mem_twinSet_self d.mem d.hz
    · exact d.hK'
    · exact d.hK₃
  have hc : ({K, K', K₃} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨K, K', K₃, d.hne.symm, d.hK₃K.symm, d.hK₃K'.symm, rfl⟩
  calc 3 = ({K, K', K₃} : Set (Subgroup G)).ncard := hc.symm
    _ ≤ (twinSet Ω K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem exists_fourth_twin (L L' L₃ : Subgroup G) (hge : 4 ≤ (twinSet Ω K).ncard) :
    ∃ M ∈ twinSet Ω K, M ≠ L ∧ M ≠ L' ∧ M ≠ L₃ := by
  by_contra hcon
  push Not at hcon
  have hsub : twinSet Ω K ⊆ ({L, L', L₃} : Set (Subgroup G)) := by
    intro M hM
    by_cases h1 : M = L
    · exact Or.inl h1
    by_cases h2 : M = L'
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hcon M hM h1 h2))
  have h3 : ({L, L', L₃} : Set (Subgroup G)).ncard ≤ 3 := by
    have e1 := Set.ncard_insert_le L ({L', L₃} : Set (Subgroup G))
    have e2 := Set.ncard_insert_le L' ({L₃} : Set (Subgroup G))
    rw [Set.ncard_singleton] at e2
    omega
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

open Classical in
theorem ncard_twins_eq_four (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    (hWyl : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) : (twinSet Ω K).ncard = 4 := by
  have hΩ : HypOmegaGen Ω := hP.hyp
  set S : Finset (Subgroup G) := (Set.toFinite (twinSet Ω K)).toFinset with hSdef
  have hKS : K ∈ S := by simp [hSdef, mem_twinSet_self hd.mem hd.hz]
  have hS : ∀ M ∈ S, M ∈ twinSet Ω K := fun M hM => by simpa [hSdef] using hM
  obtain ⟨W, hW, ρ, hρ⟩ := TwinPerpV3.exists_reps_of_family' hΩ hd.hz S hKS hS
  have hnc : ¬ DbarConnected Ω W :=
    TwinPerpV3.not_dbarConnected_of_wyl' hP hd hperp hW (ρ K) (hρ K hKS) (hWyl W hW)
  set g : Subgroup G → ↥(muGroup Ω W) := fun M => muTabElt (ρ M) with hg
  have hinj : Set.InjOn g (↑S : Set (Subgroup G)) := by
    intro M hM M' hM' e
    have := (Q3T6.Mu.muTabElt_eq_iff hP hW (ρ M) (ρ M')).mp e
    rwa [hρ M hM, hρ M' hM'] at this
  have hset : Star3T.cent (muDelta Ω W) (g K) = ↑(S.image g) := by
    ext y
    constructor
    · intro hy
      rcases Q3AM710.cent_subset hP hW (ρ K) hy with h | ⟨τ, rfl, hτ⟩
      · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨K, hKS, h.symm⟩)
      · have hτK : (τ.K) ∈ twinSet Ω K := by
          rw [← hperp]
          exact Or.inr (by rw [hρ K hKS] at hτ; exact hτ)
        have hτS : τ.K ∈ S := by simpa [hSdef] using hτK
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨τ.K, hτS, ?_⟩)
        exact (Q3T6.Mu.muTabElt_eq_iff hP hW (ρ τ.K) τ).mpr (hρ τ.K hτS)
    · intro hy
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      refine ⟨muTabElt_mem _, ?_⟩
      by_cases hMK : M = K
      · rw [hMK]
      · have hnb : (ρ M).K ∈ omegaNbr Ω (ρ K).K := by
          rw [hρ M hM, hρ K hKS]
          exact TwinPerpV3.adj_of_twins' hd hperp (hS K hKS) (hS M hM) hMK
        exact ((Q3T6.Mu.muTab_commute_iff hP hW (ρ K) (ρ M)
          (by rw [hρ M hM, hρ K hKS]; exact Ne.symm hMK)).mpr hnb).symm
  have hcard : (Star3T.cent (muDelta Ω W) (g K)).ncard = (twinSet Ω K).ncard := by
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]
    exact (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
  have h3 : 3 ≤ (twinSet Ω K).ncard := three_le_ncard_twinSet hd
  have hcube : Q3T8.Asc77.ThompsonCube := fun _ _ _ _ hP' => Q3CL.thompsonCube hP'
  rcases Q3T8.Asc77.thompsonClique G Ω hP W hW hnc (g K) (muTabElt_mem _) with h | h | ⟨h, -⟩ <;>
    omega

end Count

section Quiet


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem exists_tq_of_mem_B' (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {c : G}
    (hc : c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) (hc1 : c ≠ 1) (hcz : c ≠ z) :
    ∃ J : Subgroup G, (J = K ∨ J = K' ∨ J = K₃) ∧ c ∈ Balance.Bootstrap.trivialOnQuot J := by
  have hΩ := h.hyp
  have t₁₃ : u₁ ∈ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ h.mem h.hK₃.1 h.hK₃K.symm h.hz h.hzK₃ h.hu₁.1
  have t₂₃ : u₂ ∈ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ h.hK'.1 h.hK₃.1 h.hK₃K'.symm h.hzK' h.hzK₃ h.hu₂.1
  have t₂₁ : u₂ ∈ Balance.Bootstrap.trivialOnQuot K :=
    A7T22.le_trivialOnQuot_of_twin hΩ h.hK'.1 h.mem h.hne h.hzK' h.hz h.hu₂.1
  have t₃₁ : u₃ ∈ Balance.Bootstrap.trivialOnQuot K :=
    A7T22.le_trivialOnQuot_of_twin hΩ h.hK₃.1 h.mem h.hK₃K h.hzK₃ h.hz h.hu₃.1
  have t₁₂ : u₁ ∈ Balance.Bootstrap.trivialOnQuot K' :=
    A7T22.le_trivialOnQuot_of_twin hΩ h.mem h.hK'.1 h.hne.symm h.hz h.hzK' h.hu₁.1
  have t₃₂ : u₃ ∈ Balance.Bootstrap.trivialOnQuot K' :=
    A7T22.le_trivialOnQuot_of_twin hΩ h.hK₃.1 h.hK'.1 h.hK₃K' h.hzK₃ h.hzK' h.hu₃.1
  have zt : ∀ {J : Subgroup G}, IsUniqueInvolution J z →
      z ∈ Balance.Bootstrap.trivialOnQuot J := fun hzJ =>
    ExactLayer.mem_trivialOnQuot_of_le_centralizer fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem hzJ hx).symm
  have e1 : u₁ * u₂ * (u₂ * u₃) = u₁ * z * u₃ := by
    calc u₁ * u₂ * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * u₃ := by rw [h.sq₂]
  have e2 : u₁ * u₂ * z * (u₂ * u₃) = u₁ * u₃ := by
    calc u₁ * u₂ * z * (u₂ * u₃) = u₁ * (u₂ * z) * u₂ * u₃ := by group
      _ = u₁ * (z * u₂) * u₂ * u₃ := by rw [h.comm_z₂]
      _ = u₁ * (z * (u₂ * u₂)) * u₃ := by group
      _ = u₁ * (z * z) * u₃ := by rw [h.sq₂]
      _ = u₁ * u₃ := by rw [h.hz.sq, mul_one]
  rcases h.mem_B_cases hc with e | e | e | e | e | e | e | e
  · exact absurd e hc1
  · exact ⟨K₃, Or.inr (Or.inr rfl), e ▸ (Balance.Bootstrap.trivialOnQuot K₃).mul_mem t₁₃ t₂₃⟩
  · exact absurd e hcz
  · exact ⟨K, Or.inl rfl, e ▸ (Balance.Bootstrap.trivialOnQuot K).mul_mem t₂₁ t₃₁⟩
  · exact ⟨K₃, Or.inr (Or.inr rfl), e ▸ (Balance.Bootstrap.trivialOnQuot K₃).mul_mem
      ((Balance.Bootstrap.trivialOnQuot K₃).mul_mem t₁₃ t₂₃) (zt h.hzK₃)⟩
  · refine ⟨K', Or.inr (Or.inl rfl), ?_⟩
    rw [e, e1]
    exact (Balance.Bootstrap.trivialOnQuot K').mul_mem
      ((Balance.Bootstrap.trivialOnQuot K').mul_mem t₁₂ (zt h.hzK')) t₃₂
  · exact ⟨K, Or.inl rfl, e ▸ (Balance.Bootstrap.trivialOnQuot K).mul_mem (zt h.hz)
      ((Balance.Bootstrap.trivialOnQuot K).mul_mem t₂₁ t₃₁)⟩
  · refine ⟨K', Or.inr (Or.inl rfl), ?_⟩
    rw [e, e2]
    exact (Balance.Bootstrap.trivialOnQuot K').mul_mem t₁₂ t₃₂


theorem hyp51At_vertex_z (d : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) z := by
  have hzB : z ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := T7B.mem_closure_snd
  have hLV : K ∈ twinSet Ω K := mem_twinSet_self d.mem d.hz
  exact A7Q.Vertex.hyp51At_of_triangle d.hz.sq d.hz.ne_one (d.B_le_centralizer_of_mem hzB)
    (d.subn K hLV) (d.subn K' d.hK') (d.subn K₃ d.hK₃)
    (d.comm_le_oddCore_centralizer hLV d.hK' d.hne.symm)
    (d.comm_le_oddCore_centralizer d.hK' d.hK₃ d.hK₃K'.symm)
    (d.comm_le_oddCore_centralizer hLV d.hK₃ d.hK₃K.symm)
    (Subgroup.mul_mem_sup d.hu₁.1 d.hu₂.1) (Subgroup.mul_mem_sup d.hu₂.1 d.hu₃.1)
    (Subgroup.mul_mem_sup d.hu₁.1 d.hu₃.1) T7B.mem_closure_fst T7B.mem_closure_thd
    d.mem_B_13 d.sq_12 d.sq_23 d.sq_13 d.mul_ne_one d.mul_ne_one_ne_z_23.1
    d.mul_ne_one_ne_z_13.1 d.mul_ne_z d.mul_ne_one_ne_z_23.2 d.mul_ne_one_ne_z_13.2

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp51At_of_twinPair (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : PerpHypR r n Y R S t) {B : Subgroup Y} (hB : IsElemAbelian 2 B) {c : Y} (hcB : c ∈ B)
    (htB : t ∈ B) (hc2 : c * c = 1) (hc1 : c ≠ 1) (hct : t ≠ c)
    (htc : t ∈ Subgroup.centralizer ({c} : Set Y)) {J J' : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)) (hne : J' ≠ J)
    (hcJ : c ∈ Balance.Bootstrap.trivialOnQuot J)
    (hcJ' : c ∈ Balance.Bootstrap.trivialOnQuot J') : Hyp51At B c := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hStd : TwinStdR r n Y R S t :=
    ⟨h.core.card, h.core.simple, h.core.nonab, h.core.datum, h.core.quat, h.core.gen,
      h.core.oddFree, h.core.hyp, h.core.aEmpty, h.core.twin⟩
  obtain ⟨S₀, hStd₀⟩ := hStd.core
  have hRc : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by
    rw [hRc]
    exact hJ.1
  have hzJ : IsUniqueInvolution J t := isUniqueInvolution_of_mem_twinSet hU hJ
  obtain ⟨SJ, hStdJ⟩ := exists_datum_atR hStd₀ hRc hJΩ hzJ
  have hRcJ : tightCore J = J := TwinVtx.tightCore_eq_of_mem hRc hJΩ
  have hcm : c ∈ centralizerModOdd ⊤ J :=
    ⟨Subgroup.mem_top _, hcJ.1, Asc77.mem_normalizer_oddCore_of_mem_normalizer hcJ.1,
      fun l hl => hcJ.2 l hl⟩
  have hJ'tw : J' ∈ twinSet (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, TwinVtx.conjClass_eq_of_mem hJ.1, twinSet_eq_of_mem_twinSet hU hJ]
    exact hJ'
  have hq : Quiet c t htc :=
    quiet_of_twin_R h4 hT hStdJ hRcJ h.center_eq_bot hc2 hc1 hcm htc hJ'tw (by rwa [hRcJ]) hcJ'
  exact hyp51At_of_quietR hB htB hcB hc1 hU.ne_one hct htc hq

theorem hyp51B_of_fourth_twin (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : PerpHypR r n Y R S t) {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hK₄ : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h14 : K₄ ≠ K) (h24 : K₄ ≠ K') (h34 : K₄ ≠ K₃) :
    Hyp51 (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hmemT : ∀ {L : Subgroup Y}, L ∈ CoreAssembly.conjClass (tightCore R) →
      IsUniqueInvolution L t →
      L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    fun hL hz => ⟨hL, t, hU, hz⟩
  have hzK₄ : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hU hK₄
  have hΩ := d.hyp
  have hB4 : Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y) ≤
      Balance.Bootstrap.trivialOnQuot K₄ := by
    have t1 : u₁ ∈ Balance.Bootstrap.trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.mem hK₄.1 h14.symm d.hz hzK₄ d.hu₁.1
    have t2 : u₂ ∈ Balance.Bootstrap.trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h24.symm d.hzK' hzK₄ d.hu₂.1
    have t3 : u₃ ∈ Balance.Bootstrap.trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.hK₃.1 hK₄.1 h34.symm d.hzK₃ hzK₄ d.hu₃.1
    have tz : t ∈ Balance.Bootstrap.trivialOnQuot K₄ :=
      ExactLayer.mem_trivialOnQuot_of_le_centralizer fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem hzK₄ hx).symm
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (rfl | rfl | rfl)
    · exact (Balance.Bootstrap.trivialOnQuot K₄).mul_mem t1 t2
    · exact tz
    · exact (Balance.Bootstrap.trivialOnQuot K₄).mul_mem t2 t3
  refine ⟨d.isElemAbelian_B, d.natCard_B, fun c hc hc1 => ?_⟩
  have hzB : t ∈ Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y) := T7B.mem_closure_snd
  by_cases hcz : c = t
  · rw [hcz]
    exact hyp51At_vertex_z d
  · obtain ⟨J, hJ, hcJ⟩ := exists_tq_of_mem_B' d hc hc1 hcz
    have hJT : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
      rcases hJ with rfl | rfl | rfl
      · exact hmemT d.mem d.hz
      · exact hmemT d.hK'.1 d.hzK'
      · exact hmemT d.hK₃.1 d.hzK₃
    have hne : K₄ ≠ J := by
      rcases hJ with rfl | rfl | rfl <;> assumption
    have hc2 : c * c = 1 := by
      rw [← pow_two]
      exact d.isElemAbelian_B.2 c hc
    have htc : t ∈ Subgroup.centralizer ({c} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (d.B_le_centralizer_of_mem hzB hc)).symm
    exact hyp51At_of_twinPair h4 hT h d.isElemAbelian_B hc hzB hc2 hc1 (Ne.symm hcz) htc hJT hK₄ hne
      hcJ (hB4 hc)

end Quiet

end Perp22

end CFSG.CGT.PushingUpLit.SolKNA.R4
