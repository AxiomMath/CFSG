module

public import CFSG.CGT.PushingUpLit.BHS5.Ambient
public import CFSG.CGT.PushingUpLit.BHS.ThreeSixD
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.OffenderBridge
public import CFSG.CGT.PushingUpLit.BHS5.ThreeFour

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS

variable {Γ : Type} [Group Γ]

structure VHyp (G T M V : Subgroup Γ) : Prop extends AmbHyp G T M where
  elem : IsElemAbelian 2 V
  le_T : V ≤ T
  normalized : G ≤ Subgroup.normalizer (V : Set Γ)
  pCore_le : pCoreOf 2 G ≤ Subgroup.centralizer (V : Set Γ)
  cen_le_M : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ M
  omega_le : omegaOneCenterOf T ≤ V
  J_not_le : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)

theorem AmbHyp.vHyp [Finite Γ] {G T M : Subgroup Γ} (h : AmbHyp G T M) :
    VHyp G T M (omegaOneCenterOf (pCoreOf 2 G)) :=
  { h with
    elem := isElemAbelian_omegaOneCenterOf_pCoreOf
    le_T := h.V_le_T
    normalized := le_normalizer_omegaOneCenterOf_pCoreOf
    pCore_le := pCoreOf_le_centralizer_omegaOneCenterOf
    cen_le_M := h.cenV_le_M
    omega_le := h.omegaOneCenterOf_T_le_V
    J_not_le := h.not_thompsonJ_le_centralizer_V }

section Transfer

variable {G T M V : Subgroup Γ} (hv : VHyp G T M V)

include hv

@[expose] noncomputable def VHyp.rho : ↥G →* MulAut ↥V :=
  (conjAct V).comp (Subgroup.inclusion hv.normalized)

theorem VHyp.autOn_eq_map {X : Subgroup Γ} (hX : X ≤ G) :
    autOn X V = (X.subgroupOf G).map hv.rho := by
  unfold autOn VHyp.rho
  rw [← Subgroup.map_map]
  congr 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨y, hX hy⟩, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

theorem VHyp.mem_ker_rho {g : ↥G} : g ∈ hv.rho.ker ↔ (g : Γ) ∈ Subgroup.centralizer (V : Set Γ) :=
  conjAct_eq_one_iff V (Subgroup.inclusion hv.normalized g)

theorem VHyp.ker_inf_le : hv.rho.ker ⊓ (⊤ : Subgroup ↥G) ≤ M.subgroupOf G := fun g hg =>
  Subgroup.mem_subgroupOf.2 (hv.cen_le_M ⟨g.2, hv.mem_ker_rho.1 hg.1⟩)

theorem VHyp.M_le_G : M ≤ G := hv.minpar.lt_P.le

section FiniteTransfer

variable [Finite Γ]

theorem VHyp.minPar_map :
    MinPar ((⊤ : Subgroup ↥G).map hv.rho) ((T.subgroupOf G).map hv.rho)
      ((M.subgroupOf G).map hv.rho) :=
  MinPar.map_of_ker_le hv.rho hv.minpar.subgroupOf_top hv.ker_inf_le

theorem VHyp.pCore_top_le_ker : pCoreOf 2 (⊤ : Subgroup ↥G) ≤ hv.rho.ker := by
  intro q hq
  rw [hv.mem_ker_rho]
  have hn : (pCoreOf 2 (⊤ : Subgroup ↥G)).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1
      (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥G) (Subgroup.mem_top g)) x).1 hx⟩
  have hN : (pCoreOf 2 (⊤ : Subgroup ↥G)).map G.subtype ≤ pCoreOf 2 G := by
    refine le_pCoreOf 2 (Subgroup.map_subtype_le _) ?_ ((pCoreOf_isPGroup 2 _).map _)
    have h1 : ((pCoreOf 2 (⊤ : Subgroup ↥G)).map G.subtype).subgroupOf G =
        pCoreOf 2 (⊤ : Subgroup ↥G) :=
      Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
    rw [h1]
    exact hn
  exact hv.pCore_le (hN ⟨q, hq, rfl⟩)

theorem VHyp.hyp51 :
    @Hyp51 ↥V (commGroupOfElemAbelian hv.elem) (autOn G V) (autOn T V) (autOn M V) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  have hG : autOn G V = (⊤ : Subgroup ↥G).map hv.rho := by
    rw [hv.autOn_eq_map le_rfl, Subgroup.subgroupOf_self]
  have hT : autOn T V = (T.subgroupOf G).map hv.rho := hv.autOn_eq_map hv.minpar.T_le
  have hM : autOn M V = (M.subgroupOf G).map hv.rho := hv.autOn_eq_map hv.M_le_G
  have hmin := hv.minPar_map
  rw [← hG, ← hT, ← hM] at hmin
  refine ⟨hmin, ?_, ?_, ?_⟩
  · have := pCoreOf_map_eq_bot_of_ker_le hv.rho hv.minpar.subgroupOf_top hv.ker_inf_le
      hv.pCore_top_le_ker
    rwa [← hG] at this
  · obtain ⟨A, hA, hne⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set Γ) := by
      by_contra hcon
      push Not at hcon
      exact hv.J_not_le (iSup₂_le fun A hA => hcon A hA)
    have hTN : T ≤ Subgroup.normalizer (V : Set Γ) := hv.minpar.T_le.trans hv.normalized
    have hAN : A ≤ Subgroup.normalizer (V : Set Γ) := hA.1.trans hTN
    have hoffG : IsOffG V A := isOffG_of_isMaxElemAbelian hv.elem hv.le_T hTN hA hne
    exact ⟨autOn A V, autOn_le_autOn V (hA.1.trans hv.minpar.T_le),
      (isOffG_iff_isOff_autOn hv.elem hAN).1 hoffG⟩
  · intro x hx
    obtain ⟨hxG, hxfix⟩ := hx
    obtain ⟨a, haG, rfl⟩ := mem_autOn_iff.1 hxG
    have hMa : (a : Γ) ∈ M := by
      apply hv.toAmbHyp.cStarStar_le_M
      refine le_sup_left (a := G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ))
        ⟨haG, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
      have hzV : z ∈ V := hv.omega_le hz
      have hzC : z ∈ centerOf T := (Subgroup.closure_le _).2 (fun w hw => hw.1) hz
      have hu : (⟨z, hzV⟩ : ↥V) ∈ fixV (autOn T V) := by
        intro y hy
        obtain ⟨t, htT, rfl⟩ := mem_autOn_iff.1 hy
        apply Subtype.ext
        rw [conjAct_apply']
        have := Subgroup.mem_centralizer_iff.1 hzC.2 (t : Γ) htT
        calc (t : Γ) * z * (t : Γ)⁻¹ = z * (t : Γ) * (t : Γ)⁻¹ := by rw [this]
          _ = z := by group
      have h1 := congrArg (fun w : ↥V => (w : Γ)) (hxfix _ hu)
      simp only [conjAct_apply'] at h1
      calc z * (a : Γ) = (a * z * (a : Γ)⁻¹) * a := by rw [h1]
        _ = a * z := by group
    exact hM ▸ (mem_autOn_iff.2 ⟨a, hMa, rfl⟩)

end FiniteTransfer

end Transfer

end CFSG.CGT.PushingUpLit.BHS5
