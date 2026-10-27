module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8TwoTriple
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8TwoOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf15Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinCore
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CaseC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL

section Conn


theorem secFam_dstarConn_of_triple {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {c : G} {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hMF : TwinDisc.DStarConnectedTwinQ8Below n)
    (hlt : Nat.card (↥(TwinDisc.coreHull Ω c) ⧸
      classicalInvolutionOddCore ↥(TwinDisc.coreHull Ω c)) < n)
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (hA : ∀ M ∈ TwinDisc.secFam Ω c, AEmpty (TwinDisc.secFam Ω c) M)
    (htt : TwinTriple (TwinDisc.secFam Ω c)) {B : Subgroup G} (hB : B ∈ tqMembers3 Ω c) :
    ∀ M ∈ TwinDisc.secFam Ω c, M ∈ dstarComp (TwinDisc.secFam Ω c) (TwinDisc.secImg Ω c B) := by
  rcases TwinDisc.dichotomy_of_thm4RTwin h4 hlt (TwinDisc.hypOmegaGen_secFam hΩ hc2)
      (TwinDisc.secFam_twoGroup h2) (TwinDisc.secFam_q8 hc2 hq) hA TwinDisc.oddCore_quot_eq_bot
      (TwinDisc.secImg_mem_secFam hB) with hconn | horb
  · exact hconn
  · have htrans : ∀ K₁ ∈ TwinDisc.secFam Ω c, ∀ L ∈ TwinDisc.secFam Ω c,
        ∃ g : ↥(TwinDisc.coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreHull Ω c),
          conjSub g K₁ = L := by
      intro K₁ hK₁ L hL
      obtain ⟨y₁, hy₁⟩ := horb K₁ hK₁
      obtain ⟨y₂, hy₂⟩ := horb L hL
      exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
    have hgen : omegaGen (TwinDisc.secFam Ω c) = ⊤ :=
      omegaGen_quotFamily_eq_top _ _
        (omegaGen_restrictFamily_eq_top (TwinDisc.cFam Ω c) (TwinDisc.coreHull Ω c) rfl)
    have hD := hMF _ hlt (TwinDisc.secFam Ω c) (TwinDisc.hypOmegaGen_secFam hΩ hc2)
      (TwinDisc.secFam_twoGroup h2) (TwinDisc.secFam_q8 hc2 hq) TwinDisc.oddCore_quot_eq_bot hA
      hgen htrans htt
    intro M' hM'
    exact hD _ (TwinDisc.secImg_mem_secFam hB) M' hM'

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem prod_not_mem_center [CaseIAmbient T] (cfg : L3E8Cfg K z J zJ H Q E S) {h : T}
    (hne : h⁻¹ * z * h ≠ z) : z * (h⁻¹ * z * h) ∉ Subgroup.center T :=
  CaseIAmbient.not_mem_center (cfg.prod_ne_one hne)

theorem cent_le_prod [CaseIAmbient T] (cfg : L3E8Cfg K z J zJ H Q E S)
    (hU : UniqueCosetZ K z) (h4 : Thm4RTwinBelow 3 (Nat.card T))
    (hMF : TwinDisc.DStarConnectedTwinQ8Below (Nat.card T)) {h : T}
    (hne : h⁻¹ * z * h ≠ z) (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z)
    (hnot : h⁻¹ * z * h ∉ firstFactor K) :
    Subgroup.centralizer ({z * (h⁻¹ * z * h)} : Set T) ≤ sigmaNorm K := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hΩc : ConjInvariant (CoreAssembly.conjClass K) := hΩ.conjInvariant
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have h2 := cfg.toFrameStd.typeRHyp.twoGroup
  have hq := cfg.toFrameStd.typeRHyp.sylow
  have ha2 := cfg.prod_isPGroup hne hc
  rcases cfg.aEmpty_cFam_or_cent_le hU ha2 (cfg.prod_ne_one hne) (z_mem_centralizer_prod hc) with
    hA | hle
  swap
  · exact hle
  have hAs := secFam_aEmpty_of_cFam hΩ ha2 hA
  obtain ⟨R, hR, hRc, htt⟩ := cfg.exists_twinTriple_prod hne hc hnot
  have hKtq : K ∈ tqMembers3 (CoreAssembly.conjClass K) (z * (h⁻¹ * z * h)) :=
    ⟨hKΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hKΩ ⟨R, hR, hRc⟩⟩
  have hlt := TwinDisc.card_secQuot_lt (Ω := CoreAssembly.conjClass K)
    (cfg.prod_not_mem_center hne)
  have hconn := secFam_dstarConn_of_triple h4 hMF hlt hΩ ha2 h2 hq hAs htt hKtq
  have hH : oddCoreOf (Subgroup.centralizer ({z * (h⁻¹ * z * h)} : Set T)) ≤
      sigmaStarNorm (CoreAssembly.conjClass K) K :=
    (cfg.oddCore_cent_prod_le hc hnot).trans cfg.sigmaNorm_le_sigmaStarNorm
  intro c hc'
  have hcK := conjSub_mem_tqMembers3 hΩc hc' hKtq
  have hp := TwinDisc.secPath_of_connected hΩ ha2 hKtq le_rfl hconn _ hcK
  have hmem := TwinDisc.mem_dstarComp_of_secPath hΩc hKΩ hH hp Relation.ReflTransGen.refl
  exact sigmaStarNorm_le_sigmaNorm K (T7A.mem_sigmaStarNorm_of_conj hΩc hKΩ hmem)

end L3E8Cfg

end Conn

section Package


theorem thm4RTwinBelow_of_pkg {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) :
    Thm4RTwinBelow 3 n :=
  thm4RTwin_of_twoClass (fun _ hA hP' => TL4.exitTwoClassR_of hA hP') n hcit hP

theorem dstarConnectedTwinQ8Below_of_pkg {n : ℕ} (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) : TwinDisc.DStarConnectedTwinQ8Below n :=
  TwinDisc.dstarConnectedTwinQ8Below_of_exit hcit hP
    (TwinDisc.dstarExitQ8_proved TwinDisc.ExitE4.e4ModelDStar_of_certs hcit hP)

theorem L3E8Cfg.cent_le_of_pkg {T : Type} [Group T] [Finite T] [CaseIAmbient T]
    {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T} {H Q E S : Subgroup T}
    (cfg : L3E8Cfg K z J zJ H Q E S) (hU : UniqueCosetZ K z) (hcit : CIT3Below (Nat.card T))
    (hP : TL4.TightBelowRPlus 3 (Nat.card T)) : L3E8CentLe K z := by
  rintro _ ⟨h, hne, hc, hnot, rfl⟩
  exact cfg.cent_le_prod hU (thm4RTwinBelow_of_pkg hcit hP)
    (dstarConnectedTwinQ8Below_of_pkg hcit hP) hne hc hnot

end Package

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
