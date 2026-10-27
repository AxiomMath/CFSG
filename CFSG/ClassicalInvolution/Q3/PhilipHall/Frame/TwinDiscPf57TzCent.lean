module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf51TzStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf55SigmaLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf56Tri

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc


section P8

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' : Subgroup Y} {z u : Y} {J : Subgroup Y} {t : Y} {W : Subgroup Y}

theorem tzCent_of_zetaTri (I : TwinDiscBase n) (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hY : ¬ rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K)
    (hJtq : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) u)
    (htrans : ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
      ∀ N ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
        ∃ g : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
          classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
            conjSub g M = N)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    (hzC : z ∈ Subgroup.centralizer ({u} : Set Y)) (htC : t ∈ Subgroup.centralizer ({u} : Set Y))
    (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) ∈
      coreHull (CoreAssembly.conjClass (tightCore R)) u)
    (hζ : ZetaTri hΩ hc2 hzC htC htY) :
    ∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
      (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈
        oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u) := by
  have hf := s.data.frame
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hrY := rLayer_le_coreLayer hΩ h2 hc2
  have hs := alphaStepsBase I s
  rcases hζ with h1 | h1 | h1
  · exfalso
    apply hY
    have hzt := comm_mem_oddCoreOf_of_secAct_eq_one hΩ hc2 hzC h1
    exact hrY.trans (coreLayer_le_sigmaGen_of_le_centralizer_z hΩ hc2 hf.mem hf.hz
      (coreLayer_le_centralizer_of_trivial hs hf hc2 hα (Or.inl rfl) hzt))
  · have htz : secAct hΩ hc2 ⟨t, htC⟩ = secAct hΩ hc2 ⟨z, hzC⟩ := by
      rw [secAct_of_mem hΩ hc2 htY, h1]
    have htzC : t * z ∈ Subgroup.centralizer ({u} : Set Y) := Subgroup.mul_mem _ htC hzC
    refine comm_mem_oddCoreOf_of_secAct_eq_one hΩ hc2 htzC ?_
    have e : (⟨t * z, htzC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨t, htC⟩ * ⟨z, hzC⟩ := rfl
    rw [e, map_mul, ← htz, ← map_mul]
    have : (⟨t, htC⟩ * ⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = 1 :=
      Subtype.ext hf.ht.sq
    rw [this, map_one]
  · exfalso
    apply hY
    refine hrY.trans (coreLayer_le_sigmaGen_of_transitive_gen hΩ hc2 hf.mem hf.hz
      (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)) hf.ht
      (fun m hm => mem_centralizer_z_of_oddCore_centralizer_u s hα hm) hzC htC htY rfl hJtq ?_)
    intro N hN
    obtain ⟨g, hg⟩ := htrans _ (secImg_mem_secFam hJtq) N hN
    exact ⟨g, by rw [h1]; trivial, hg⟩

end P8


section P9

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.TL4

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' : Subgroup Y} {z u : Y} {J : Subgroup Y} {t : Y} {W : Subgroup Y}

theorem zetaTri_of_noExit (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (s : Setting n R S t₀ K K' z u J t W)
    (hnd : ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore R)) u))
    (hno : NoExit (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u))
      (secFam (CoreAssembly.conjClass (tightCore R)) u))
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    (hzC : z ∈ Subgroup.centralizer ({u} : Set Y)) (htC : t ∈ Subgroup.centralizer ({u} : Set Y))
    (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) ∈
      coreHull (CoreAssembly.conjClass (tightCore R)) u) :
    ZetaTri hΩ hc2 hzC htC htY := by
  have hf := s.data.frame
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have htr : ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ N ∈ CoreAssembly.conjClass (tightCore R),
      ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₁', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) := hf.hJ.1
  have hJ'Ω : J' ∈ CoreAssembly.conjClass (tightCore R) := hJ'tw.1
  have hJtq : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) u :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩
  have hJ'tq : J' ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) u :=
    ⟨hJ'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ'Ω ⟨T', hF.hT', hF.le_centralizer_u.2⟩⟩
  have hlt : Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hF.hxy]
    have hc : x * y = y * x := hF.cRR' x hF.hx y hF.hy
    calc x * (x * y) = x * (y * x) := by rw [hc]
      _ = (x * y) * x := by group
  have hx4 : x * x * (x * x) = 1 := by rw [hF.hx2, hf.hz.sq]
  have hxJ : x ∈ trivialOnQuot J :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hF.cRT x hF.hx s hs).symm⟩
  have hxJ' : x ∈ trivialOnQuot J' :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ'Ω ⟨T', hF.hT', fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hF.cRT' x hF.hx s hs).symm⟩
  have h8 : 8 ≤ Nat.card T' :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'Ω hF.hT')
  have hT't : T' ≤ Subgroup.centralizer ({t} : Set Y) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hJ't.commute_of_mem (hF.hT'.1 hs)).symm
  have hT'J : T' ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hJ'Ω hJ'ne.symm hf.ht hF.hT'.1 hF.hT'.2.1
      (by omega) hT't
  have hih : IH8T 3 1 n := InductionBridge.ih8T_of_cit3Below hcit
  obtain ⟨htC', htY', h⟩ := secAct_sq_trichotomy_noExit hcit hih hP hΩ hc2 h2 hq hA hlt hno hnd
    hJtq hJ'tq hf.ht hJ't hF.hT hF.hT' hF.le_centralizer_u.1 hF.le_centralizer_u.2 hF.cTT' hT'J
    hxC hxJ hxJ' hx4
  have hαα : secAct hΩ hc2 ⟨x, hxC⟩ * secAct hΩ hc2 ⟨x, hxC⟩ = secAct hΩ hc2 ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hF.hx2
  rw [hαα] at h
  exact h

@[expose] def DiscUZetaTriO2 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y)
    (s : Setting n R S t₀ K K' z u J t W),
    TwinMu.ThompsonWitness (CoreAssembly.conjClass (tightCore R)) K K' z u J →
    alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
      dComp (CoreAssembly.conjClass (tightCore R)) K ≠
          dstarComp (CoreAssembly.conjClass (tightCore R)) K →
        SecConnU (CoreAssembly.conjClass (tightCore R)) u →
          ¬ rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
              sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
            (∃ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
              ∃ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
                  classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
                IsUniqueInvolution M zb ∧ TightInO2 zb) →
              ∀ (hzC : z ∈ Subgroup.centralizer ({u} : Set Y))
                (htC : t ∈ Subgroup.centralizer ({u} : Set Y))
                (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) ∈
                  coreHull (CoreAssembly.conjClass (tightCore R)) u),
                ZetaTri s.core.hyp
                  (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
                    s.data.frame.hu2) hzC htC htY

@[expose] def DiscUZetaTriE4 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y)
    (s : Setting n R S t₀ K K' z u J t W),
    TwinMu.ThompsonWitness (CoreAssembly.conjClass (tightCore R)) K K' z u J →
    alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
      dComp (CoreAssembly.conjClass (tightCore R)) K ≠
          dstarComp (CoreAssembly.conjClass (tightCore R)) K →
        SecConnU (CoreAssembly.conjClass (tightCore R)) u →
          ¬ rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
              sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
            (¬ ∃ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
              ∃ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
                  classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
                IsUniqueInvolution M zb ∧ TightInO2 zb) →
              TwinE4 (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
                classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u)) →
              ∀ (hzC : z ∈ Subgroup.centralizer ({u} : Set Y))
                (htC : t ∈ Subgroup.centralizer ({u} : Set Y))
                (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) ∈
                  coreHull (CoreAssembly.conjClass (tightCore R)) u),
                ZetaTri s.core.hyp
                  (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
                    s.data.frame.hu2) hzC htC htY

theorem discUTzCentT_of_branches (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hO2 : DiscUZetaTriO2 n) (hE4 : DiscUZetaTriE4 n) :
    DiscUTzCentT n := by
  intro Y _ _ R S t₀ K K' z u J t W s hw hα hne hconn hY
  have I : TwinDiscBase n := twinDiscBase_of_thm4 h4
  have hf := s.data.frame
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have htr : ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ N ∈ CoreAssembly.conjClass (tightCore R),
      ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₁', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) := hf.hJ.1
  have hJtq : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) u :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩
  have hlt : Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  have htrans := TwinMu.Pf3.transY_of_witness h4 s hne hw
  have hodd : ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
      ∀ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
        IsUniqueInvolution M zb → oddCoreImg (Subgroup.centralizer ({zb} : Set _)) = ⊥ :=
    fun M hM zb hzb => oddCentEdge_proved n hcit hP _ hlt _ hS htrans (section_edge s) M hM zb hzb
  have hnd := not_dConnected_secFam_of_not_le_sigmaGen s hα hY
  have hzC : z ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (u_comm_z hΩ hf).symm
  obtain ⟨htC, htY, -⟩ := isUniqueInvolution_secImg hΩ hc2 hJtq hf.ht
  refine tzCent_of_zetaTri I s hα hY hJtq htrans hΩ hc2 hzC htC htY ?_
  rcases ExitU.noExit_or_o2_or_e4 hS htrans (section_edge s) hodd with hno | ho | hE
  · exact zetaTri_of_noExit hcit hP s hnd hno hΩ hc2 hzC htC htY
  · exact hO2 Y R S t₀ K K' z u J t W s hw hα hne hconn hY ho hzC htC htY
  · by_cases hO : ∃ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
        ∃ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
          classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
          IsUniqueInvolution M zb ∧ TightInO2 zb
    · exact hO2 Y R S t₀ K K' z u J t W s hw hα hne hconn hY hO hzC htC htY
    · exact hE4 Y R S t₀ K K' z u J t W s hw hα hne hconn hY hO hE hzC htC htY

end P9

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
