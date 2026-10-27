module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Sq

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

theorem reflTransGen_dstarAdj_symm {G : Type} [Group G] {Ω : Set (Subgroup G)} {A B : Subgroup G}
    (hA : A ∈ Ω) (h : Relation.ReflTransGen (dstarAdj Ω) A B) :
    Relation.ReflTransGen (dstarAdj Ω) B A := by
  have key : B ∈ Ω ∧ Relation.ReflTransGen (dstarAdj Ω) B A := by
    induction h with
    | refl => exact ⟨hA, Relation.ReflTransGen.refl⟩
    | tail _ hstep ih =>
      exact ⟨hstep.1, Relation.ReflTransGen.head ⟨ih.1, hstep.2.symm⟩ ih.2⟩
  exact key.2

@[expose] def DiscUNoExitAE5 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      ¬ SecConnU (CoreAssembly.conjClass (tightCore R)) u →
        NoExit (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
          classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u))
          (secFam (CoreAssembly.conjClass (tightCore R)) u) ∨
        ((∃ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
          ∃ zb : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
              classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
            IsUniqueInvolution M zb ∧ TightInO2 zb) ∧
          Nonempty (TC.Thin.AEIdent (secFam (CoreAssembly.conjClass (tightCore R)) u) 5))

@[expose] def DiscUAE5 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      ¬ SecConnU (CoreAssembly.conjClass (tightCore R)) u →
        Nonempty (TC.Thin.AEIdent (secFam (CoreAssembly.conjClass (tightCore R)) u) 5) →
        (∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
            z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u)) ∨
          (∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
            (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈
              oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u))

theorem discZT_of_cases {n : ℕ} (hcit : CIT3Below n) (hih : IH8T 3 1 n)
    (hP : TL4.TightBelowRPlus 3 n) (hN : DiscUNoExitAE5 n) (hAE : DiscUAE5 n) : DiscZT n := by
  intro Y _ _ R S t₀ K K' z u J t W s hdisc
  rcases hN Y R S t₀ K K' z u J t W s hdisc with hno | ⟨-, hae⟩
  swap
  · exact hAE Y R S t₀ K K' z u J t W s hdisc hae
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₁', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hJ'Ω : J' ∈ Ω := hJ'tw.1
  have hJtq : J ∈ tqMembers3 Ω u :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩
  have hJ'tq : J' ∈ tqMembers3 Ω u :=
    ⟨hJ'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ'Ω ⟨T', hF.hT', hF.le_centralizer_u.2⟩⟩
  have hlt : Nat.card (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hF.hxy]
    have hc : x * y = y * x := hF.cRR' x hF.hx y hF.hy
    calc x * (x * y) = x * (y * x) := by rw [hc]
      _ = (x * y) * x := by group
  have hzC : z ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (u_comm_z hΩ hf).symm
  have htC : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hf.htu
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
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hJ'Ω hJ'ne.symm hf.ht hF.hT'.1 hF.hT'.2.1 (by omega) hT't
  obtain ⟨htC', htY, hkey⟩ := secAct_sq_dichotomy hcit hih hP hΩ hc2 h2 hq hA hlt hdisc hno hJtq hJ'tq
    hf.ht hJ't hF.hT hF.hT' hF.le_centralizer_u.1 hF.le_centralizer_u.2 hF.cTT' hT'J hxC hxJ hxJ' hx4
  have hαα : secAct hΩ hc2 ⟨x, hxC⟩ * secAct hΩ hc2 ⟨x, hxC⟩ = secAct hΩ hc2 ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hF.hx2
  rcases hkey with h1 | h1
  · left
    exact comm_mem_oddCoreOf_of_secAct_eq_one hΩ hc2 hzC (hαα ▸ h1)
  · right
    have htz : secAct hΩ hc2 ⟨t, htC⟩ = secAct hΩ hc2 ⟨z, hzC⟩ := by
      rw [secAct_of_mem hΩ hc2 htY, ← hαα, h1]
    have htzC : t * z ∈ Subgroup.centralizer ({u} : Set Y) := Subgroup.mul_mem _ htC hzC
    refine comm_mem_oddCoreOf_of_secAct_eq_one hΩ hc2 htzC ?_
    have e : (⟨t * z, htzC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨t, htC⟩ * ⟨z, hzC⟩ := rfl
    rw [e, map_mul, ← htz, ← map_mul]
    have : (⟨t, htC⟩ * ⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = 1 :=
      Subtype.ext hf.ht.sq
    rw [this, map_one]

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
