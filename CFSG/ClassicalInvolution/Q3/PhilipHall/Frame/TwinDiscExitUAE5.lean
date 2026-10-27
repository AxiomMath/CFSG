module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUDisc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf19AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Gen

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



section Aut

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem mem_pSpan_of_top (hgen : TC.Thin.pSpan Φ = ⊤) (x : X) : x ∈ TC.Thin.pSpan Φ := by
  have : x ∈ (⊤ : Subgroup X) := Subgroup.mem_top x
  rwa [← hgen] at this

@[expose] noncomputable def autOfTop (hgen : TC.Thin.pSpan Φ = ⊤) (α : MulAut X) :
    MulAut ↥(TC.Thin.pSpan Φ) where
  toFun y := ⟨α y, mem_pSpan_of_top hgen _⟩
  invFun y := ⟨α.symm y, mem_pSpan_of_top hgen _⟩
  left_inv y := Subtype.ext (α.symm_apply_apply y)
  right_inv y := Subtype.ext (α.apply_symm_apply y)
  map_mul' a b := Subtype.ext (map_mul α (a : X) (b : X))

theorem autOfTop_coe (hgen : TC.Thin.pSpan Φ = ⊤) (α : MulAut X) (y : ↥(TC.Thin.pSpan Φ)) :
    ((autOfTop hgen α y : ↥(TC.Thin.pSpan Φ)) : X) = α (y : X) := rfl

theorem autOfTop_perm (hgen : TC.Thin.pSpan Φ = ⊤) (α : MulAut X)
    (hperm : ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map α.toMonoidHom = L') :
    ∀ M ∈ Φ, ∃ M' ∈ Φ, (M.subgroupOf (TC.Thin.pSpan Φ)).map (autOfTop hgen α).toMonoidHom =
      M'.subgroupOf (TC.Thin.pSpan Φ) := by
  intro M hM
  obtain ⟨M', hM', hMM'⟩ := hperm M hM
  refine ⟨M', hM', ?_⟩
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_subgroupOf, ← hMM']
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf, ← hMM'] at hy
    obtain ⟨l, hl, hly⟩ := hy
    refine ⟨⟨l, mem_pSpan_of_top hgen _⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    exact Subtype.ext hly

end Aut

section Main

variable {n : ℕ}

theorem discUAE5_of_cert (h4 : Thm4RTwinBelow 3 n) : DiscUAE5 n := by
  intro Y _ _ R S t₀ K K' z u J t W s hdisc hI
  obtain ⟨I⟩ := hI
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
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  have htrans : ∀ M ∈ secFam Ω u, ∀ N ∈ secFam Ω u, ∃ g, conjSub g M = N := by
    rcases dichotomy_secFam h4 hlt hΩ hc2 h2 hq hA hJtq with hd | hd
    · exact absurd (fun M hM N hN =>
        (reflTransGen_dstarAdj_symm (secImg_mem_secFam hJtq) (hd M hM)).trans (hd N hN)) hdisc
    · intro M hM N hN
      obtain ⟨a, ha⟩ := hd M hM
      obtain ⟨b, hb⟩ := hd N hN
      refine ⟨b * a⁻¹, ?_⟩
      rw [← hb, ← ha, ← conjSub_mul]
      congr 1
      group
  have F := AE5.q8Fam_of_aeIdent hS htrans I
  have h2' := F.two
  have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hF.hxy]
    have hc : x * y = y * x := hF.cRR' x hF.hx y hF.hy
    calc x * (x * y) = x * (y * x) := by rw [hc]
      _ = (x * y) * x := by group
  have hzC : z ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (u_comm_z hΩ hf).symm
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
  obtain ⟨htC', htY, htbar⟩ := isUniqueInvolution_secImg hΩ hc2 hJtq hf.ht
  obtain ⟨htC'', htY', htbar'⟩ := isUniqueInvolution_secImg hΩ hc2 hJ'tq hJ't
  set tb : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u) :=
    QuotientGroup.mk (⟨⟨t, htC'⟩, htY⟩ : ↥(coreHull Ω u)) with htbdef
  have hnbr := omegaNbr_secImg hΩ hc2 hJtq hJ'tq hF.hT hF.hT' hF.le_centralizer_u.1
    hF.le_centralizer_u.2 hF.cTT' hT'J
  have hperm : ∀ L ∈ secFam Ω u, ∃ L' ∈ secFam Ω u,
      L.map (secAct hΩ hc2 ⟨x, hxC⟩).toMonoidHom = L' := by
    intro L hL'
    obtain ⟨J₁, hJ₁, rfl⟩ := exists_of_mem_secFam hL'
    exact ⟨_, secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxC hJ₁),
      secAct_map_secImg hΩ hc2 ⟨x, hxC⟩⟩
  have hfx := secAct_fix_secImg hΩ hc2 (h2' _ (secImg_mem_secFam hJtq)) hxC hxJ
  have hfx' := secAct_fix_secImg hΩ hc2 (h2' _ (secImg_mem_secFam hJ'tq)) hxC hxJ'
  have hgen := F.gen
  have hkey := AE5.psi_dichotomy F I (autOfTop hgen (secAct hΩ hc2 ⟨x, hxC⟩))
    (autOfTop_perm hgen _ hperm) (secImg_mem_secFam hJtq) (secImg_mem_secFam hJ'tq) hnbr.2.1.symm
    htbar htbar'
    (fun y hy => Subtype.ext (hfx _ hy)) (fun y hy => Subtype.ext (hfx' _ hy))
  have hα2 : secAct hΩ hc2 ⟨x, hxC⟩ * secAct hΩ hc2 ⟨x, hxC⟩ = 1 := by
    rcases hkey with h1 | h1
    · ext a
      have := congrArg Subtype.val (h1 ⟨a, mem_pSpan_of_top hgen _⟩)
      show (secAct hΩ hc2 ⟨x, hxC⟩) ((secAct hΩ hc2 ⟨x, hxC⟩) a) = a
      have e : (secAct hΩ hc2 ⟨x, hxC⟩) a = a := this
      rw [e, e]
    · ext a
      have e : ∀ b, (secAct hΩ hc2 ⟨x, hxC⟩) b = tb * b * tb⁻¹ := fun b =>
        h1 ⟨b, mem_pSpan_of_top hgen _⟩
      show (secAct hΩ hc2 ⟨x, hxC⟩) ((secAct hΩ hc2 ⟨x, hxC⟩) a) = a
      rw [e, e]
      have hsq := htbar.sq
      calc tb * (tb * a * tb⁻¹) * tb⁻¹ = (tb * tb) * a * (tb * tb)⁻¹ := by group
        _ = a := by rw [hsq]; group
  have hαα : secAct hΩ hc2 ⟨x, hxC⟩ * secAct hΩ hc2 ⟨x, hxC⟩ = secAct hΩ hc2 ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hF.hx2
  exact Or.inl (comm_mem_oddCoreOf_of_secAct_eq_one hΩ hc2 hzC (hαα ▸ hα2))

end Main

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
