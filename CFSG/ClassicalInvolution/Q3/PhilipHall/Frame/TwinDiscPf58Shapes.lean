module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf57TzCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUMuRest
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUConnE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf19AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf17Trans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Sq
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z02
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentKind
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf6Lift
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieNR
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf12Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Distinct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Sq
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscBaseProved
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.Ih8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Exact
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189a
public import CFSG.ClassicalInvolution.Q3.AE.E29
public import CFSG.ClassicalInvolution.Q3.AE.E64
public import Mathlib.GroupTheory.Perm.List
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ClassicalInvolution.Q3.TL3DichComm
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lay
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelSp62
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelD42
public import CFSG.ClassicalInvolution.Q3.Q3MTModel1
public import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Universal.Catalog
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf15Odd
public import CFSG.ClassicalInvolution.Q3.TL3T25

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

section P10

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.TL4

@[expose] def SqTriOn (X : Type) [Group X] (Φ : Set (Subgroup X)) : Prop :=
  ∀ {A B : Subgroup X} {x₀ : X}, A ∈ Φ → B ∈ omegaNbr Φ A → IsUniqueInvolution A x₀ →
    IsUniqueInvolution B x₀ → ∀ α : MulAut X, α * α * (α * α) = 1 →
      (∀ L ∈ Φ, ∃ L' ∈ Φ, L.map α.toMonoidHom = L') → (∀ a ∈ A, α a = a) →
      (∀ b ∈ B, α b = b) →
        α * α = 1 ∨ α * α = MulAut.conj x₀ ∨
          Subgroup.closure ({q | (α * α) q = q} ∪ {q | x₀ * q = q * x₀}) = ⊤

@[expose] def SqTriShape (shape : ∀ (X : Type) [Group X] [Finite X], Set (Subgroup X) → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), Q8Section X Φ →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) → shape X Φ → SqTriOn X Φ

@[expose] def shapeW (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop :=
  ∃ V : Subgroup X, WSet Φ = {V}

@[expose] def shapeE64 (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop :=
  Nonempty (TC.Thin.AEIdentOn Φ 7 AE.e64Sets AE.e64Sub)

@[expose] def shapeAE (m : ℕ) (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop :=
  Nonempty (TC.Thin.AEIdent Φ m)
variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' : Subgroup Y} {z u : Y} {J : Subgroup Y} {t : Y} {W : Subgroup Y}

theorem zetaTri_of_sqTri (s : Setting n R S t₀ K K' z u J t W)
    (h2' : ∀ J₁ ∈ secFam (CoreAssembly.conjClass (tightCore R)) u, IsPGroup 2 ↥J₁)
    (hTri : SqTriOn (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
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
  obtain ⟨htC₁, htY₁, htbar⟩ := isUniqueInvolution_secImg hΩ hc2 hJtq hf.ht
  obtain ⟨htC₂, htY₂, htbar'⟩ := isUniqueInvolution_secImg hΩ hc2 hJ'tq hJ't
  have hBnbr : secImg (CoreAssembly.conjClass (tightCore R)) u J' ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) u)
        (secImg (CoreAssembly.conjClass (tightCore R)) u J) :=
    omegaNbr_secImg hΩ hc2 hJtq hJ'tq hF.hT hF.hT' hF.le_centralizer_u.1 hF.le_centralizer_u.2
      hF.cTT' hT'J
  have hα4 : secAct hΩ hc2 ⟨x, hxC⟩ * secAct hΩ hc2 ⟨x, hxC⟩ *
      (secAct hΩ hc2 ⟨x, hxC⟩ * secAct hΩ hc2 ⟨x, hxC⟩) = 1 := by
    simp only [← map_mul]
    have : (⟨x, hxC⟩ * ⟨x, hxC⟩ * (⟨x, hxC⟩ * ⟨x, hxC⟩) :
        ↥(Subgroup.centralizer ({u} : Set Y))) = 1 := Subtype.ext hx4
    rw [this, map_one]
  have hfixJ := secAct_fix_secImg hΩ hc2 (h2' _ (secImg_mem_secFam hJtq)) hxC hxJ
  have hfixJ' := secAct_fix_secImg hΩ hc2 (h2' _ (secImg_mem_secFam hJ'tq)) hxC hxJ'
  have hperm : ∀ L ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
      ∃ L' ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
        L.map (secAct hΩ hc2 ⟨x, hxC⟩).toMonoidHom = L' := by
    intro L hL'
    obtain ⟨J₁, hJ₁, rfl⟩ := exists_of_mem_secFam hL'
    exact ⟨_, secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxC hJ₁),
      secAct_map_secImg hΩ hc2 ⟨x, hxC⟩⟩
  have h := hTri (secImg_mem_secFam hJtq) hBnbr htbar htbar' (secAct hΩ hc2 ⟨x, hxC⟩) hα4
    hperm hfixJ hfixJ'
  have hαα : secAct hΩ hc2 ⟨x, hxC⟩ * secAct hΩ hc2 ⟨x, hxC⟩ = secAct hΩ hc2 ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hF.hx2
  rw [hαα] at h
  exact h

end P10

section P13

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.TL4

theorem sqTriShape_ae56 (m : ℕ) (hm : m = 5 ∨ m = 6) : SqTriShape (shapeAE m) := by
  intro X _ _ Φ hS htrans hI A B x₀ hA hB hxA hxB α hα4 hperm hfixA hfixB
  obtain ⟨I⟩ := hI
  have hn5 : 5 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have F := AE5.q8Fam_of_aeIdent_n hn5 hS I
  have hgen := F.gen
  have hk := AE5.psi_sq_dichotomy hm F I (autOfTop hgen α) (autOfTop_perm hgen α hperm)
    hA hB.1 hB.2.1.symm hxA hxB
    (fun y hy => Subtype.ext (hfixA _ hy)) (fun y hy => Subtype.ext (hfixB _ hy))
  rcases hk with h1 | h1
  · left
    ext a
    exact congrArg Subtype.val (h1 ⟨a, mem_pSpan_of_top hgen _⟩)
  · right
    left
    ext a
    exact h1 ⟨a, mem_pSpan_of_top hgen _⟩

end P13

section P11

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.TL4

variable {n : ℕ}

@[expose] def DiscUZetaTriAt (n : ℕ)
    (shape : ∀ (X : Type) [Group X] [Finite X], Set (Subgroup X) → Prop) : Prop :=
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
            (∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
              ∀ N ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
                ∃ g : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
                  classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
                    conjSub g M = N) →
            (∀ J₁ ∈ secFam (CoreAssembly.conjClass (tightCore R)) u, IsPGroup 2 ↥J₁) →
              shape (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
                classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u))
                (secFam (CoreAssembly.conjClass (tightCore R)) u) →
              ∀ (hzC : z ∈ Subgroup.centralizer ({u} : Set Y))
                (htC : t ∈ Subgroup.centralizer ({u} : Set Y))
                (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) ∈
                  coreHull (CoreAssembly.conjClass (tightCore R)) u),
                ZetaTri s.core.hyp
                  (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
                    s.data.frame.hu2) hzC htC htY

theorem discUZetaTriAt_of_sqTriShape
    {shape : ∀ (X : Type) [Group X] [Finite X], Set (Subgroup X) → Prop}
    (h : SqTriShape shape) : DiscUZetaTriAt n shape := by
  intro Y _ _ R S t₀ K K' z u J t W s hw hα hne hconn hY htrans h2' hshape hzC htC htY
  have hf := s.data.frame
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  exact zetaTri_of_sqTri s h2'
    (h _ _ (q8Section_secFam hΩ hc2 h2 hq hA) htrans hshape) hΩ hc2 hzC htC htY

end P11

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
