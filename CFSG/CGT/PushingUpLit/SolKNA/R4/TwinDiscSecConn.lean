module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscClaims
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscModel
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscSecHyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Tz

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
open scoped commutatorElement


section Named

variable {r n : ℕ}

@[expose] def DiscSecConnTzR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
          ∀ N ∈ SylCent (CoreAssembly.conjClass (tightCore R)) (t * z),
            SecPath (CoreAssembly.conjClass (tightCore R))
              (oddCoreOf (Subgroup.centralizer ({t * z} : Set Y))) M N

theorem discTqTz_of_connR (B : TwinDiscBaseR r n) (h : DiscSecConnTzR r n) : DiscTqTzR r n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα M hM
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hs := alphaStepsR B s
  have hα' : alphaOf (Subgroup.closure ({z, t} : Set Y)) = ⊥ := by
    rw [hs.alpha_zt hf]; exact hα
  have hzA : z ∈ Subgroup.closure ({z, t} : Set Y) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({z, t} : Set Y) := Subgroup.subset_closure (by simp)
  have htz1 : t * z ≠ 1 := by
    intro e
    apply hf.t_ne_z
    have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [h2]; exact inv_eq_of_mul_eq_one_right hf.hz.sq
  have hH : oddCoreOf (Subgroup.centralizer ({t * z} : Set Y)) ≤ sigmaStarNorm Ω K := by
    intro n' hn'
    have hcomm : n' * z = z * n' :=
      oddCore_comm_of_alpha hα' (Subgroup.mul_mem _ htA hzA) htz1 hzA hn'
    exact centralizer_le_sigmaStarNorm_z hΩ hf.mem hf.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have hKS := mem_sylCent_tz_K' hΩ hf
  exact mem_dstarComp_of_secPath hΩ.conjInvariant hf.mem hH
    (h Y R S t₀ K K' z u J t W s hα K hKS M hM) Relation.ReflTransGen.refl

theorem discSecConnTzR_of (hT4 : Thm4RTwinBelow r n) (hMF : DStarConnectedTwinR r n) :
    DiscSecConnTzR r n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα M hM N hN
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_membersR s
  have hK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, hRR', hRT, hR'T⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hf.mem hf.hz hf.hK' hf.hne hf.hJ
  have h8R : 8 ≤ Nat.card R₀ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.mem hR₀)
  have h8T : 8 ≤ Nat.card T₀ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.hJ.1 hT₀)
  have hzR : z ∈ R₀ := mem_of_isUniqueInvolution_of_isPGroup hf.hz hR₀.1 hR₀.2.1 (by omega)
  have htT : t ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup hf.ht hT₀.1 hT₀.2.1 (by omega)
  have hzt : z * t = t * z := hRT z hzR t htT
  have hcsq : (t * z) * (t * z) = 1 := by
    calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [hzt]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [hf.ht.sq, hf.hz.sq, one_mul]
  have hc2 : IsPGroup 2 (Subgroup.zpowers (t * z)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcsq
  have hcomm : ∀ x : Y, x * t = t * x → x * z = z * x → x * (t * z) = (t * z) * x := by
    intro x hxt hxz
    calc x * (t * z) = (x * t) * z := by group
      _ = (t * x) * z := by rw [hxt]
      _ = t * (x * z) := by group
      _ = t * (z * x) := by rw [hxz]
      _ = (t * z) * x := by group
  have hRc : R₀ ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hRT x hx t htT) (hf.hz.commute_of_mem (hR₀.1 hx)).symm
      exact this)
  have hR'c : R₀' ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hR'T x hx t htT) (hK'.commute_of_mem (hR₀'.1 hx)).symm
      exact this)
  have hTc : T₀ ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hf.ht.commute_of_mem (hT₀.1 hx)).symm (hRT z hzR x hx).symm
      exact this)
  have hKtq : K ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.mem, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.mem ⟨R₀, hR₀, hRc⟩⟩
  have hK'tq : K' ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.hK'.1 ⟨R₀', hR₀', hR'c⟩⟩
  have hJtq : J ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.hJ.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.hJ.1 ⟨T₀, hT₀, hTc⟩⟩
  have hJK : J ≠ K := (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)).2.1
  have hJK' : J ≠ K' := (hf.hJ.2 K' hf.hK').2.1
  have hTz : T₀ ≤ Subgroup.centralizer ({z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hTK : T₀ ≤ Subgroup.normalizer (K : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hf.mem hf.hJ.1 hJK.symm hf.hz hT₀.1 hT₀.2.1
      (by omega) hTz
  have hTK' : T₀ ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hf.hK'.1 hf.hJ.1 hJK'.symm hK' hT₀.1 hT₀.2.1
      (by omega) hTz
  have htt : TwinTriple (TwinDisc.secFam Ω (t * z)) :=
    twinTriple_secFam hΩ hc2 hKtq hK'tq hJtq hf.hz hf.hK' hR₀ hR₀' hT₀ hRc hR'c hTc hRR' hRT hR'T
      hTK hTK'
  have hMtq : M ∈ tqMembers3 Ω (t * z) := ⟨hM.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hM.1 hM.2⟩
  have hNtq : N ∈ tqMembers3 Ω (t * z) := ⟨hN.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hN.1 hN.2⟩
  have htz1 : t * z ≠ 1 := by
    intro e
    apply hf.t_ne_z
    have h2' : t = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [h2']; exact inv_eq_of_mul_eq_one_right hf.hz.sq
  have hlt : Nat.card (↥(coreHull Ω (t * z)) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω (t * z))) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_oneR s htz1)
  have hconn : ∀ M' ∈ TwinDisc.secFam Ω (t * z),
      M' ∈ dstarComp (TwinDisc.secFam Ω (t * z)) (secImg Ω (t * z) M) := by
    rcases dichotomy_secFamR hT4 hlt hΩ hc2 h2 hq hA hMtq with hconn | horb
    · exact hconn
    · have htrans : ∀ K₁ ∈ TwinDisc.secFam Ω (t * z), ∀ L ∈ TwinDisc.secFam Ω (t * z),
          ∃ g : ↥(coreHull Ω (t * z)) ⧸ classicalInvolutionOddCore ↥(coreHull Ω (t * z)),
            conjSub g K₁ = L := by
        intro K₁ hK₁ L hL
        obtain ⟨y₁, hy₁⟩ := horb K₁ hK₁
        obtain ⟨y₂, hy₂⟩ := horb L hL
        exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
      have hgen : omegaGen (TwinDisc.secFam Ω (t * z)) = ⊤ :=
        omegaGen_quotFamily_eq_top _ _
          (omegaGen_restrictFamily_eq_top (cFam Ω (t * z)) (coreHull Ω (t * z)) rfl)
      have hD := hMF _ hlt (TwinDisc.secFam Ω (t * z)) (hypOmegaGen_secFam hΩ hc2) (secFam_twoGroup h2)
        (secFam_quat hc2 hq) oddCore_quot_eq_bot (secFam_aEmpty hΩ hA hc2) hgen htrans htt
      intro M' hM'
      exact hD _ (secImg_mem_secFam hMtq) M' hM'
  exact secPath_of_connected hΩ hc2 hMtq le_rfl hconn N hNtq

end Named

end CFSG.CGT.PushingUpLit.SolKNA.R4
