module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf20Pair
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf10Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtNbr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf13Star
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf8Class
public import CFSG.ClassicalInvolution.SmallCases.A7T22H51

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Exits

section Gen

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_quiet {B : Subgroup G} (hB : IsElemAbelian 2 B) {c t : G} (hcB : c ∈ B)
    (htB : t ∈ B) (hc1 : c ≠ 1) (ht1 : t ≠ 1) (hct : t ≠ c)
    (htC : t ∈ Subgroup.centralizer ({c} : Set G)) (hq : Quiet c t htC) : Hyp51At B c :=
  ⟨fun L₁ L₂ h₁ _ m₁ _ => (moved_false_of_quiet hB htB hcB hc1 ht1 hct htC hq h₁ m₁).elim,
    fun L hL hm => (moved_false_of_quiet hB htB hcB hc1 ht1 hct htC hq hL hm).elim⟩

theorem hyp51At_of_exit (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) {c t : G} (hcB : c ∈ B) (htB : t ∈ B) (hc1 : c ≠ 1)
    (ht1 : t ≠ 1) (hct : t ≠ c) (htC : t ∈ Subgroup.centralizer ({c} : Set G)) {J : Subgroup G}
    (he : ExitAt J c t htC) (hm : MovedOddFreeAt c t htC) : Hyp51At B c :=
  hyp51At_of_autOddFree hB htB hcB hc1 ht1 hct htC hm.1 fun L hL hmv =>
    he.autOddFree hSp hD4 hM12 hL
      (hmv _ (oddQuotMk_mem_modOdd htB htC)
        (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 htB ht1 hct htC))

end Gen

section Std

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem v3_out_gen (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (hPerp : PerpHypS n Y R S t) {c : Y} (hcc : c * c = 1) (hc1 : c ≠ 1) {J J' : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) (hJ' : J' ∈ CoreAssembly.conjClass (tightCore R))
    (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t) (hne : J' ≠ J)
    (hcJ : c ∈ trivialOnQuot J) (hcJ' : c ∈ trivialOnQuot J')
    (htC : t ∈ Subgroup.centralizer ({c} : Set Y)) :
    Quiet c t htC ∨ TwinExitPf9.LiftedAtSec J c t htC ∨ (ExitAt J c t htC ∧ MovedOddFreeAt c t htC) := by
  have hC := CoreData.of_S hPerp.core
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
  obtain ⟨S₀, h₀⟩ := TwinEdge.twinCoreHyp_core hPerp.core.toHyp
  have hid := TwinEdge.tightCore_idem R
  have hΩeq : CoreAssembly.conjClass (tightCore (tightCore R)) =
      CoreAssembly.conjClass (tightCore R) := by rw [hid]
  have hJ0 : J ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by rw [hΩeq]; exact hJ
  obtain ⟨SJ, hJd⟩ := exists_datum_at h₀ hid hJ0 htJ
  have hRcJ : tightCore J = J := tightCore_eq_of_mem hid hJ0
  have hcm : c ∈ centralizerModOdd ⊤ J :=
    ⟨Subgroup.mem_top _, hcJ.1, mem_normalizer_oddCore_of_mem_normalizer hcJ.1,
      fun l hl => hcJ.2 l hl⟩
  have hJ'tw : J' ∈ twinSet (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, conjClass_eq_of_mem hJ0, hΩeq]
    exact ⟨hJ', t, htJ, htJ'⟩
  have hne' : J' ≠ tightCore J := by rw [hRcJ]; exact hne
  exact TwinExitPf9.quietLiftedSecExit_of_twin hSp hD4 h4 hJd hRcJ hZ hcc hc1 hcm htC hJ'tw hne' hcJ'

variable {K K' K₃ K₄ : Subgroup Y} {a₁ a₂ a₃ a₄ : Y} {u₁ u₂ u₃ : Y}

set_option maxHeartbeats 1600000 in
theorem v3Hyp51U1_of_model (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n) (hP : PerpHypS n Y R S t)
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hK₄ : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K')
    (h43 : K₄ ≠ K₃) :
    Hyp51At (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) (u₁ * u₂) := by
  have hC := CoreData.of_S hP.core
  have hBelow : CIT3Below (Nat.card Y) := hC.card ▸ hC.below
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
  have hΩ := d.hyp
  have hcc : (u₁ * u₂) * (u₁ * u₂) = 1 := d.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet d.hz hK₄
  have hmem := tq_of_hyp22G d
  have hmem4 : K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    refine ⟨hK₄.1, ?_⟩
    have t14 : u₁ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.mem hK₄.1 h41.symm d.hz hz4 d.hu₁.1
    have t24 : u₂ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h42.symm d.hzK' hz4 d.hu₂.1
    exact (trivialOnQuot K₄).mul_mem t14 t24
  have htc : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * t = u₁ * (u₂ * t) := by group
      _ = u₁ * (t * u₂) := by rw [← d.comm_z₂]
      _ = (u₁ * t) * u₂ := by group
      _ = (t * u₁) * u₂ := by rw [← d.comm_z₁]
      _ = t * (u₁ * u₂) := by group
  have hu₂c : u₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * u₂ = (u₂ * u₁) * u₂ := by rw [d.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have hcm : ∀ {J : Subgroup Y}, u₂ ∈ trivialOnQuot J → u₂ ∈ centralizerModOdd ⊤ J := fun h =>
    ⟨Subgroup.mem_top _, h.1, Asc77.mem_normalizer_oddCore_of_mem_normalizer h.1,
      fun l hl => h.2 l hl⟩
  have t23 : u₂ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' d.hzK₃ d.hu₂.1
  have t24 : u₂ ∈ trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h42.symm d.hzK' hz4 d.hu₂.1
  have hB := d.isElemAbelian_B
  have hcB : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hu₃core : u₃ ∈ TwinADescent.coreAt (u₁ * u₂) K₃ := by
    have hu₃c : u₃ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      symm
      calc u₁ * u₂ * u₃ = u₁ * (u₂ * u₃) := by group
        _ = u₁ * (u₃ * u₂) := by rw [d.comm₂₃]
        _ = (u₁ * u₃) * u₂ := by group
        _ = (u₃ * u₁) * u₂ := by rw [d.comm₁₃]
        _ = u₃ * (u₁ * u₂) := by group
    have hle : Subgroup.zpowers u₃ ≤ K₃ ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
      Subgroup.zpowers_le.mpr ⟨d.hu₃.1, hu₃c⟩
    exact le_tightCore_of_isPGroup hle
      (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, d.hu₃.2]; norm_num))
      (Subgroup.mem_zpowers u₃)
  have out1 := v3_out_gen hSp hD4 h4 hP hcc d.mul_ne_one d.hK₃.1 hK₄.1 d.hzK₃ hz4 h43 hmem.2 hmem4.2 htc
  have out2 := v3_out_gen hSp hD4 h4 hP hcc d.mul_ne_one hK₄.1 d.hK₃.1 hz4 d.hzK₃ (Ne.symm h43)
    hmem4.2 hmem.2 htc
  have hlift : TwinExitPf9.LiftedAtSec K₃ (u₁ * u₂) t htc →
      TwinExitPf9.LiftedAtSec K₄ (u₁ * u₂) t htc →
      Hyp51At (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) (u₁ * u₂) := by
    intro l3 l4
    obtain ⟨M, M', hM, hM', hne, hcomm, hcM, hcM', hmM, -⟩ :=
      liftPair_of_twinsY hP hΩ hc2 hcc d.mul_ne_one hmem hmem4 h43 d.hzK₃ hz4 htc l3 l4 hu₂c
        (hcm t23) (hcm t24)
    have hu₃M : u₃ ∈ M := hmM u₃ hu₃core d.comm_z₃.symm
    refine TwinFrame.hyp51At_of_classicalOrQuiet_model hBelow hZ hB htB hcB d.mul_ne_one d.hz.ne_one
      (Ne.symm d.mul_ne_z) htc (Or.inl ⟨M, hM⟩) ?_
    intro L hL hmov
    exact alpha_of_lifted_sq hBelow hZ hB hcB d.mul_ne_one htB d.hz.ne_one (Ne.symm d.mul_ne_z) hM hM'
      hne hcomm hu₂c d.sq₂ hcM hcM' hu₃M d.sq₃ (Subgroup.subset_closure (by simp)) le_rfl hL hmov
  rcases out1 with q | l3 | ⟨e3, m3⟩
  · exact hyp51At_of_quiet hB hcB htB d.mul_ne_one d.hz.ne_one (Ne.symm d.mul_ne_z) htc q
  · rcases out2 with q | l4 | ⟨e4, m4⟩
    · exact hyp51At_of_quiet hB hcB htB d.mul_ne_one d.hz.ne_one (Ne.symm d.mul_ne_z) htc q
    · exact hlift l3 l4
    · exact hyp51At_of_exit hSp hD4 hM12 hB hcB htB d.mul_ne_one d.hz.ne_one (Ne.symm d.mul_ne_z)
        htc e4 m4
  · exact hyp51At_of_exit hSp hD4 hM12 hB hcB htB d.mul_ne_one d.hz.ne_one (Ne.symm d.mul_ne_z)
      htc e3 m3

set_option maxHeartbeats 1600000 in
theorem star_vertexY (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n) (hP : PerpHypS n Y R S t)
    (F : StarFrame (CoreAssembly.conjClass (tightCore R)) t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    Hyp51At (Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) (a₁ * a₂) := by
  have hΩ := F.hyp
  have hK := F.hK
  have hK' := F.hK'
  have hK₃ := F.hK₃
  have hK₄ := F.hK₄
  have hzK := F.hzK
  have hzK' := F.hzK'
  have hzK₃ := F.hzK₃
  have hzK₄ := F.hzK₄
  have h12 := F.n12
  have h13 := F.n13
  have h23 := F.n23
  have h14 := F.n14
  have h24 := F.n24
  have h34 := F.n34
  have ha₁ := F.h₁
  have ha₂ := F.h₂
  have ha₃ := F.h₃
  have ha₄ := F.h₄
  have o₁ := F.o₁
  have o₂ := F.o₂
  have o₃ := F.o₃
  have o₄ := F.o₄
  have c12 := F.c12
  have c13 := F.c13
  have c14 := F.c14
  have c23 := F.c23
  have c24 := F.c24
  have c34 := F.c34
  have hB := F.isElemAbelian
  have hc1 := F.p_ne_one
  have hct : t ≠ a₁ * a₂ := Ne.symm F.p_ne_t
  classical
  have hC := CoreData.of_S hP.core
  have hBelow : CIT3Below (Nat.card Y) := hC.card ▸ hC.below
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
  have hcB : a₁ * a₂ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hcc : (a₁ * a₂) * (a₁ * a₂) = 1 := Lemma52Proof.mul_self_eq_one_of_mem hB hcB
  have hc2 : IsPGroup 2 (Subgroup.zpowers (a₁ * a₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have s1 : a₁ * a₁ = t := T7A.sq_eq_of_orderOf_four hzK ha₁ o₁
  have ct : ∀ {J : Subgroup Y} {x : Y}, IsUniqueInvolution J t → x ∈ J → t * x = x * t :=
    fun hJ hx => hJ.commute_of_mem hx
  have hcC : ∀ x : Y, x * a₁ = a₁ * x → x * a₂ = a₂ * x → x ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) := by
    intro x h1 h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc a₁ * a₂ * x = a₁ * (a₂ * x) := by group
      _ = a₁ * (x * a₂) := by rw [← h2]
      _ = (a₁ * x) * a₂ := by group
      _ = (x * a₁) * a₂ := by rw [← h1]
      _ = x * (a₁ * a₂) := by group
  have htC : t ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) :=
    hcC t (ct hzK ha₁) (ct hzK' ha₂)
  have ha₃C : a₃ ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) := hcC a₃ c13.symm c23.symm
  have ha₄C : a₄ ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) := hcC a₄ c14.symm c24.symm
  have ha₂C : a₂ ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) := hcC a₂ c12.symm rfl
  have hbC : a₃ * a₄ ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) :=
    Subgroup.mul_mem _ ha₃C ha₄C
  have tqm : ∀ {J : Subgroup Y}, J ∈ CoreAssembly.conjClass (tightCore R) → IsUniqueInvolution J t →
      J ≠ K → J ≠ K' → J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (a₁ * a₂) := by
    intro J hJ hzJ hJK hJK'
    refine ⟨hJ, ?_⟩
    have t1 : a₁ ∈ trivialOnQuot J :=
      A7T22.le_trivialOnQuot_of_twin hΩ hK hJ hJK.symm hzK hzJ ha₁
    have t2 : a₂ ∈ trivialOnQuot J :=
      A7T22.le_trivialOnQuot_of_twin hΩ hK' hJ hJK'.symm hzK' hzJ ha₂
    exact (trivialOnQuot J).mul_mem t1 t2
  have hmem3 := tqm hK₃ hzK₃ h13 h23
  have hmem4 := tqm hK₄ hzK₄ h14 h24
  have hcm : ∀ {J : Subgroup Y}, a₂ ∈ trivialOnQuot J → a₂ ∈ centralizerModOdd ⊤ J := fun h =>
    ⟨Subgroup.mem_top _, h.1, Asc77.mem_normalizer_oddCore_of_mem_normalizer h.1,
      fun l hl => h.2 l hl⟩
  have t23 : a₂ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ hK' hK₃ h23.symm hzK' hzK₃ ha₂
  have t24 : a₂ ∈ trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ hK' hK₄ h24.symm hzK' hzK₄ ha₂
  have out1 := v3_out_gen hSp hD4 h4 hP hcc hc1 hK₃ hK₄ hzK₃ hzK₄ h34 hmem3.2 hmem4.2 htC
  have out2 := v3_out_gen hSp hD4 h4 hP hcc hc1 hK₄ hK₃ hzK₄ hzK₃ (Ne.symm h34) hmem4.2 hmem3.2 htC
  have hlift : TwinExitPf9.LiftedAtSec K₃ (a₁ * a₂) t htC → TwinExitPf9.LiftedAtSec K₄ (a₁ * a₂) t htC →
      Hyp51At (Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) (a₁ * a₂) := by
    intro l3 l4
    obtain ⟨M, M', hM, hM', hne, hcomm, -, -, hmM, hmM'⟩ :=
      liftPair_of_twinsY hP hΩ hc2 hcc hc1 hmem3 hmem4 h34 hzK₃ hzK₄ htC l3 l4 ha₂C (hcm t23) (hcm t24)
    have incore : ∀ {J : Subgroup Y} {x : Y}, x ∈ J → orderOf x = 4 →
        x ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) → x ∈ TwinADescent.coreAt (a₁ * a₂) J := by
      intro J x hx ho hxC
      have hle : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({a₁ * a₂} : Set Y) :=
        Subgroup.zpowers_le.mpr ⟨hx, hxC⟩
      exact le_tightCore_of_isPGroup hle
        (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ho]; norm_num))
        (Subgroup.mem_zpowers x)
    have ha₃M : a₃ ∈ M := hmM a₃ (incore ha₃ o₃ ha₃C) (ct hzK₃ ha₃).symm
    have ha₄M' : a₄ ∈ M' := hmM' a₄ (incore ha₄ o₄ ha₄C) (ct hzK₄ ha₄).symm
    have hgen : Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) =
        Subgroup.closure ({t, a₃ * a₄, a₁ * a₂} : Set Y) := by
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hsnc : ¬ ({a₁ * a₂} : Set Y) ⊆ Subgroup.center Y := fun h => hc1 (by
      have h1 : a₁ * a₂ ∈ Subgroup.center Y := h (Set.mem_singleton _)
      rwa [hZ, Subgroup.mem_bot] at h1)
    refine TwinFrame.hyp51At_of_classicalOrQuiet_inner hBelow hZ TL4.d4OddAutInnerNC3_proved hB hgen
      hc1 hzK.ne_one hct htC hbC (Or.inl ⟨M, hM⟩) ?_
    intro L hL hmov
    have hΦ := secData3_sFamily3 hM hM' hM
    obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
    obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one (a₁ * a₂) M M' M)
    have hMt : IsUniqueInvolution M t := isUniqueInvolution_of_sectionMember3 hM
    have hM't : IsUniqueInvolution M' t := isUniqueInvolution_of_sectionMember3 hM'
    have htj : oddQuotMk (a₁ * a₂) ⟨t, htC⟩ ∈ secComp hΦ D j :=
      hj (oddQuotMk_mem_modOdd hMt.mem htC)
    have htmov : ∃ w ∈ L, oddQuotMk (a₁ * a₂) ⟨t, htC⟩ * w ≠ w * oddQuotMk (a₁ * a₂) ⟨t, htC⟩ :=
      hmov _ (oddQuotMk_mem_modOdd htB htC)
        (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 htB hzK.ne_one hct htC)
    have hLj : L = secComp hΦ D j := eq_secComp_of_not_commute hΦ D htj hL htmov
    subst hLj
    have h3j : oddQuotMk (a₁ * a₂) ⟨a₃, ha₃C⟩ ∈ secComp hΦ D j :=
      hj (oddQuotMk_mem_modOdd ha₃M ha₃C)
    have hM'j : modOdd (a₁ * a₂) M' ≤ secComp hΦ D j :=
      Q3T7.modOdd_twin_le_secComp3 hΦ D hB hcB hc1 htB hzK.ne_one hct htC hmov hL
        (mem_sFamily3_two (a₁ * a₂) M M' M) hM't.mem
    have h4j : oddQuotMk (a₁ * a₂) ⟨a₄, ha₄C⟩ ∈ secComp hΦ D j :=
      hM'j (oddQuotMk_mem_modOdd ha₄M' ha₄C)
    have e : oddQuotMk (a₁ * a₂) ⟨a₃ * a₄, hbC⟩ =
        oddQuotMk (a₁ * a₂) ⟨a₃, ha₃C⟩ * oddQuotMk (a₁ * a₂) ⟨a₄, ha₄C⟩ :=
      map_mul (oddQuotMk (a₁ * a₂)) (⟨a₃, ha₃C⟩ : ↥(Subgroup.centralizer ({a₁ * a₂} : Set Y))) ⟨a₄, ha₄C⟩
    rw [e]
    exact Subgroup.mul_mem _ h3j h4j
  rcases out1 with q | l3 | ⟨e3, m3⟩
  · exact hyp51At_of_quiet hB hcB htB hc1 hzK.ne_one hct htC q
  · rcases out2 with q | l4 | ⟨e4, m4⟩
    · exact hyp51At_of_quiet hB hcB htB hc1 hzK.ne_one hct htC q
    · exact hlift l3 l4
    · exact hyp51At_of_exit hSp hD4 hM12 hB hcB htB hc1 hzK.ne_one hct htC e4 m4
  · exact hyp51At_of_exit hSp hD4 hM12 hB hcB htB hc1 hzK.ne_one hct htC e3 m3

end Std

end Exits

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
