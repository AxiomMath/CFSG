module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205AzLiftPair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205AzFacts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf20OmegaA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf21M20
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtU
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Vertex

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

structure Vertex205 (_d : Std20Frame K K' J S R R' W V z t) (a c : G) : Prop where
  mem : c ∈ Subgroup.closure ({z, t, a} : Set G)
  sq : c * c = 1
  ne_one : c ≠ 1
  z_ne : z ≠ c
  z_cent : z ∈ Subgroup.centralizer ({c} : Set G)
  t_cent : t ∈ Subgroup.centralizer ({c} : Set G)
  tqK : c ∈ Balance.Bootstrap.trivialOnQuot K
  tqK' : c ∈ Balance.Bootstrap.trivialOnQuot K'
  R_le : R ≤ Subgroup.centralizer ({c} : Set G)
  R'_le : R' ≤ Subgroup.centralizer ({c} : Set G)
  card_lt : Nat.card ↥(Subgroup.centralizer ({c} : Set G)) < Nat.card G
  gen : Subgroup.closure ({z, t, a} : Set G) = Subgroup.closure ({z, t, c} : Set G)

theorem vertex205_a (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    Vertex205 d a a where
  mem := Subgroup.subset_closure (by simp)
  sq := hd.conf.ha2
  ne_one := hd.conf.ha1
  z_ne := a_ne_z d hd
  z_cent := Subgroup.mem_centralizer_singleton_iff.mpr (a_comm_z d hd).symm
  t_cent := Subgroup.mem_centralizer_singleton_iff.mpr (d.s_comm_t hd.conf.hA).symm
  tqK := ⟨d.cent_le_normalizer hd.conf.hA.1, fun x hx => d.s_comm_K hd.conf.hA hx⟩
  tqK' := ⟨d.cent_le_normalizer' hd.conf.hA.1, fun x hx => d.s_comm_K' hd.conf.hA hx⟩
  R_le := R_le_centralizer_a d hd
  R'_le := R'_le_centralizer_a d hd
  card_lt := card_centralizer_lt d hd
  gen := rfl

theorem vertex205_az (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    Vertex205 d a (a * z) where
  mem := az_mem_B d hd
  sq := az_mul_self d hd
  ne_one := az_ne_one d hd
  z_ne := z_ne_az d hd
  z_cent := z_mem_centralizer_az d hd
  t_cent := t_mem_centralizer_az d hd
  tqK := az_mem_trivialOnQuot_K d hd
  tqK' := az_mem_trivialOnQuot_K' d hd
  R_le := R_le_centralizer_az d hd
  R'_le := R'_le_centralizer_az d hd
  card_lt := card_centralizer_az_lt d hd
  gen := closure_zta_eq_closure_zt_az a

variable {a c : G} {d : Std20Frame K K' J S R R' W V z t}

theorem isElemAbelian_B_vertex (hd : Frame205Data d a) :
    IsElemAbelian 2 (Subgroup.closure ({z, t, a} : Set G)) :=
  d.s_B_isElemAbelian hd.conf.hA hd.conf.ha2

theorem isPGroup_zpowers_vertex (hv : Vertex205 d a c) : IsPGroup 2 ↥(Subgroup.zpowers c) :=
  CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hv.sq

theorem frameKa_mem_omegaAFam_of_vertex (hv : Vertex205 d a c) :
    frameKa K c ∈
      omegaAFam (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G)) :=
  ⟨tightCore (K ⊓ Subgroup.centralizer ({c} : Set G)),
    ⟨K, CoreAssembly.mem_conjClass_self K, ⟨R, d.hR, hv.R_le⟩, rfl⟩,
    (tightCore_le _).trans inf_le_right, rfl⟩

theorem frameKa'_mem_omegaAFam_of_vertex (hv : Vertex205 d a c) :
    frameKa K' c ∈
      omegaAFam (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G)) :=
  ⟨tightCore (K' ⊓ Subgroup.centralizer ({c} : Set G)),
    ⟨K', d.late_mem_K', ⟨R', d.hR', hv.R'_le⟩, rfl⟩,
    (tightCore_le _).trans inf_le_right, rfl⟩

theorem z_mem_frameKa_of_vertex (hv : Vertex205 d a c) :
    (⟨z, hv.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ frameKa K c := by
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hle : Subgroup.zpowers z ≤ K ⊓ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨d.viol.hzK.mem, hv.z_cent⟩
  have hz : z ∈ tightCore (K ⊓ Subgroup.centralizer ({c} : Set G)) :=
    le_tightCore_of_isPGroup hle (isPGroup_zpowers_of_mul_self_eq_one d.viol.hzK.sq hz1)
      (Subgroup.mem_zpowers z)
  exact Subgroup.mem_subgroupOf.mpr hz

theorem z_mem_frameKa'_of_vertex (hv : Vertex205 d a c) :
    (⟨z, hv.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ frameKa K' c := by
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hle : Subgroup.zpowers z ≤ K' ⊓ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨d.late_hzK'.mem, hv.z_cent⟩
  have hz : z ∈ tightCore (K' ⊓ Subgroup.centralizer ({c} : Set G)) :=
    le_tightCore_of_isPGroup hle (isPGroup_zpowers_of_mul_self_eq_one d.viol.hzK.sq hz1)
      (Subgroup.mem_zpowers z)
  exact Subgroup.mem_subgroupOf.mpr hz

theorem exists_not_comm_of_movedByAll_vertex (hd : Frame205Data d a) (hv : Vertex205 d a c)
    {L : Subgroup (Balance.OddQuot c)}
    (hmov : MovedByAll (Subgroup.closure ({z, t, a} : Set G)) c L) :
    ∃ y ∈ L, Balance.oddQuotMk c ⟨z, hv.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hv.z_cent⟩ := by
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  exact hmov _ (Balance.oddQuotMk_mem_modOdd hzB hv.z_cent)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers (isElemAbelian_B_vertex hd) hv.mem hv.ne_one hzB
      d.viol.hzK.ne_one hv.z_ne hv.z_cent)

theorem hyp51At_of_liftedAt_vertex (hcit : CIT3Below (Nat.card G)) (hd : Frame205Data d a)
    (hv : Vertex205 d a c) (l : LiftedAt K c z) (l' : LiftedAt K' c z) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  have hB := isElemAbelian_B_vertex hd
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hZ : Subgroup.center G = ⊥ := FrameCore.center d.nonabelian
  obtain ⟨M, hM, hKM⟩ := l
  obtain ⟨M', hM', hKM'⟩ := l'
  rw [tgt_coreAt_eq] at hKM hKM'
  refine TwinFrame.hyp51At_of_classicalOrQuiet_inner hcit hZ TL4.d4OddAutInnerNC3_proved hB
    hv.gen hv.ne_one hz1 hv.z_ne hv.z_cent hv.t_cent (Or.inl ⟨M, hM⟩) ?_
  intro L hL hmov
  have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => hv.ne_one (by
    have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton _)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := secData3_sFamily3 hM hM' hM
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hcit hsnc
  obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c M M' M)
  have hMz : IsUniqueInvolution M z := isUniqueInvolution_of_sectionMember3 hM
  have hM'z : IsUniqueInvolution M' z := isUniqueInvolution_of_sectionMember3 hM'
  have hzj : oddQuotMk c ⟨z, hv.z_cent⟩ ∈ secComp hΦ D j :=
    hj (oddQuotMk_mem_modOdd hMz.mem hv.z_cent)
  have hzmov : ∃ w ∈ L, oddQuotMk c ⟨z, hv.z_cent⟩ * w ≠ w * oddQuotMk c ⟨z, hv.z_cent⟩ :=
    hmov _ (oddQuotMk_mem_modOdd hzB hv.z_cent)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hv.mem hv.ne_one hzB hz1 hv.z_ne hv.z_cent)
  have hLj : L = secComp hΦ D j := eq_secComp_of_not_commute hΦ D hzj hL hzmov
  subst hLj
  have hM'j : modOdd c M' ≤ secComp hΦ D j :=
    Q3T7.modOdd_twin_le_secComp3 hΦ D hB hv.mem hv.ne_one hzB hz1 hv.z_ne hv.z_cent hmov hL
      (mem_sFamily3_two c M M' M) hM'z.mem
  have hRj : ∀ r ∈ R, ∀ hrC : r ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨r, hrC⟩ ∈ secComp hΦ D j := by
    intro r hr hrC
    have hcore : r ∈ TwinADescent.coreAt c K :=
      le_tightCore_of_isPGroup (le_inf d.hR.1 hv.R_le) d.hR.2.1 hr
    exact hj (oddQuotMk_mem_modOdd (hKM hcore) hrC)
  have hR'j : ∀ r ∈ R', ∀ hrC : r ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨r, hrC⟩ ∈ secComp hΦ D j := by
    intro r hr hrC
    have hcore : r ∈ TwinADescent.coreAt c K' :=
      le_tightCore_of_isPGroup (le_inf d.hR'.1 hv.R'_le) d.hR'.2.1 hr
    exact hM'j (oddQuotMk_mem_modOdd (hKM' hcore) hrC)
  have hRQ : R.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      (secComp hΦ D j).comap (oddQuotMk c) := fun x hx =>
    hRj x.1 (Subgroup.mem_subgroupOf.mp hx) x.2
  have hR'Q : R'.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      (secComp hΦ D j).comap (oddQuotMk c) := fun x hx =>
    hR'j x.1 (Subgroup.mem_subgroupOf.mp hx) x.2
  have hsup : (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      (secComp hΦ D j).comap (oddQuotMk c) := by
    rw [Subgroup.subgroupOf_sup hv.R_le hv.R'_le]
    exact sup_le hRQ hR'Q
  exact hsup (Subgroup.mem_subgroupOf.mpr (t_mem_sup_R_R' d) :
    (⟨t, hv.t_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)))

end Vertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
