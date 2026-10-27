module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.CocodeOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.CertSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.T0
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneAction

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
  Certificates.RouteP.M24Defect
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] def cocodeMCols : List ℕ := [1847, 1425, 994, 211, 600, 554, 1365, 1286, 1570, 319, 571]

@[expose] def cocodeNCols : List ℕ := [1904, 454, 1452, 1351, 848, 1920, 1318, 200, 141, 801, 1127]

theorem cocodeMCols_lt : ∀ c ∈ cocodeMCols, c < 2 ^ 11 := by decide

theorem cocodeNCols_lt : ∀ c ∈ cocodeNCols, c < 2 ^ 11 := by decide

theorem length_cocodeMCols : cocodeMCols.length = 11 := rfl

theorem length_conjACols : conjACols.length = 11 := rfl

theorem length_conjBCols : conjBCols.length = 11 := rfl

theorem actM_cocodeN_cocodeM : ∀ m < 2 ^ 11, actM cocodeNCols (actM cocodeMCols m) = m := by
  decide +kernel

theorem actM_cocodeM_cocodeN : ∀ m < 2 ^ 11, actM cocodeMCols (actM cocodeNCols m) = m := by
  decide +kernel

theorem actM_cocodeM_conjA : ∀ m < 2 ^ 11,
    actM cocodeMCols (actM conjACols m) = actM (matA aArr) (actM cocodeMCols m) := by
  decide +kernel

theorem actM_cocodeM_conjB : ∀ m < 2 ^ 11,
    actM cocodeMCols (actM conjBCols m) = actM (matA bArr) (actM cocodeMCols m) := by
  decide +kernel

theorem actM_mod_eleven {cs : List ℕ} (h : cs.length = 11) (m : ℕ) :
    actM cs (m % 2 ^ 11) = actM cs m := by
  have := actM_mod cs m
  rwa [h] at this

theorem actM_cocodeM_conjA_all (m : ℕ) :
    actM cocodeMCols (actM conjACols m) = actM (matA aArr) (actM cocodeMCols m) := by
  have h := actM_cocodeM_conjA (m % 2 ^ 11) (Nat.mod_lt _ (by norm_num))
  rwa [actM_mod_eleven length_conjACols, actM_mod_eleven length_cocodeMCols] at h

theorem actM_cocodeM_conjB_all (m : ℕ) :
    actM cocodeMCols (actM conjBCols m) = actM (matA bArr) (actM cocodeMCols m) := by
  have h := actM_cocodeM_conjB (m % 2 ^ 11) (Nat.mod_lt _ (by norm_num))
  rwa [actM_mod_eleven length_conjBCols, actM_mod_eleven length_cocodeMCols] at h

@[expose] noncomputable def cocodeCoordsM : MaskVM W11 11 where
  vm m := toW 11 (actM cocodeMCols m)
  vm_xor a b := by rw [actM_xor, toW_xor]
  vm_mod a := by rw [actM_mod_eleven length_cocodeMCols a]
  vm_inj a b ha hb h := by
    have h1 := toW_inj (actM_lt cocodeMCols_lt a) (actM_lt cocodeMCols_lt b) h
    have h2 := congrArg (actM cocodeNCols) h1
    rwa [actM_cocodeN_cocodeM a ha, actM_cocodeN_cocodeM b hb] at h2
  vm_surj w := by
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
    exact ⟨actM cocodeNCols m, actM_lt cocodeNCols_lt m, by rw [actM_cocodeM_cocodeN m hm]⟩

@[expose] noncomputable def epsQ (m : ℕ) : E0q :=
  ⟨⟨epsMask m, E0_le_Zq (epsMask_mem_E0 m)⟩, epsMask_mem_E0 m⟩

section Coordinates

@[expose] noncomputable def cocodeCoordsEps : MaskVM E0q 11 where
  vm := epsQ
  vm_xor a b := Subtype.ext (Subtype.ext (epsMask_xor a b))
  vm_mod a := Subtype.ext (Subtype.ext (epsMask_mod a))
  vm_inj a b ha hb h := epsMask_injOn ha hb (congrArg (fun x : E0q => ((x : Zq) : Q3)) h)
  vm_surj v := by
    obtain ⟨m, hm, hmv⟩ := exists_epsMask_of_mem_E0 (show ((v : Zq) : Q3) ∈ E0 from v.2)
    exact ⟨m, hm, Subtype.ext (Subtype.ext hmv)⟩

@[expose] noncomputable def e0 : ↥E0q ≃* W11 :=
  (maskVMEquiv cocodeCoordsEps).symm.trans (maskVMEquiv cocodeCoordsM)

theorem e0_epsQ (m : ℕ) : e0 (epsQ m) = toW 11 (actM cocodeMCols m) := by
  have h : maskVMEquiv cocodeCoordsEps (toW 11 m) = epsQ m := maskVMEquiv_toW _ m
  rw [e0, MulEquiv.trans_apply, ← h, MulEquiv.symm_apply_apply, maskVMEquiv_toW]
  rfl

end Coordinates

@[expose] noncomputable def tauM24 : Equiv.Perm (Fin 24) := bridgeQ⁻¹ * sigmaM24

theorem tauM24_zero : tauM24 0 = 23 := by decide

theorem tauM24_one : tauM24 1 = 13 := by decide

theorem tauM24_mul_PA : tauM24 * PA * tauM24⁻¹ = bridgePA := by
  rw [tauM24, ← conj_m24gA, bridgePA]
  group

theorem tauM24_mul_PB : tauM24 * PB * tauM24⁻¹ = bridgePB⁻¹ := by
  have h : PB = (sigmaM24⁻¹ * m24gB * sigmaM24)⁻¹ := by rw [conj_m24gB, inv_inv]
  rw [tauM24, h, bridgePB]
  group

section PiZq

theorem tauM24_conj_mem {n : Q3} (hn : n ∈ Zq) :
    tauM24 * planeHom ⟨n, hn⟩ * tauM24⁻¹ ∈ AutPerm := by
  refine Subgroup.closure_induction
    (p := fun g hg => tauM24 * planeHom ⟨g, hg⟩ * tauM24⁻¹ ∈ AutPerm) ?_ ?_ ?_ ?_ hn
  · rintro x ((rfl | rfl) | ⟨j, rfl⟩)
    · rw [planeHom_aElt, tauM24_mul_PA]
      exact bridgePA_mem
    · rw [planeHom_bElt, tauM24_mul_PB]
      exact AutPerm.inv_mem bridgePB_mem
    · rw [planeHom_eq_one_of_mem_E0 (g := ⟨epsElt j, epsElt_mem_Zq j⟩) (epsElt_mem_E0 j)]
      simp
  · show tauM24 * planeHom 1 * tauM24⁻¹ ∈ AutPerm
    simp
  · intro x y hx hy hx' hy'
    have h : tauM24 * planeHom ⟨x * y, Zq.mul_mem hx hy⟩ * tauM24⁻¹ =
        (tauM24 * planeHom ⟨x, hx⟩ * tauM24⁻¹) * (tauM24 * planeHom ⟨y, hy⟩ * tauM24⁻¹) := by
      rw [show (⟨x * y, Zq.mul_mem hx hy⟩ : Zq) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
      group
    rw [h]
    exact AutPerm.mul_mem hx' hy'
  · intro x hx hx'
    have h : tauM24 * planeHom ⟨x⁻¹, Zq.inv_mem hx⟩ * tauM24⁻¹ =
        (tauM24 * planeHom ⟨x, hx⟩ * tauM24⁻¹)⁻¹ := by
      rw [show (⟨x⁻¹, Zq.inv_mem hx⟩ : Zq) = (⟨x, hx⟩ : Zq)⁻¹ from rfl, map_inv]
      group
    rw [h]
    exact AutPerm.inv_mem hx'

theorem tauM24_conj_mem' (n : Zq) :
    (MulAut.conj tauM24).toMonoidHom (planeHom n) ∈ AutPerm := by
  obtain ⟨n, hn⟩ := n
  simpa [MulAut.conj_apply] using tauM24_conj_mem hn

@[expose] noncomputable def piZq : Zq →* ↥AutPerm :=
  ((MulAut.conj tauM24).toMonoidHom.comp planeHom).codRestrict AutPerm tauM24_conj_mem'

theorem coe_piZq (n : Zq) :
    ((piZq n : ↥AutPerm) : Equiv.Perm (Fin 24)) = tauM24 * planeHom n * tauM24⁻¹ := rfl

theorem piZq_aElt : piZq ⟨aElt, aElt_mem_Zq⟩ = genA :=
  Subtype.ext (by rw [coe_piZq, planeHom_aElt, tauM24_mul_PA]; rfl)

theorem piZq_bElt : piZq ⟨bElt, bElt_mem_Zq⟩ = genB :=
  Subtype.ext (by rw [coe_piZq, planeHom_bElt, tauM24_mul_PB]; rfl)

theorem piZq_eq_one_of_mem_E0q {n : Zq} (hn : n ∈ E0q) : piZq n = 1 :=
  Subtype.ext (by rw [coe_piZq, planeHom_eq_one_of_mem_E0 hn]; simp)

theorem piZq_eq_one_iff {n : Zq} : piZq n = 1 ↔ planeHom n = 1 := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [coe_piZq] at h1
    exact conj_eq_one_iff.1 h1
  · intro h
    exact Subtype.ext (by rw [coe_piZq, h]; simp)

theorem piZq_range_eq_top : piZq.range = ⊤ := by
  rw [eq_top_iff, ← closure_genA_genB, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨_, piZq_aElt⟩
  · exact ⟨_, piZq_bElt⟩

end PiZq

section Action

theorem exists_epsQ (x : E0q) : ∃ m, epsQ m = x := by
  obtain ⟨m, -, hm⟩ := cocodeCoordsEps.vm_surj x
  exact ⟨m, hm⟩

@[expose] noncomputable def actZq : ↥Zq →* MulAut W11 :=
  (MulAut.congr e0).toMonoidHom.comp (@MulAut.conjNormal ↥Zq _ E0q E0q_normal)

theorem coe_conjNormal (n : Zq) (x : E0q) :
    (((@MulAut.conjNormal ↥Zq _ E0q E0q_normal) n x : E0q) : Zq) = n * x * n⁻¹ := by
  haveI := E0q_normal
  exact MulAut.conjNormal_apply n x

theorem actZq_apply (n : Zq) (x : E0q) :
    actZq n (e0 x) = e0 ((@MulAut.conjNormal ↥Zq _ E0q E0q_normal) n x) := by
  show e0 ((@MulAut.conjNormal ↥Zq _ E0q E0q_normal) n (e0.symm (e0 x))) = _
  rw [MulEquiv.symm_apply_apply]

theorem actZq_epsQ {n : Zq} {cols : List ℕ}
    (h : ∀ m, (n : Q3) * epsMask m * (n : Q3)⁻¹ = epsMask (actM cols m)) (m : ℕ) :
    actZq n (e0 (epsQ m)) = e0 (epsQ (actM cols m)) := by
  rw [actZq_apply]
  refine congrArg e0 (Subtype.ext ?_)
  rw [coe_conjNormal]
  exact Subtype.ext (h m)

theorem actZq_eq_one {n : Zq} (h : ∀ x : E0q, n * (x : Zq) = (x : Zq) * n) : actZq n = 1 := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e0.surjective w
  have hx : (@MulAut.conjNormal ↥Zq _ E0q E0q_normal) n x = x :=
    Subtype.ext (by rw [coe_conjNormal, h x, mul_inv_cancel_right])
  rw [actZq_apply, hx]
  rfl

theorem actZq_aElt : actZq ⟨aElt, aElt_mem_Zq⟩ = rho11 AutPerm le_rfl genA := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e0.surjective w
  obtain ⟨m, rfl⟩ := exists_epsQ x
  have h1 : actZq ⟨aElt, aElt_mem_Zq⟩ (e0 (epsQ m)) = e0 (epsQ (actM conjACols m)) :=
    actZq_epsQ (fun m => aElt_mul_epsMask_mul_inv m) m
  have h2 : rho11 AutPerm le_rfl genA (e0 (epsQ m)) =
      toW 11 (actM (matA aArr) (actM cocodeMCols m)) := by
    rw [e0_epsQ, ← toW_actM_matA hasArr_genA]
  rw [h1, h2, e0_epsQ, actM_cocodeM_conjA_all]

theorem actZq_bElt : actZq ⟨bElt, bElt_mem_Zq⟩ = rho11 AutPerm le_rfl genB := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨x, rfl⟩ := e0.surjective w
  obtain ⟨m, rfl⟩ := exists_epsQ x
  have h1 : actZq ⟨bElt, bElt_mem_Zq⟩ (e0 (epsQ m)) = e0 (epsQ (actM conjBCols m)) :=
    actZq_epsQ (fun m => bElt_mul_epsMask_mul_inv m) m
  have h2 : rho11 AutPerm le_rfl genB (e0 (epsQ m)) =
      toW 11 (actM (matA bArr) (actM cocodeMCols m)) := by
    rw [e0_epsQ, ← toW_actM_matA hasArr_genB]
  rw [h1, h2, e0_epsQ, actM_cocodeM_conjB_all]

theorem mul_comm_of_mem_E0q {n : Zq} (hn : n ∈ E0q) (x : E0q) : n * (x : Zq) = (x : Zq) * n :=
  Subtype.ext (E0_comm hn x.2)

theorem actZq_eq : actZq = (rho11 AutPerm le_rfl).comp piZq := by
  refine MonoidHom.ext fun n => ?_
  obtain ⟨n, hn⟩ := n
  refine Subgroup.closure_induction
    (p := fun n hn => actZq ⟨n, hn⟩ = (rho11 AutPerm le_rfl) (piZq ⟨n, hn⟩)) ?_ ?_ ?_ ?_ hn
  · rintro x ((rfl | rfl) | ⟨j, rfl⟩)
    · rw [piZq_aElt]
      exact actZq_aElt
    · rw [piZq_bElt]
      exact actZq_bElt
    · rw [piZq_eq_one_of_mem_E0q (n := ⟨epsElt j, epsElt_mem_Zq j⟩) (epsElt_mem_E0 j), map_one]
      exact actZq_eq_one (mul_comm_of_mem_E0q (epsElt_mem_E0 j))
  · show actZq 1 = (rho11 AutPerm le_rfl) (piZq 1)
    rw [map_one, map_one, map_one]
  · intro x y hx hy hxh hyh
    show actZq (⟨x, hx⟩ * ⟨y, hy⟩) = (rho11 AutPerm le_rfl) (piZq (⟨x, hx⟩ * ⟨y, hy⟩))
    rw [map_mul, map_mul, map_mul, hxh, hyh]
  · intro x hx hxh
    show actZq (⟨x, hx⟩ : Zq)⁻¹ = (rho11 AutPerm le_rfl) (piZq (⟨x, hx⟩ : Zq)⁻¹)
    rw [map_inv, map_inv, map_inv, hxh]

end Action

section Extension

theorem cocodeExtension_Zq : CocodeExtension ↥Zq (E0.subgroupOf Zq) e0 where
  normal := E0q_normal
  centralizer_eq := by
    ext n
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hn
      have h1 : actZq n = 1 := actZq_eq_one fun x => (hn x x.2).symm
      have h2 : piZq n = 1 := by
        apply rho11_injective AutPerm le_rfl
        rw [map_one, ← MonoidHom.comp_apply, ← actZq_eq, h1]
      have h3 : n ∈ planeHom.ker := by
        rw [MonoidHom.mem_ker]
        exact piZq_eq_one_iff.1 h2
      rw [planeHom_ker_eq] at h3
      exact h3
    · intro hn x hx
      exact (mul_comm_of_mem_E0q hn ⟨x, hx⟩).symm
  range_eq := by
    rw [MonoidHom.map_range]
    show actZq.range = img11 AutPerm
    rw [actZq_eq, ← range_rho11_eq_img11 AutPerm le_rfl, MonoidHom.range_comp, piZq_range_eq_top,
      Subgroup.map_top]

theorem act_cocodeExtension_Zq : cocodeExtension_Zq.act = actZq := rfl

theorem π_cocodeExtension_Zq (n : Zq) :
    ((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) =
      tauM24 * planeHom n * tauM24⁻¹ := by
  have h : cocodeExtension_Zq.π n = piZq n := by
    apply rho11_injective AutPerm le_rfl
    rw [cocodeExtension_Zq.rho_π, act_cocodeExtension_Zq, actZq_eq]
    rfl
  rw [h]
  rfl

theorem smul_planePt_eq_planePt_iff (n : Zq) (i j : Fin 24) :
    (n : Q3) • planePt i = planePt j ↔ planeHom n i = j := by
  rw [← planePt_planeHom, planePt_injective.eq_iff]

theorem mem_B0_iff (n : Zq) : (n : Q3) ∈ B0 ↔ planeHom n 0 = 0 ∧ planeHom n 1 = 1 := by
  rw [B0, Subgroup.mem_inf, mem_L0_iff, Zp_eq_stabilizer, MulAction.mem_stabilizer_iff,
    ← planePt_zero, ← planePt_one, smul_planePt_eq_planePt_iff, smul_planePt_eq_planePt_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, n.2⟩⟩

theorem B0_subgroupOf_Zq_eq_Bduad :
    B0.subgroupOf Zq = cocodeExtension_Zq.Bduad (tauM24 0) (tauM24 1) := by
  ext n
  rw [Subgroup.mem_subgroupOf, CocodeExtension.mem_Bduad_iff, π_cocodeExtension_Zq, mem_B0_iff]
  simp [Equiv.Perm.mul_apply]

theorem mem_B0_iff_mem_Bduad (n : Zq) :
    (n : Q3) ∈ B0 ↔ n ∈ cocodeExtension_Zq.Bduad (tauM24 0) (tauM24 1) := by
  rw [← B0_subgroupOf_Zq_eq_Bduad, Subgroup.mem_subgroupOf]

theorem mem_Ze_iff_π (n : Zq) :
    (n : Q3) ∈ Ze ↔
      (((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 0) = tauM24 0 ∧
        ((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 1) = tauM24 1) ∨
      (((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 0) = tauM24 1 ∧
        ((cocodeExtension_Zq.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) (tauM24 1) = tauM24 0) := by
  rw [mem_Ze_iff, ← planePt_zero, ← planePt_one, smul_planePt_eq_planePt_iff,
    smul_planePt_eq_planePt_iff, smul_planePt_eq_planePt_iff, smul_planePt_eq_planePt_iff,
    π_cocodeExtension_Zq]
  simp [Equiv.Perm.mul_apply]

end Extension

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
