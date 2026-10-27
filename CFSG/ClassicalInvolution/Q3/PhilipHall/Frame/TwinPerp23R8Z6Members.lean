module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Pkg
public import CFSG.ClassicalInvolution.Sp62Rec.I1.ActionData
import CFSG.ClassicalInvolution.Sp62Rec.OddConj
import CFSG.ClassicalInvolution.Sp62Rec.I1.PermQuot
import CFSG.ClassicalInvolution.Sp62Rec.I1.TwinCentralizer
import CFSG.ClassicalInvolution.Sp62Rec.I1.AutConj
import CFSG.ClassicalInvolution.Sp62Rec.I1.HatOfData
import CFSG.ClassicalInvolution.Sp62Rec.I1.WeightFour
import CFSG.ClassicalInvolution.Sp62Rec.I1.WIsoHhat
import CFSG.ClassicalInvolution.Q3.Sec13AECoverEven
import CFSG.ClassicalInvolution.Q3.TL4AECoverD
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec.I1

structure MemberLabels {G : Type} [Group G] (Ω : Set (Subgroup G)) (E : Subgroup G)
    (f : ↥E →* Wr 6) : Prop where
  label : ∀ J ∈ Ω, J ≤ E → ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool),
    (J.subgroupOf E).map f = memAt α h b
  surj : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool), ∃ J ∈ Ω, J ≤ E ∧
    (J.subgroupOf E).map f = memAt α h b

theorem MemberLabels.bijOn {G : Type} [Group G] {Ω : Set (Subgroup G)} {E : Subgroup G}
    {f : ↥E →* Wr 6} (H : MemberLabels Ω E f) (hf : Function.Injective f) :
    Set.BijOn (fun J : Subgroup G => (J.subgroupOf E).map f) {J | J ∈ Ω ∧ J ≤ E}
      {M | ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool), M = memAt α h b} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro J ⟨hJ, hJE⟩
    obtain ⟨α, h, b, hb⟩ := H.label J hJ hJE
    exact ⟨α, h, b, hb⟩
  · rintro J₁ ⟨-, hJ₁⟩ J₂ ⟨-, hJ₂⟩ h12
    have h1 : J₁.subgroupOf E = J₂.subgroupOf E := Subgroup.map_injective hf h12
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hJ₁, inf_eq_left.mpr hJ₂] at h2
  · rintro M ⟨α, h, b, rfl⟩
    obtain ⟨J, hJ, hJE, hb⟩ := H.surj α h b
    exact ⟨J, ⟨hJ, hJE⟩, hb⟩

section Action


theorem I1Action.map_member {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}
    {f : ↥E →* Wr 6} {Θ : ↥Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}
    (D : I1Action z e E B f Θ φ) {J : Subgroup G} (hJ : J ≤ E) {M : Subgroup (Wr 6)}
    (hM : (J.subgroupOf E).map f = M) :
    (J.subgroupOf B).map φ = (M.subgroupOf Wsub).map Θ.toMonoidHom := by
  subst hM
  ext w
  constructor
  · rintro ⟨⟨x, hxB⟩, hx, rfl⟩
    have hxJ : x ∈ J := Subgroup.mem_subgroupOf.mp hx
    have hxE : x ∈ E := hJ hxJ
    obtain ⟨hm, h1⟩ := D.φ_f x hxE
    exact ⟨⟨f ⟨x, hxE⟩, hm⟩, Subgroup.mem_subgroupOf.mpr
      ⟨⟨x, hxE⟩, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩, h1.symm⟩
  · rintro ⟨⟨m, hmW⟩, hmM, rfl⟩
    obtain ⟨⟨x, hxE⟩, hx, hxm⟩ := Subgroup.mem_subgroupOf.mp hmM
    have hxJ : x ∈ J := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨hm, h1⟩ := D.φ_f x hxE
    refine ⟨⟨x, D.E_le_B hxE⟩, Subgroup.mem_subgroupOf.mpr hxJ, ?_⟩
    rw [h1]
    exact congrArg Θ (Subtype.ext hxm)

theorem I1Action.map_member_wsub {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}
    {f : ↥E →* Wr 6} {Θ : ↥Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}
    (D : I1Action z e E B f Θ φ) {J : Subgroup G} (hJ : J ≤ E) {M : Subgroup (Wr 6)}
    (hM : (J.subgroupOf E).map f = M) :
    (J.subgroupOf B).map (Θ.symm.toMonoidHom.comp φ) = M.subgroupOf Wsub := by
  rw [← Subgroup.map_map, D.map_member hJ hM, Subgroup.map_map]
  have h : Θ.symm.toMonoidHom.comp Θ.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => Θ.symm_apply_apply x
  rw [h, Subgroup.map_id]

end Action

end CFSG.ClassicalInvolution.Sp62Rec

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Q3.AE.Wr

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot mem_trivialOnQuot_iff)

variable {Y : Type} [Group Y] [Finite Y]

section Members

structure I1Members (R : Subgroup Y) (e : Y) (f : ↥(rLayer (Om R) e) →* Wr 6) : Prop where
  core_label : ∀ J ∈ tqMembers3 (Om R) e, ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool),
    ((TwinADescent.coreAt e J).subgroupOf (rLayer (Om R) e)).map f = memAt α h b
  core_surj : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool), ∃ J ∈ tqMembers3 (Om R) e,
    ((TwinADescent.coreAt e J).subgroupOf (rLayer (Om R) e)).map f = memAt α h b

theorem tightCore_eq_self_of_mem_Om {R J : Subgroup Y} (hJ : J ∈ Om R) : tightCore J = J := by
  obtain ⟨g, rfl⟩ := hJ
  rw [← conjSub_tightCore, tightCore_tightCore]

theorem coreAt_eq_of_le_centralizer {R : Subgroup Y} {c : Y} {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJc : J ≤ Subgroup.centralizer ({c} : Set Y)) : TwinADescent.coreAt c J = J := by
  unfold TwinADescent.coreAt
  rw [inf_of_le_left hJc]
  exact tightCore_eq_self_of_mem_Om hJ

theorem I1Members.label {R : Subgroup Y} {e : Y} {f : ↥(rLayer (Om R) e) →* Wr 6}
    (M : I1Members R e f) {J : Subgroup Y} (hJ : J ∈ Om R) (hJE : J ≤ rLayer (Om R) e) :
    ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool),
      (J.subgroupOf (rLayer (Om R) e)).map f = memAt α h b := by
  have hJc : J ≤ Subgroup.centralizer ({e} : Set Y) := hJE.trans (rLayer_le_centralizer _ _)
  obtain ⟨α, h, b, hb⟩ := M.core_label J (mem_tqMembers3_of_le_centralizer hJ hJc)
  rw [coreAt_eq_of_le_centralizer hJ hJc] at hb
  exact ⟨α, h, b, hb⟩

theorem le_centralizer_of_oddCoreIn_eq_bot {J : Subgroup Y} {e : Y} (hJ : e ∈ trivialOnQuot J)
    (hO : oddCoreIn J = ⊥) : J ≤ Subgroup.centralizer ({e} : Set Y) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := (mem_trivialOnQuot_iff.mp hJ).2 x hx
  rw [hO, Subgroup.mem_bot] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

end Members


section Labels

theorem oddCoreIn_eq_bot_of_mem_Om {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hP : PerpHypS n Y R S t)
    (hodd : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) {J : Subgroup Y} (hJ : J ∈ Om R) :
    oddCoreIn J = ⊥ := by
  obtain ⟨g, rfl⟩ := hJ
  have hz := (Inner.isUniqueInvolution_core (CoreData.of_S hP.core).datum).conj g
  have hsub := isSubnormal_of_hypOmegaGen (CoreData.of_S hP.core).hyp ⟨g, rfl⟩ hz
  have h1 := oddCoreIn_le_of_isSubnormal hsub
  rw [oddCoreIn_centralizer_conj_eq_bot hodd] at h1
  exact le_bot_iff.mp h1

theorem le_rLayer_iff_le_centralizer {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    (hP : PerpHypS n Y R S t) (hsq : e * e = 1) {J : Subgroup Y} (hJ : J ∈ Om R) :
    J ≤ rLayer (Om R) e ↔ J ≤ Subgroup.centralizer ({e} : Set Y) := by
  refine ⟨fun h => h.trans (rLayer_le_centralizer _ _), fun hJc => ?_⟩
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq
  have h1 := TwinDisc.coreAt_le_rLayer (CoreData.of_S hP.core).hyp hc2
    (mem_tqMembers3_of_le_centralizer hJ hJc)
  rwa [coreAt_eq_of_le_centralizer hJ hJc] at h1

theorem I1Members.memberLabels_of_centralizes {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    {f : ↥(rLayer (Om R) e) →* Wr 6} (hP : PerpHypS n Y R S t) (hsq : e * e = 1)
    (hc : ∀ J ∈ tqMembers3 (Om R) e, J ≤ Subgroup.centralizer ({e} : Set Y))
    (M : I1Members R e f) : MemberLabels (Om R) (rLayer (Om R) e) f := by
  refine ⟨fun J hJ hJE => M.label hJ hJE, fun α h b => ?_⟩
  obtain ⟨J, hJ, hb⟩ := M.core_surj α h b
  rw [coreAt_eq_of_le_centralizer hJ.1 (hc J hJ)] at hb
  exact ⟨J, hJ.1, (le_rLayer_iff_le_centralizer hP hsq hJ.1).mpr (hc J hJ), hb⟩

theorem I1Members.memberLabels {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    {f : ↥(rLayer (Om R) e) →* Wr 6} (hP : PerpHypS n Y R S t) (hsq : e * e = 1)
    (hodd : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) (M : I1Members R e f) :
    MemberLabels (Om R) (rLayer (Om R) e) f :=
  M.memberLabels_of_centralizes hP hsq fun J hJ =>
    le_centralizer_of_oddCoreIn_eq_bot hJ.2 (oddCoreIn_eq_bot_of_mem_Om hP hodd hJ.1)

theorem I1Members.bijOn {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    {f : ↥(rLayer (Om R) e) →* Wr 6} (hP : PerpHypS n Y R S t) (hsq : e * e = 1)
    (M : I1Members R e f) (hf : Function.Injective f) :
    Set.BijOn
      (fun J : Subgroup Y => ((TwinADescent.coreAt e J).subgroupOf (rLayer (Om R) e)).map f)
      (tqMembers3 (Om R) e)
      {M | ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool), M = memAt α h b} := by
  have hΩ := (CoreData.of_S hP.core).hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq
  refine ⟨fun J hJ => ?_, fun J hJ J' hJ' h => ?_, fun m hm => ?_⟩
  · obtain ⟨α, h, b, hb⟩ := M.core_label J hJ
    exact ⟨α, h, b, hb⟩
  · have h2 := Subgroup.subgroupOf_inj.mp (Subgroup.map_injective hf h)
    rw [inf_eq_left.mpr (TwinDisc.coreAt_le_rLayer hΩ hc2 hJ),
      inf_eq_left.mpr (TwinDisc.coreAt_le_rLayer hΩ hc2 hJ')] at h2
    exact TwinDisc.eq_of_coreAt_eq hΩ hc2 hJ hJ' h2
  · obtain ⟨α, h, b, rfl⟩ := hm
    obtain ⟨J, hJ, hb⟩ := M.core_surj α h b
    exact ⟨J, hJ, hb⟩


theorem I1Members.exists_map_phi {R : Subgroup Y} {t e : Y} {B : Subgroup Y}
    {f : ↥(rLayer (Om R) e) →* Wr 6} {Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}
    (M : I1Members R e f) (D : I1Action t e (rLayer (Om R) e) B f Θ φ) {J : Subgroup Y}
    (hJ : J ∈ Om R) (hJE : J ≤ rLayer (Om R) e) :
    ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool),
      (J.subgroupOf B).map φ =
        ((memAt α h b).subgroupOf Sp62Rec.I1.Wsub).map Θ.toMonoidHom := by
  obtain ⟨α, h, b, hb⟩ := M.label hJ hJE
  exact ⟨α, h, b, D.map_member hJE hb⟩

variable {Ω : Set (Subgroup Y)} {c : Y}

theorem map_secOf_coreAt
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (J : Subgroup Y) :
    ((TwinADescent.coreAt c J).subgroupOf (rLayer Ω c)).map (secOf hmap) =
      TwinDisc.secImg Ω c J := by
  have hcoe : ∀ h : ↥(coreHull Ω c), ((TwinPerpV3.hullEquiv hmap h : ↥(rLayer Ω c)) : Y) =
      (((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) :=
    fun h => TwinPerpV3.hullEquiv_coe hmap h
  ext s
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(TwinPerpV3.hullEquiv hmap).symm y, ?_, (secOf_apply hmap y).symm⟩
    have h1 := hcoe ((TwinPerpV3.hullEquiv hmap).symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : (y : Y) ∈ TwinADescent.coreAt c J := Subgroup.mem_subgroupOf.mp hy
    show ((((TwinPerpV3.hullEquiv hmap).symm y : ↥(coreHull Ω c)) :
      ↥(Subgroup.centralizer ({c} : Set Y))) : Y) ∈ TwinADescent.coreAt c J
    rw [← h1]
    exact h2
  · rintro ⟨h, hh, rfl⟩
    refine ⟨TwinPerpV3.hullEquiv hmap h, ?_, ?_⟩
    · show (((TwinPerpV3.hullEquiv hmap h : ↥(rLayer Ω c)) : Y)) ∈ TwinADescent.coreAt c J
      rw [hcoe h]
      exact hh
    · rw [secOf_apply, MulEquiv.symm_apply_apply]
      rfl

theorem map_q0_coreAt
    (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set Y)).subtype = rLayer Ω c)
    (q0 : ↥(rLayer Ω c) →* ↥(pSpan (TwinDisc.secFam Ω c)))
    (hq0 : ∀ y : ↥(rLayer Ω c),
      ((q0 y : ↥(pSpan (TwinDisc.secFam Ω c))) :
        ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) = secOf hmap y)
    (J : Subgroup Y) :
    ((TwinADescent.coreAt c J).subgroupOf (rLayer Ω c)).map q0 =
      (TwinDisc.secImg Ω c J).subgroupOf (pSpan (TwinDisc.secFam Ω c)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, hq0, ← map_secOf_coreAt hmap J]
    exact ⟨x, hx, rfl⟩
  · intro hz
    have hz' := Subgroup.mem_subgroupOf.mp hz
    rw [← map_secOf_coreAt hmap J] at hz'
    obtain ⟨x, hx, hxz⟩ := hz'
    exact ⟨x, hx, Subtype.ext ((hq0 x).trans hxz)⟩

end Labels

section Core


theorem i1_action_members {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    (hP : PerpHypS n Y R S t) {Z : Subgroup Y}
    (hAE : SecAE R e 6) (hI : I1In R t e Z)
    (Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat)
    (hΘ : Θ ⟨allOnes 6, Sp62Rec.I1.allOnes_mem_Wsub⟩ = ⟨alpha, alpha_mem_Hhat⟩) :
    ∃ (f : ↥(rLayer (Om R) e) →* Wr 6) (φ : ↥(Z ⊔ rLayer (Om R) e) →* ↥Hhat),
      I1Action t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) f Θ φ ∧ I1Members R e f := by
  classical
  have hsq : e * e = 1 := (hI.Z_elem e hI.e_mem e hI.e_mem).2
  have SD : SecData R e := SecData.of_perp hP hsq
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer SD.hΩ hc2 SD.two
  set E := rLayer (Om R) e with hE
  set B := Z ⊔ E with hB
  have hZC : Z ≤ Subgroup.centralizer ({e} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hI.Z_elem x hx e hI.e_mem).1
  have hEC : E ≤ Subgroup.centralizer ({e} : Set Y) := TwinPerpV3.rLayer_le_centralizer _ _
  have hBC : B ≤ Subgroup.centralizer ({e} : Set Y) := sup_le hZC hEC
  have hEB : E ≤ B := le_sup_right
  have hEn := rLayer_map_conj_eq R e
  rw [← hE] at hEn
  have hEn' : ∀ g ∈ B, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g hg x hx
    have h1 := hEn g (hBC hg)
    have h2 : g * x * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h1] at h2
  have heE : e ∈ E := mem_rLayer_self hI
  obtain ⟨J, J', hJ, hJ', hne, hzJ, hzJ', hcomm⟩ := hI.twin
  set Φ := TwinDisc.secFam (Om R) e with hΦ
  obtain ⟨I⟩ := hAE
  have hH := aeCoverHyp_of_I1 SD I hJ hJ' hne hzJ hzJ'
  have hker : I.φ.ker ≠ ⊥ :=
    ker_ne_bot_of_central SD.q8 I (c := secOf hmap ⟨e, heE⟩) (secOf_central hmap heE)
      (secOf_ne_one hmap heE hsq hI.e_ne_one)
  obtain ⟨-, hbot | ⟨ψ, hψ, hψm⟩⟩ := Sec13.aeCover_ker hH (by norm_num : 5 ≤ 6)
  · exact absurd hbot hker
  have hgen : pSpan Φ = ⊤ := TwinDisc.AE5.hgen_of SD.q8
  have hperfP : Group.IsPerfect ↥(pSpan Φ) :=
    TL4.AECov.isPerfect_pSpan I (by norm_num) hH.card hH.conj_mem hH.label_inj
  haveI := hperfP
  have hperfA : Group.IsPerfect ↥(aeSub 6) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  let eqTop : ↥(pSpan Φ) ≃* SecQ R e := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hperfX : Group.IsPerfect (SecQ R e) :=
    Group.IsPerfect.ofSurjective (f := eqTop.toMonoidHom) eqTop.surjective
  let q0 : ↥E →* ↥(pSpan Φ) := eqTop.symm.toMonoidHom.comp (secOf hmap)
  have hq0 : Function.Surjective q0 := eqTop.symm.surjective.comp (secOf_surjective hmap)
  have hq0coe : ∀ y : ↥E, ((q0 y : ↥(pSpan Φ)) : SecQ R e) = secOf hmap y := fun y => rfl
  let f : ↥E →* Wr 6 := ((aeSub 6).subtype.comp ψ.toMonoidHom).comp q0
  have hfr : f.range = aeSub 6 := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact (ψ (q0 x)).2
    · intro ha
      obtain ⟨y, hy⟩ := ψ.surjective ⟨a, ha⟩
      obtain ⟨x, rfl⟩ := hq0 y
      exact ⟨x, congrArg Subtype.val hy⟩
  have hfk : f.ker = (oddCoreIn E).subgroupOf E := by
    rw [← secOf_ker hmap]
    ext x
    show ((ψ (q0 x) : ↥(aeSub 6)) : Wr 6) = 1 ↔ _
    constructor
    · intro h
      have h1 : ψ (q0 x) = 1 := Subtype.ext h
      have h2 : q0 x = 1 := ψ.injective (h1.trans (map_one ψ).symm)
      have h3 : secOf hmap x = 1 := by
        have := congrArg (fun y : ↥(pSpan Φ) => (y : SecQ R e)) h2
        exact this
      exact h3
    · intro h
      have h3 : secOf hmap x = 1 := h
      have h2 : q0 x = 1 := Subtype.ext h3
      rw [h2, map_one]; rfl
  have hcbarcen : ∀ y : ↥(pSpan Φ), y * q0 ⟨e, heE⟩ = q0 ⟨e, heE⟩ * y := by
    intro y
    apply eqTop.injective
    rw [map_mul, map_mul]
    have h0 : eqTop (q0 ⟨e, heE⟩) = secOf hmap ⟨e, heE⟩ := rfl
    rw [h0]
    exact (secOf_central hmap heE (eqTop y)).symm
  have hcbarker : q0 ⟨e, heE⟩ ∈ I.φ.ker :=
    AEIdent.center_le_ker (by norm_num : 5 ≤ 6) I (Subgroup.mem_center_iff.mpr hcbarcen)
  have hcbar1 : q0 ⟨e, heE⟩ ≠ 1 := fun h =>
    secOf_ne_one hmap heE hsq hI.e_ne_one (congrArg (fun y : ↥(pSpan Φ) => (y : SecQ R e)) h)
  have hfe : f ⟨e, heE⟩ = allOnes 6 := Sp62Rec.I1.psi_eq_allOnes I ψ hψ hcbarker hcbar1
  have hκ : ∀ h ∈ Subgroup.centralizer ({e} : Set Y), ∃ w : Wr 6, ActsOnE f h w := by
    intro h hh
    let g' : ↥(Subgroup.centralizer ({e} : Set Y)) := ⟨h, hh⟩
    let α' : SecQ R e ≃* SecQ R e := TwinExitPf6.secAut (Om R) e SD.hΩ hc2 g'
    have hα'Φ : ∀ L ∈ Φ, L.map α'.toMonoidHom ∈ Φ := fun L hL =>
      TwinExitPf10.secAut_map_secFam SD.hΩ hc2 g' hL
    obtain ⟨αP', hαP', hαPΦ'⟩ := Sp62Rec.I1.exists_restrict_aut hgen α' hα'Φ
    obtain ⟨w, hw⟩ := Sp62Rec.I1.exists_conj_of_aut I hperfP ψ hψ αP' hαPΦ'
    refine ⟨w, fun x hx hx' => ?_⟩
    have h1 : q0 ⟨h * x * h⁻¹, hx'⟩ = αP' (q0 ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [hq0coe, hαP', hq0coe]
      exact secOf_conj SD.hΩ hc2 hmap g' ⟨x, hx⟩ _
    show ((ψ (q0 ⟨h * x * h⁻¹, hx'⟩) : ↥(aeSub 6)) : Wr 6) =
      w * ((ψ (q0 ⟨x, hx⟩) : ↥(aeSub 6)) : Wr 6) * w⁻¹
    rw [h1, hw]
  obtain ⟨ρ, hρ, hρker⟩ := hI.S6
  set N : Subgroup ↥B := E.subgroupOf B with hNdef
  haveI hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff hEB]
    intro h g hh hg
    exact hEn' g hg h hh
  let eEN : ↥N ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEB
  let Zs : Subgroup ↥B := Z.subgroupOf B
  have hZs : ∀ x ∈ Zs, ∀ y ∈ Zs, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext
      (hI.Z_elem _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)).1
  have hsup : Zs ⊔ N = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup (A := Z) (A' := E) (B := B) le_sup_left le_sup_right
    have h2 : ((Z ⊔ E).subgroupOf B) = ⊤ := Subgroup.subgroupOf_self B
    rw [h2] at h1
    exact h1.symm
  have hunit : ∀ u : ℤˣ, Odd (orderOf u) → u = 1 := by
    intro u hu
    rcases Int.units_eq_one_or u with h | h
    · exact h
    · exfalso
      rw [h] at hu
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : orderOf (-1 : ℤˣ) = 2 := orderOf_eq_prime (by decide) (by decide)
      rw [h2] at hu
      exact absurd hu (by decide)
  have hsign : ∀ x ∈ N, Equiv.Perm.sign (ρ x) = 1 := by
    let q : ↥N →* SecQ R e := (secOf hmap).comp eEN.toMonoidHom
    have hq : Function.Surjective q := (secOf_surjective hmap).comp eEN.surjective
    let s : ↥N →* ℤˣ := Equiv.Perm.sign.comp (ρ.comp N.subtype)
    have hs : q.ker ≤ s.ker := by
      intro x hx
      have h1 : eEN x ∈ (secOf hmap).ker := hx
      rw [secOf_ker, Subgroup.mem_subgroupOf] at h1
      have h2 : Odd (orderOf (((x : ↥B) : Y))) :=
        Odd.of_dvd_nat (odd_card_oddCoreIn E) (Subgroup.orderOf_dvd_natCard _ h1)
      have h3 : orderOf x = orderOf (((x : ↥B) : Y)) := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      have h4 : Odd (orderOf (s x)) := Odd.of_dvd_nat (h3 ▸ h2) (orderOf_map_dvd s x)
      exact hunit _ h4
    have := Sp62Rec.I1.hom_eq_one_of_perfect_quotient q hq hperfX s hs
    intro x hx
    exact DFunLike.congr_fun this ⟨x, hx⟩
  obtain ⟨τ', hτ'Zs, hτ'N, hτ'sign, hΓ⟩ :=
    Sp62Rec.I1.exists_odd_mem_of_perm_quotient N Zs hZs hsup ρ hρ hρker hsign
  have hτ'Z : (τ' : Y) ∈ Z := Subgroup.mem_subgroupOf.mp hτ'Zs
  have hτC : (τ' : Y) ∈ Subgroup.centralizer ({e} : Set Y) := hZC hτ'Z
  have hτ2 : (τ' : Y) * (τ' : Y) = 1 := (hI.Z_elem _ hτ'Z _ hτ'Z).2
  let g : ↥(Subgroup.centralizer ({e} : Set Y)) := ⟨(τ' : Y), hτC⟩
  have hg2 : g * g = 1 := Subtype.ext hτ2
  let αX : SecQ R e ≃* SecQ R e := TwinExitPf6.secAut (Om R) e SD.hΩ hc2 g
  have hαΦ : ∀ L ∈ Φ, L.map αX.toMonoidHom ∈ Φ := fun L hL =>
    TwinExitPf10.secAut_map_secFam SD.hΩ hc2 g hL
  have hK := TwinDisc.secImg_mem_secFam hJ
  have hK' := TwinDisc.secImg_mem_secFam hJ'
  obtain ⟨htC, htY, hU⟩ := TwinDisc.isUniqueInvolution_secImg SD.hΩ hc2 hJ hzJ
  obtain ⟨htC', htY', hU'⟩ := TwinDisc.isUniqueInvolution_secImg SD.hΩ hc2 hJ' hzJ'
  have hneK : TwinDisc.secImg (Om R) e J' ≠ TwinDisc.secImg (Om R) e J :=
    (TwinPerpV3.secImg_ne_of_twin SD.hΩ hc2 hJ hJ' hne.symm hzJ hzJ').symm
  have hτt : (τ' : Y) * t = t * (τ' : Y) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hI.Z_le hτ'Z)
  have hαz : αX (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e))) =
      QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e)) := by
    refine TwinExitPf6.secAut_mk SD.hΩ hc2 g _ _ (Subtype.ext ?_)
    show t = (τ' : Y) * t * (τ' : Y)⁻¹
    rw [hτt]; group
  have hodd := secAut_odd_of_twin SD g hJ
    (fun l hl => hcomm (τ' : Y) hτ'Z l (Subgroup.mem_sup_left hl))
  have hodd' := secAut_odd_of_twin SD g hJ'
    (fun l hl => hcomm (τ' : Y) hτ'Z l (Subgroup.mem_sup_right hl))
  have hfix := Sp62Rec.I1.aut_fixes_twins hH hK hK' hneK hU hU' αX hαΦ hαz hodd hodd'
  obtain ⟨αP, hαP, hαPΦ⟩ := Sp62Rec.I1.exists_restrict_aut hgen αX hαΦ
  obtain ⟨w, hw⟩ := Sp62Rec.I1.exists_conj_of_aut I hperfP ψ hψ αP hαPΦ
  have hαX2 : ∀ y : SecQ R e, αX (αX y) = y := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
    haveI hHn := TwinExitPf6.normal_coreHull SD.hΩ hc2
    let h1 : ↥(coreHull (Om R) e) :=
      ⟨g * ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) * g⁻¹,
        hHn.conj_mem _ h.2 g⟩
    have e1 := TwinExitPf6.secAut_mk SD.hΩ hc2 g h h1 rfl
    have e2 := TwinExitPf6.secAut_mk SD.hΩ hc2 g h1 h (by
      show ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) =
        g * (g * ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) * g⁻¹) * g⁻¹
      calc ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y)))
          = (g * g) * ((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) *
              (g * g)⁻¹ := by rw [hg2]; simp
        _ = _ := by group)
    show αX (αX (QuotientGroup.mk' _ h)) = QuotientGroup.mk' _ h
    rw [e1, e2]
  have hαsq : ∀ x : ↥(pSpan Φ), αP (αP x) = x := fun x =>
    Subtype.ext (by rw [hαP, hαP]; exact hαX2 _)
  have hτf : ∀ (x : Y) (hx : x ∈ E),
      f ⟨(τ' : Y) * x * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 x hx⟩ = w * f ⟨x, hx⟩ * w⁻¹ := by
    intro x hx
    have h1 : q0 ⟨(τ' : Y) * x * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 x hx⟩ = αP (q0 ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [hq0coe, hαP, hq0coe]
      exact secOf_conj SD.hΩ hc2 hmap g ⟨x, hx⟩ _
    show ((ψ (q0 ⟨(τ' : Y) * x * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 x hx⟩) : ↥(aeSub 6)) : Wr 6) =
      w * ((ψ (q0 ⟨x, hx⟩) : ↥(aeSub 6)) : Wr 6) * w⁻¹
    rw [h1, hw]
  obtain ⟨β, hβ, b, hlab, hlab'⟩ := Sp62Rec.I1.twin_labels_abs hH hK hK' hneK hU hU'
  have hcommL : ∀ (L : Subgroup (SecQ R e)) (hL : L ∈ Φ), L ≤ TwinDisc.secImg (Om R) e J ⊔
      TwinDisc.secImg (Om R) e J' → ∀ (b' : Bool),
      (L.subgroupOf (pSpan Φ)).map I.φ = memBar β hβ b' → ∀ x ∈ memAt β hβ b', w * x = x * w := by
    intro L hL hLle b' hlabL x hx
    have hx' := hψm L hL β hβ b' hlabL
    rw [← hx'] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := ha
    have hyL : (y : SecQ R e) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hαy : αP y = y := Subtype.ext (by rw [hαP]; exact hfix _ (hLle hyL))
    have h1 := hw y
    rw [hαy] at h1
    show w * (ψ y : Wr 6) = (ψ y : Wr 6) * w
    calc w * (ψ y : Wr 6) = (w * (ψ y : Wr 6) * w⁻¹) * w := by group
      _ = (ψ y : Wr 6) * w := by rw [← h1]
  have hKle : TwinDisc.secImg (Om R) e J ≤ TwinDisc.secImg (Om R) e J ⊔
      TwinDisc.secImg (Om R) e J' := le_sup_left
  have hK'le : TwinDisc.secImg (Om R) e J' ≤ TwinDisc.secImg (Om R) e J ⊔
      TwinDisc.secImg (Om R) e J' := le_sup_right
  have h1 : ∀ x ∈ memAt β hβ true, w * x = x * w := by
    cases b
    · exact hcommL _ hK' hK'le true (by simpa using hlab')
    · exact hcommL _ hK hKle true hlab
  have h2 : ∀ x ∈ memAt β hβ false, w * x = x * w := by
    cases b
    · exact hcommL _ hK hKle false hlab
    · exact hcommL _ hK' hK'le false (by simpa using hlab')
  let f' : ↥N →* Wr 6 := f.comp eEN.toMonoidHom
  have hρN : N.subtype.range.map ρ = alternatingGroup (Fin 6) := by
    rw [Subgroup.range_subtype]
    exact Sp62Rec.I1.map_perm_eq_alternating N Zs hZs hsup ρ hρ hsign
  have hfalt : ∀ s ∈ alternatingGroup (Fin 6), ∃ x : ↥N, (f' x).perm = s := by
    intro s hs
    have hmem : (⟨0, s⟩ : Wr 6) ∈ aeSub 6 :=
      mem_aeSub.2 ⟨by simp [wsum], Equiv.Perm.mem_alternatingGroup.mp hs⟩
    rw [← hfr] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨eEN.symm y, by
      show (f (eEN (eEN.symm y))).perm = s
      rw [MulEquiv.apply_symm_apply, hy]⟩
  have hoddK : ∀ x : ↥N, f' x = 1 → Odd (orderOf x) := by
    intro x hx
    have h1 : eEN x ∈ f.ker := hx
    rw [hfk, Subgroup.mem_subgroupOf] at h1
    have h2 : Odd (orderOf (((x : ↥B) : Y))) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn E) (Subgroup.orderOf_dvd_natCard _ h1)
    have h3 : orderOf x = orderOf (((x : ↥B) : Y)) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [h3]; exact h2
  have hkerρ := Sp62Rec.I1.rho_eq_one_of_perm_eq_one N.subtype ρ hρN f' hoddK
  have hwodd : Equiv.Perm.sign w.perm = -1 :=
    Sp62Rec.I1.sign_perm_eq_neg_one N.subtype ρ hρN f' hfalt hkerρ τ' hτ'sign w
      (fun x => ⟨⟨τ' * (x : ↥B) * τ'⁻¹, hNn.conj_mem x x.2 τ'⟩, rfl⟩)
      (fun x y hxy => by
        have hxy' : ((y : ↥B) : Y) = (τ' : Y) * ((x : ↥B) : Y) * (τ' : Y)⁻¹ :=
          congrArg Subtype.val hxy
        have := hτf ((x : ↥B) : Y) (Subgroup.mem_subgroupOf.mp x.2)
        have e : eEN y = ⟨(τ' : Y) * ((x : ↥B) : Y) * (τ' : Y)⁻¹, hEn' (τ' : Y) τ'.2 _
            (Subgroup.mem_subgroupOf.mp x.2)⟩ := Subtype.ext hxy'
        show f (eEN y) = w * f (eEN x) * w⁻¹
        rw [e]; exact this)
  have hsq' : ∀ x ∈ aeSub 6, (w * w) * x = x * (w * w) := by
    intro x hx
    obtain ⟨y, hy⟩ := ψ.surjective ⟨x, hx⟩
    have h3 := hw (αP y)
    rw [hαsq, hw y, hy] at h3
    have h4 : x = w * (w * x * w⁻¹) * w⁻¹ := h3
    have h7 : (w * (w * x * w⁻¹) * w⁻¹) * (w * w) = (w * w) * x := by group
    rw [← h4] at h7
    exact h7.symm
  obtain ⟨hw2, hws⟩ := Sp62Rec.I1.eq_of_centralizes_twins hβ h1 h2 hwodd hsq'
  have hτE : (τ' : Y) ∉ E := fun h => hτ'N (Subgroup.mem_subgroupOf.mpr h)
  have hB' : ∀ g ∈ B, g ∈ E ∨ g * (τ' : Y)⁻¹ ∈ E := by
    intro g' hg'
    rcases hΓ ⟨g', hg'⟩ with h | h
    · exact Or.inl (Subgroup.mem_subgroupOf.mp h)
    · exact Or.inr (Subgroup.mem_subgroupOf.mp h)
  obtain ⟨φ, hφs, hφk, hφE, hφe, hφf⟩ := Sp62Rec.I1.hat_of_data' Θ hΘ hEB hEn' heE f hfr hfk hfe
    τ'.2 hτ2 hτE hB' hw2 hws hwodd hτf hperfA
  have htE : t ∈ E := hmap ▸ ⟨⟨t, htC⟩, htY, rfl⟩
  have hhull : (TwinPerpV3.hullEquiv hmap).symm ⟨t, htE⟩ =
      (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e)) := by
    apply Subtype.ext
    apply Subtype.ext
    have := TwinPerpV3.hullEquiv_coe hmap ((TwinPerpV3.hullEquiv hmap).symm ⟨t, htE⟩)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have htq : ((q0 ⟨t, htE⟩ : ↥(pSpan Φ)) : SecQ R e) =
      QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e)) := by
    rw [hq0coe, secOf_apply, hhull]
  have htmem : q0 ⟨t, htE⟩ ∈ (TwinDisc.secImg (Om R) e J).subgroupOf (pSpan Φ) :=
    Subgroup.mem_subgroupOf.mpr (htq ▸ hU.mem)
  have htψ : (f ⟨t, htE⟩ : Wr 6) ∈ memAt β hβ b := by
    have h1 : (f ⟨t, htE⟩ : Wr 6) ∈
        (((TwinDisc.secImg (Om R) e J).subgroupOf (pSpan Φ)).map ψ.toMonoidHom).map
          (aeSub 6).subtype :=
      ⟨ψ (q0 ⟨t, htE⟩), ⟨q0 ⟨t, htE⟩, htmem, rfl⟩, rfl⟩
    rw [hψm _ hK β hβ b hlab] at h1
    exact h1
  have htsq : f ⟨t, htE⟩ * f ⟨t, htE⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htE⟩ : ↥E) * ⟨t, htE⟩ = 1 := Subtype.ext hzJ.sq
    rw [this, map_one]
  have htf : f ⟨t, htE⟩ = zOf (emb β hβ) := by
    rcases eq_of_mem_memAt_mul_self htψ htsq with h1 | h1
    · exfalso
      have h2 : q0 ⟨t, htE⟩ = 1 := by
        have h2' : ψ (q0 ⟨t, htE⟩) = 1 := Subtype.ext h1
        exact ψ.injective (h2'.trans (map_one ψ).symm)
      have h3 : ((q0 ⟨t, htE⟩ : ↥(pSpan Φ)) : SecQ R e) = 1 := by rw [h2]; rfl
      rw [htq] at h3
      exact hU.ne_one h3
    · exact h1
  obtain ⟨hm, hφt⟩ := hφf t htE
  have hmz : zOf (emb β hβ) ∈ Sp62Rec.I1.Wsub := htf ▸ hm
  have hxe : (⟨f ⟨t, htE⟩, hm⟩ : ↥Sp62Rec.I1.Wsub) = ⟨zOf (emb β hβ), hmz⟩ := Subtype.ext htf
  have hodd : Odd (Subgroup.centralizer ({φ ⟨t, hEB htE⟩} : Set ↥Hhat)).index := by
    rw [hφt, hxe]
    have hcent : Subgroup.centralizer ({Θ ⟨zOf (emb β hβ), hmz⟩} : Set ↥Hhat) =
        (Subgroup.centralizer ({(⟨zOf (emb β hβ), hmz⟩ : ↥Sp62Rec.I1.Wsub)} :
          Set ↥Sp62Rec.I1.Wsub)).map Θ.toMonoidHom := by
      ext y
      constructor
      · intro hy
        refine ⟨Θ.symm y, SetLike.mem_coe.mpr ?_, by simp⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        apply Θ.injective
        rw [map_mul, map_mul]
        simpa using hy
      · rintro ⟨y', hy', rfl⟩
        have hy'' := SetLike.mem_coe.mp hy'
        rw [Subgroup.mem_centralizer_singleton_iff] at hy'' ⊢
        show Θ y' * Θ ⟨zOf (emb β hβ), hmz⟩ = Θ ⟨zOf (emb β hβ), hmz⟩ * Θ y'
        rw [← map_mul, ← map_mul, hy'']
    have hidx : (Subgroup.map Θ.toMonoidHom (Subgroup.centralizer
        ({(⟨zOf (emb β hβ), hmz⟩ : ↥Sp62Rec.I1.Wsub)} : Set ↥Sp62Rec.I1.Wsub))).index =
        (Subgroup.centralizer ({(⟨zOf (emb β hβ), hmz⟩ : ↥Sp62Rec.I1.Wsub)} :
          Set ↥Sp62Rec.I1.Wsub)).index := Subgroup.index_map_equiv _ Θ
    rw [hcent, hidx]
    exact Sp62Rec.I1.odd_index_centralizer_zOf (emb β hβ) hmz
  have hcoreLab : ∀ J ∈ tqMembers3 (Om R) e,
      ((TwinADescent.coreAt e J).subgroupOf E).map f =
        (((TwinDisc.secImg (Om R) e J).subgroupOf (pSpan Φ)).map ψ.toMonoidHom).map
          (aeSub 6).subtype := by
    intro J hJ
    rw [← map_q0_coreAt hmap q0 hq0coe J, Subgroup.map_map, Subgroup.map_map]
  have hmem : I1Members R e f := by
    refine ⟨fun J hJ => ?_, fun β hβ b => ?_⟩
    · obtain ⟨β, hβ, b, hlab⟩ := I.label _ (TwinDisc.secImg_mem_secFam hJ)
      exact ⟨β, hβ, b, (hcoreLab J hJ).trans
        (hψm _ (TwinDisc.secImg_mem_secFam hJ) β hβ b hlab)⟩
    · obtain ⟨L, hL, hlab⟩ := I.label_surj β hβ b
      obtain ⟨J, hJ, rfl⟩ := TwinDisc.exists_of_mem_secFam hL
      exact ⟨J, hJ, (hcoreLab J hJ).trans (hψm _ hL β hβ b hlab)⟩
  exact ⟨f, φ,
    { E_le_B := hEB, B_le := hBC, E_normal := hEn, e_mem := heE, z_mem := hEB htE,
      f_range := hfr, f_ker := hfk, Θ_pi := hΘ, φ_surj := hφs, φ_ker := hφk, φ_E := hφE,
      φ_e := hφe, φ_odd := hodd, φ_f := hφf, kappa := hκ }, hmem⟩

end Core

section Final


theorem i1_action_members_final {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    (hP : PerpHypS n Y R S t) {Z : Subgroup Y} (hAE : SecAE R e 6) (hI : I1In R t e Z) :
    ∃ (f : ↥(rLayer (Om R) e) →* Wr 6) (Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat)
      (φ : ↥(Z ⊔ rLayer (Om R) e) →* ↥Hhat),
      I1Action t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) f Θ φ ∧ I1Members R e f := by
  obtain ⟨Θ, hΘ⟩ := Sp62Rec.I1.exists_iso_Wsub_Hhat
  obtain ⟨f, φ, D, M⟩ := i1_action_members hP hAE hI Θ hΘ
  exact ⟨f, Θ, φ, D, M⟩

theorem i1_action_memberLabels_final {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t e : Y}
    (hP : PerpHypS n Y R S t) {Z : Subgroup Y} (hAE : SecAE R e 6) (hI : I1In R t e Z)
    (hodd : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    ∃ (f : ↥(rLayer (Om R) e) →* Wr 6) (Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat)
      (φ : ↥(Z ⊔ rLayer (Om R) e) →* ↥Hhat),
      I1Action t e (rLayer (Om R) e) (Z ⊔ rLayer (Om R) e) f Θ φ ∧
        MemberLabels (Om R) (rLayer (Om R) e) f := by
  obtain ⟨f, Θ, φ, D, M⟩ := i1_action_members_final hP hAE hI
  exact ⟨f, Θ, φ, D, M.memberLabels hP (hI.Z_elem e hI.e_mem e hI.e_mem).2 hodd⟩

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
