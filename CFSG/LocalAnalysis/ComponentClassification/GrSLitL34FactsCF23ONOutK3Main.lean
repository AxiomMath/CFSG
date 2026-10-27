module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Twist
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK2Twist
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutInput
public import CFSG.Sporadic.ONOddCore.FullGroup
public import CFSG.Sporadic.ONOddCore.CertifiedSimple

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG Subgroup CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.Sporadic.Schreier (fixSub)

@[expose] def CentA5 (X : Type) [Group X] (z : X) : Prop :=
  ∃ F : Subgroup X, F ≤ centralizer ({z} : Set X) ∧ z ∉ F ∧
    centralizer ({z} : Set X) = zpowers z ⊔ F ∧ Nonempty (F ≃* alternatingGroup (Fin 5))

theorem centA5_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {z : X}
    (h : CentA5 Y (e z)) : CentA5 X z := by
  obtain ⟨F, hFC, hzF, hC, ⟨iso⟩⟩ := h
  have hcent : (centralizer ({e z} : Set Y)).map e.symm.toMonoidHom =
      centralizer ({z} : Set X) := by
    rw [centralizer_map_equiv e.symm (e z), MulEquiv.symm_apply_apply]
  refine ⟨F.map e.symm.toMonoidHom, ?_, ?_, ?_,
    ⟨(F.equivMapOfInjective _ e.symm.injective).symm.trans iso⟩⟩
  · rw [← hcent]
    exact Subgroup.map_mono hFC
  · rintro ⟨y, hy, hyz⟩
    apply hzF
    have hy' : y = e z := by
      rw [← hyz]
      simp
    rwa [← hy']
  · rw [← hcent, hC, Subgroup.map_sup, MonoidHom.map_zpowers]
    simp

theorem map_fixSub {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {α : MulAut H}
    {α' : MulAut H'} (hc : ∀ x, e (α x) = α' (e x)) :
    (fixSub α).map e.toMonoidHom = fixSub α' := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    show α' (e x) = e x
    rw [← hc, hx']
  · intro hy
    have hy' : α' y = y := hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    show α (e.symm y) = e.symm y
    apply e.injective
    rw [hc, MulEquiv.apply_symm_apply, hy']

@[expose] def fixEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {α : MulAut H}
    {α' : MulAut H'} (hc : ∀ x, e (α x) = α' (e x)) : fixSub α ≃* fixSub α' :=
  ((fixSub α).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_fixSub e hc))

theorem centA5_transport {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {α : MulAut H}
    {α' : MulAut H'} (hc : ∀ x, e (α x) = α' (e x)) (z : fixSub α) (z' : fixSub α')
    (hz : e z = z') (h : CentA5 (fixSub α') z') : CentA5 (fixSub α) z := by
  apply centA5_of_mulEquiv (fixEquiv e hc)
  have hz' : fixEquiv e hc z = z' := Subtype.ext hz
  rw [hz']
  exact h

@[expose] def transAut {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (α : MulAut H) :
    MulAut H' :=
  e.symm.trans (α.trans e)

theorem transAut_apply {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (α : MulAut H)
    (y : H') : transAut e α y = e (α (e.symm y)) := rfl

theorem transAut_comm {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (α : MulAut H)
    (x : H) : e (α x) = transAut e α (e x) := by
  rw [transAut_apply, MulEquiv.symm_apply_apply]

theorem transAut_sq {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {α : MulAut H}
    (h : α * α = 1) : transAut e α * transAut e α = 1 := by
  ext y
  have h1 : α (α (e.symm y)) = e.symm y := by
    rw [← MulAut.mul_apply, h, MulAut.one_apply]
  rw [MulAut.mul_apply, transAut_apply, transAut_apply, MulEquiv.symm_apply_apply, h1,
    MulEquiv.apply_symm_apply, MulAut.one_apply]

theorem transAut_not_inner {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {α : MulAut H}
    (h : α ∉ (MulAut.conj : H →* MulAut H).range) :
    transAut e α ∉ (MulAut.conj : H' →* MulAut H').range := by
  rintro ⟨p, hp⟩
  apply h
  refine ⟨e.symm p, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun φ : MulAut H' => φ (e x)) hp
  simp only [MulAut.conj_apply, transAut_apply, MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem isSimpleGroup_Pv :
    IsSimpleGroup Pv :=
  @MulEquiv.isSimpleGroup _ _ _ _ fam_on_certified_simplicity.2 onEquivPv.symm

theorem eq_one_of_conj_eq_one
    {p : Pv} (h : MulAut.conj p = 1) : p = 1 := by
  have := isSimpleGroup_Pv
  have hc : p ∈ Subgroup.center Pv := Subgroup.mem_center_iff.2 fun g => by
    have hg := congrArg (fun φ : MulAut Pv => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    calc g * p = p * g * p⁻¹ * p := by rw [hg]
      _ = p * g := by group
  rw [center_eq_bot_of_simple' pv_not_comm, Subgroup.mem_bot] at hc
  exact hc

theorem mulAut_mul_conj {G : Type*} [Group G] (σ : MulAut G) (m : G) :
    σ * MulAut.conj m = MulAut.conj (σ m) * σ := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem sigma_conj
    (m : Pv) :
    sigmaPv * MulAut.conj m = MulAut.conj (sigmaPv m) * sigmaPv :=
  mulAut_mul_conj sigmaPv m

theorem centA5_sigma : CentA5 (fixSub sigmaPv) ⟨zP, sigmaPv_zP⟩ := by
  have hF0fix : F0 ≤ fixSub sigmaPv := fun x hx => F0_fix x hx
  have hFC : F0.subgroupOf (fixSub sigmaPv) ≤
      centralizer ({⟨zP, sigmaPv_zP⟩} : Set (fixSub sigmaPv)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (F0_le_CM hx))
  refine ⟨F0.subgroupOf (fixSub sigmaPv), hFC, ?_, ?_,
    ⟨(Subgroup.subgroupOfEquivOfLe hF0fix).trans nonempty_F0_equiv.some⟩⟩
  · intro h
    rw [Subgroup.mem_subgroupOf] at h
    exact zP_not_mem_F0 h
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      have hxM : (x : Pv) ∈ CM :=
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hx)
      have hxσ : sigmaPv (x : Pv) = x := x.2
      rcases cent_mem hxM hxσ with h | h
      · exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 h)
      · have hx' : x = ⟨zP, sigmaPv_zP⟩ * ((⟨zP, sigmaPv_zP⟩ : fixSub sigmaPv)⁻¹ * x) := by
          group
        rw [hx']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 h))
    · refine sup_le ?_ hFC
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem centA5_of_fix_z {γ : MulAut Pv} (hγo : γ ∉ (MulAut.conj : Pv →* MulAut Pv).range)
    (hγ2 : γ * γ = 1) (hγz : γ zP = zP) : CentA5 (fixSub γ) ⟨zP, hγz⟩ := by
  obtain ⟨m, hmz, hγm⟩ := outer_fix_eq hγo hγz
  have hmm : m * sigmaPv m = 1 := by
    apply eq_one_of_conj_eq_one
    have e : γ * γ = MulAut.conj (m * sigmaPv m) := by
      rw [hγm, mul_assoc, ← mul_assoc sigmaPv, sigma_conj, mul_assoc, sigmaPv_sq, mul_one,
        ← map_mul]
    rw [← e, hγ2]
  obtain ⟨k, hkM, hmk⟩ := exists_twist (Subgroup.mem_centralizer_singleton_iff.2 hmz) hmm
  have hc : ∀ y, MulAut.conj k⁻¹ (γ y) = sigmaPv (MulAut.conj k⁻¹ y) := by
    intro y
    rw [hγm, hmk, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    simp only [map_mul, map_inv, inv_inv]
    group
  have hkz : MulAut.conj k⁻¹ zP = zP := by
    have hk := Subgroup.mem_centralizer_singleton_iff.1 hkM
    rw [MulAut.conj_apply]
    calc k⁻¹ * zP * k⁻¹⁻¹ = k⁻¹ * (zP * k) := by group
      _ = k⁻¹ * (k * zP) := by rw [hk]
      _ = zP := by group
  exact centA5_transport (MulAut.conj k⁻¹) hc ⟨zP, hγz⟩ ⟨zP, sigmaPv_zP⟩ hkz centA5_sigma

theorem centA5_of_inv {β : MulAut Pv} (hβo : β ∉ (MulAut.conj : Pv →* MulAut Pv).range)
    (hβ2 : β * β = 1) (w : fixSub β) (hw : orderOf w = 2) : CentA5 (fixSub β) w := by
  have hwo : orderOf (((w : Pv) : Equiv.Perm (Fin N))) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  obtain ⟨g, hg, hgw⟩ := cti_on_all_involutions_conjugate _ (w : Pv).2 hwo
  have hgw' : (w : Pv) = ⟨g, hg⟩ * zP * (⟨g, hg⟩ : Pv)⁻¹ := Subtype.ext hgw
  have hw' : MulAut.conj (⟨g, hg⟩ : Pv)⁻¹ (w : Pv) = zP := by
    rw [hgw', MulAut.conj_apply]
    group
  have hβw : β (w : Pv) = w := w.2
  have hγz : transAut (MulAut.conj (⟨g, hg⟩ : Pv)⁻¹) β zP = zP := by
    rw [← hw', ← transAut_comm, hβw]
  exact centA5_transport (MulAut.conj (⟨g, hg⟩ : Pv)⁻¹) (transAut_comm _ β) w ⟨zP, hγz⟩ hw'
    (centA5_of_fix_z (transAut_not_inner _ hβo) (transAut_sq _ hβ2) hγz)

theorem onOuterLocalInput_holds : ONOuterLocalInput := by
  intro G _ hG α hα2 hαo z hz
  obtain ⟨ψ⟩ := hG
  have hwfix : (ψ.trans onEquivPv) (z : G) ∈ fixSub (transAut (ψ.trans onEquivPv) α) := by
    have hz' : α z = z := z.2
    show transAut (ψ.trans onEquivPv) α ((ψ.trans onEquivPv) z) = (ψ.trans onEquivPv) z
    rw [← transAut_comm, hz']
  have hw : orderOf (⟨_, hwfix⟩ : fixSub (transAut (ψ.trans onEquivPv) α)) = 2 := by
    rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hz]
  exact centA5_transport (ψ.trans onEquivPv) (transAut_comm _ α) z ⟨_, hwfix⟩ rfl
    (centA5_of_inv (transAut_not_inner _ hαo) (transAut_sq _ hα2) _ hw)

end CFSG.ComponentClassification.SolMax.ONOut
