module

public import CFSG.LargeExtraspecial.S6TwoC
public import CFSG.LargeExtraspecial.S6ThreeG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Sub

variable (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {X Y : Submodule (ZMod 2) S.Qt}
  (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
  (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y)
  {R' : Subgroup S.O} (hR' : R' ≤ Rbar S g t)
  (hN : ∀ x ∈ R' ⊓ Nbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ X)
  {Z : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
  (hZ : ((resV haQ t).comp (Subgroup.inclusion hR')).range = Z)

variable (S g) in
@[expose] noncomputable def secRepSub (t : S.O) (X Y : Submodule (ZMod 2) S.Qt)
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X)
    (hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y)
    {R' : Subgroup S.O} (hR' : R' ≤ Rbar S g t)
    (hN : ∀ x ∈ R' ⊓ Nbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ X)
    {Z : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hZ : ((resV haQ t).comp (Subgroup.inclusion hR')).range = Z) :
    Z →* (↥(Y.map X.mkQ) ≃ₗ[ZMod 2] ↥(Y.map X.mkQ)) :=
  (descend ((resV haQ t).comp (Subgroup.inclusion hR'))
    ((secHom S g t X Y hX hY).comp (Subgroup.inclusion hR')) (by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, resV_eq_one_iff, Subgroup.coe_inclusion] at hx
      rw [MonoidHom.mem_ker]
      ext ⟨m, hm⟩
      obtain ⟨w, hw, rfl⟩ := hm
      change X.mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = X.mkQ w
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hN _ (Subgroup.mem_inf.mpr ⟨x.2, hx⟩) w hw)).comp
    (MulEquiv.subgroupCongr hZ.symm).toMonoidHom

theorem secRepSub_apply {e : Z} {x : S.O} (hx : x ∈ R')
    (hex : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t ⟨x, hR' hx⟩) {w : S.Qt}
    (hw : w ∈ Y) :
    ((secRepSub S g haQ t X Y hX hY hR' hN hZ e (secMk X hw) : ↥(Y.map X.mkQ)) :
        S.Qt ⧸ X) = X.mkQ ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
  unfold secRepSub
  rw [MonoidHom.comp_apply, descend_apply' _ _ _
    (e := (MulEquiv.subgroupCongr hZ.symm).toMonoidHom e) (k := ⟨x, hx⟩) hex]
  rfl

theorem mem_fixOf_secRepSub_iff {T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} {K : Set S.O}
    (hKR : K ⊆ R')
    (hT : ∀ e ∈ Z, e ∈ T ↔ ∃ x, ∃ hx : x ∈ K, e = resV haQ t ⟨x, hR' (hKR hx)⟩)
    {w : S.Qt} (hw : w ∈ Y) :
    secMk X hw ∈ S2.fixOf (secRepSub S g haQ t X Y hX hY hR' hN hZ) T ↔
      ∀ x ∈ K, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X := by
  rw [S2.mem_fixOf]
  constructor
  · intro hfix x hx
    have he : resV haQ t ⟨x, hR' (hKR hx)⟩ ∈ Z := by
      rw [← hZ]
      exact ⟨⟨x, hKR hx⟩, rfl⟩
    have h1 := hfix ⟨_, he⟩ ((hT _ he).mpr ⟨x, hx, rfl⟩)
    have h2 := congrArg (fun m : ↥(Y.map X.mkQ) => (m : S.Qt ⧸ X)) h1
    rw [secRepSub_apply haQ hX hY hR' hN hZ (hKR hx) rfl hw, coe_secMk, Submodule.mkQ_apply,
      Submodule.mkQ_apply, Submodule.Quotient.eq] at h2
    exact h2
  · intro hK e he
    obtain ⟨x, hx, hex⟩ := (hT e e.2).mp he
    apply Subtype.ext
    rw [secRepSub_apply haQ hX hY hR' hN hZ (hKR hx) hex hw, coe_secMk, Submodule.mkQ_apply,
      Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hK x hx

end Sub

omit [Finite G] in
theorem isCompl_of_eq {α : Type*} [Lattice α] [BoundedOrder α] {A B A' B' : α} (hA : A = A')
    (hB : B = B') (h : IsCompl A' B') : IsCompl A B := by
  subst hA hB
  exact h

section FixAB

variable (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
  (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) (hPI : PairInt S g t)
include H hNo C ht ht1 hVQ hh hb hPI

theorem forall_apply_sub_mem_Vt_iff_a {w : S.Qt} (hw : w ∈ Wt S g t) :
    (∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ↔
      w ∈ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t := by
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    omega
  obtain ⟨y, hyL, hyb⟩ := exists_L0_not_mem_Qa H C ht ht1 hVQ h3 hh hb
  have hyhR : S.ρ (y * h) ∈ Rbar S g t := by
    rw [map_mul]; exact mul_mem (Lbar_le_Rbar ht (ρ_mem_Lbar S hyL)) hh
  have hP := hPI h (y * h) hh hyhR (by simpa [mul_assoc] using hyb)
  simp only [Subgroup.coe_mul, mul_assoc] at hP
  exact forall_apply_sub_mem_Vt_iff H C ht ht1 hVQ hh hyL hyb hP hw

theorem forall_apply_sub_mem_Vt_iff_b {w : S.Qt} (hw : w ∈ Wt S g t) :
    (∀ l ∈ S.Lbar ((h : G) * g), (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ↔
      w ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t := by
  have hth := mem_Lbar_of_pair H ht hh
  have hVQ₁ := not_V_le_Qa_mul H hVQ hh
  have hh₁ : S.ρ h⁻¹ ∈ Rbar S ((h : G) * g) t := ρ_inv_mem_Rbar hh
  have hab : g * S.z * g⁻¹ ≠ (h : G) * g * S.z * ((h : G) * g)⁻¹ := fun e =>
    hb (e ▸ S.conj_z_mem_Qa g)
  have hb₁ : ((h⁻¹ : S.M) : G) * ((h : G) * g) * S.z * (((h⁻¹ : S.M) : G) * ((h : G) * g))⁻¹ ∉
      S.Qa ((h : G) * g) := by
    rw [inv_mul_coe]
    exact fun hmem => hb (S.mem_Qa_symm hab hmem)
  have h3' : 3 ≤ finrank (ZMod 2) (Vt S ((h : G) * g) t) := by
    rw [Vt_mul]
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    omega
  obtain ⟨y, hyL, hyb⟩ := exists_L0_not_mem_Qa (H.mul h) (C.mul h) hth ht1 hVQ₁ h3' hh₁ hb₁
  have hw₁ : w ∈ Wt S ((h : G) * g) t := by rwa [Wt_mul]
  have hyR : S.ρ y ∈ Rbar S g t := by
    have := Lbar_le_Rbar hth (ρ_mem_Lbar S hyL)
    rwa [Rbar_mul] at this
  have hP := hPI 1 y (by rw [map_one]; exact one_mem _) hyR (by
    have := hyb
    rw [inv_mul_coe] at this
    simpa using this)
  have hP' : S.clSub (S.QG ⊓ S.Qa (((h⁻¹ : S.M) : G) * ((h : G) * g))) ⊓
      S.clSub (S.QG ⊓ S.Qa ((y : G) * (((h⁻¹ : S.M) : G) * ((h : G) * g)))) ≤
        Vt S ((h : G) * g) t := by
    rw [inv_mul_coe, Vt_mul]
    simpa using hP
  have key := forall_apply_sub_mem_Vt_iff (H.mul h) (C.mul h) hth ht1 hVQ₁ hh₁ hyL hyb hP' hw₁
  rwa [Wt_mul, Vt_mul] at key

end FixAB

section A6

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hA : A6Case H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H C ht ht1 hVQ hA hh hb

omit hCE in
theorem clSub_inf_clSub_le_Vt_a6 :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t :=
  clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb
    (radBound_of_tau_not_mem H C ht ht1 hVQ hA.tau_not_mem)

theorem timmesfeld_6_2_one :
    W S g t = (S.Qa g ⊓ W S g t) ⊔ (S.Qa ((h : G) * g) ⊓ W S g t) ∧
      ∀ x ∈ R0bar S g h ⊓ Nbar S g t, ∀ w ∈ Wt S g t,
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  refine ⟨?_, fun x hx w hw => R0bar_inf_Nbar_apply_sub_mem_Vt H C ht ht1 hVQ hA hh hb hCE hx hw⟩
  have hdec := sup_eq_Wt H C ht ht1 hVQ hh hb (clSub_inf_clSub_le_Vt_a6 H C ht ht1 hVQ hA hh hb)
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right inf_le_right)
  have hxQ : x ∈ S.QG := hx.1
  have hxW : S.cl x ∈ Wt S g t := clSub_W (S := S) ▸ S.cl_mem_clSub hx hxQ
  rw [← hdec] at hxW
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxW
  obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hu.1
  obtain ⟨y', hy', hy'Q, rfl⟩ := S.mem_clSub_iff.mp hv.1
  have hyW : y ∈ W S g t := by rw [W_eq_clPre]; exact ⟨hyQ, hu.2⟩
  have hy'W : y' ∈ W S g t := by rw [W_eq_clPre]; exact ⟨hy'Q, hv.2⟩
  have hzW : S.z ∈ W S g t := by rw [W_eq_clPre]; exact S.z_mem_clPre _
  have hmem : y * y' ∈ (S.Qa g ⊓ W S g t) ⊔ (S.Qa ((h : G) * g) ⊓ W S g t) :=
    mul_mem (mem_sup_left ⟨hy.2, hyW⟩) (mem_sup_right ⟨hy'.2, hy'W⟩)
  rw [← S.cl_mul hyQ hy'Q] at huv
  rcases (S.cl_eq_cl_iff (S.QG.mul_mem hyQ hy'Q) hxQ).mp huv with rfl | rfl
  · exact hmem
  · exact mul_mem hmem (mem_sup_left ⟨S.z_mem_Qa H.conj_mem H.conj_ne, hzW⟩)

include hNo in
theorem timmesfeld_6_2_two :
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S g t)) (hQ : Q.polarBilin.Nondegenerate),
      Q.polarBilin = beta H C ht ht1 hVQ ∧ Q (aV ht) = 0 ∧
      Q (bV (mem_Lbar_of_pair H ht hh)) = 0 ∧
      (∀ T : Submodule (ZMod 2) (Vt S g t), (∀ x ∈ T, Q x = 0) → finrank (ZMod 2) T < 2) ∧
      LmodN S g t = pointRadical Q (aV ht) ∧
      LhmodN S g t h = pointRadical Q (bV (mem_Lbar_of_pair H ht hh)) ∧
      ((R0bar S g h).subgroupOf (Rbar S g t)).map (resV H.conj_mem t) = omegaGroup Q hQ ∧
      ∃ ρ : omegaGroup Q hQ →*
          (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2] ↥((Wt S g t).map (Vt S g t).mkQ)),
        (∀ (e : omegaGroup Q hQ) {x : S.O} (hx : x ∈ R0bar S g h),
          (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
            resV H.conj_mem t ⟨x, sup_le (Lbar_le_Rbar ht)
              (Lbar_mul_le_Rbar (mem_Lbar_of_pair H ht hh)) hx⟩ →
          ∀ w (hw : w ∈ Wt S g t), ((ρ e (secMk (Vt S g t) hw) :
            ↥((Wt S g t).map (Vt S g t).mkQ)) : S.Qt ⧸ Vt S g t) =
              (Vt S g t).mkQ ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) ∧
        S2.RadDecomp ρ ⊥ ⊤ (aV ht) (bV (mem_Lbar_of_pair H ht hh)) ∧
        4 ∣ finrank (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) := by
  obtain ⟨Q, hQ, hpolβ, hQa, hQb, ⟨u, hau, hbu, hQu⟩, hEa, hEb, hR0⟩ :=
    exists_minus_form_a6 H C ht ht1 hVQ hA hh hb
  have hth := mem_Lbar_of_pair H ht hh
  have haQ := H.conj_mem
  have hR0R : R0bar S g h ≤ Rbar S g t := sup_le (Lbar_le_Rbar ht) (Lbar_mul_le_Rbar hth)
  have hpol : ∀ x y, polar Q x y = beta H C ht ht1 hVQ x y := fun x y => by
    rw [← polarBilin_apply_apply, hpolβ]
  set β := beta H C ht ht1 hVQ with hβdef
  have hβa : β.IsAlt := beta_isAlt H C ht ht1 hVQ
  have hab : β (aV ht) (bV hth) = 1 := beta_aV_bV H C ht ht1 hVQ hh hb
  have hsing : ∀ d, β (aV ht) d = 0 → Q d = 0 → d ∈ (ZMod 2) ∙ aV ht := by
    intro d hd hQd
    by_contra hdn
    apply hA.no_typeA d hd hdn
    have h1 := eichler_mem_pointRadical (q := Q) hQa (u := d) (by rw [hpol]; exact hd)
    rw [eichler_eq_spRho hpol hβa hQa hd, hQd, ← hEa] at h1
    exact h1
  have hmin : ∀ T : Submodule (ZMod 2) (Vt S g t), (∀ x ∈ T, Q x = 0) →
      finrank (ZMod 2) T < 2 := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set K := T ⊓ LinearMap.ker (β (aV ht)) with hK
    have hKa : K ≤ (ZMod 2) ∙ aV ht := fun d hd => hsing d hd.2 (hT d hd.1)
    have hker : finrank (ZMod 2) (LinearMap.ker (β (aV ht))) = 3 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (β (aV ht))
      have h2 : finrank (ZMod 2) (LinearMap.range (β (aV ht))) = 1 := by
        have hle := Submodule.finrank_le (LinearMap.range (β (aV ht)))
        rw [Module.finrank_self] at hle
        have hne : finrank (ZMod 2) (LinearMap.range (β (aV ht))) ≠ 0 := by
          intro h0
          have hmem : β (aV ht) (bV hth) ∈ LinearMap.range (β (aV ht)) := ⟨_, rfl⟩
          rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot, hab] at hmem
          exact one_ne_zero hmem
        omega
      rw [h2, hA.finrank_eq] at h1
      omega
    have hs := Submodule.finrank_sup_add_finrank_inf_eq T (LinearMap.ker (β (aV ht)))
    have hsup := Submodule.finrank_le (T ⊔ LinearMap.ker (β (aV ht)))
    rw [hA.finrank_eq] at hsup
    have hK0 : K ≠ ⊥ := by
      intro h0
      rw [← hK, h0, finrank_bot] at hs
      omega
    obtain ⟨d, hdK, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
    have haT : aV ht ∈ T := by
      rcases mem_span_cl_iff.mp (hKa hdK) with h0 | rfl
      · exact absurd h0 hd0
      · exact hdK.1
    have hTker : T ≤ LinearMap.ker (β (aV ht)) := by
      intro x hx
      rw [LinearMap.mem_ker, ← hpol, polar, hT _ (add_mem haT hx), hT _ haT, hT _ hx, sub_zero,
        sub_zero]
    have hKT : K = T := inf_eq_left.mpr hTker
    have h1 := Submodule.finrank_mono hKa
    rw [finrank_span_singleton (aV_ne_zero H ht), hKT] at h1
    omega
  have hZ : ((resV haQ t).comp (Subgroup.inclusion hR0R)).range = omegaGroup Q hQ := by
    rw [← MonoidHom.map_range, Subgroup.inclusion_range, hR0]
  have hX : ∀ x ∈ Rbar S g t, ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t :=
    fun x hx v hv => apply_mem_Vt_of_mem_Rbar haQ hx hv
  have hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wt S g t :=
    fun x hx v hv => apply_mem_Wt H hx hv
  have hN : ∀ x ∈ R0bar S g h ⊓ Nbar S g t, ∀ v ∈ Wt S g t,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t :=
    fun x hx v hv => R0bar_inf_Nbar_apply_sub_mem_Vt H C ht ht1 hVQ hA hh hb hCE hx hv
  refine ⟨Q, hQ, hpolβ, hQa, hQb, hmin, hEa, hEb, hR0,
    secRepSub S g haQ t (Vt S g t) (Wt S g t) hX hY hR0R hN hZ,
    fun e x hx hex w hw => secRepSub_apply haQ hX hY hR0R hN hZ hx hex hw, ?_⟩
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ hA.tau_not_mem
  have hPI := pairInt_of_radBound H C ht ht1 hVQ hR
  have hP := clSub_inf_clSub_le_Vt_a6 H C ht ht1 hVQ hA hh hb
  have hfa : S2.fixOf (secRepSub S g haQ t (Vt S g t) (Wt S g t) hX hY hR0R hN hZ)
      (pointRadical Q (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      (((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t).map (Vt S g t).mkQ).comap
        ((Wt S g t).map (Vt S g t).mkQ).subtype := by
    refine eq_comap_map_of_iff le_sup_right fun w hw => ?_
    rw [mem_fixOf_secRepSub_iff haQ hX hY hR0R hN hZ (K := (S.Lbar g : Set S.O))
      (fun x hx => mem_sup_left hx) (fun e he => ?_) hw]
    · exact forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hw
    · rw [SetLike.mem_coe, ← hEa, ← map_subgroupOf_resV haQ ht]
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, hl, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨_, hl, rfl⟩
  have hfb : S2.fixOf (secRepSub S g haQ t (Vt S g t) (Wt S g t) hX hY hR0R hN hZ)
      (pointRadical Q (bV hth) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      (((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t).map (Vt S g t).mkQ).comap
        ((Wt S g t).map (Vt S g t).mkQ).subtype := by
    refine eq_comap_map_of_iff le_sup_right fun w hw => ?_
    rw [mem_fixOf_secRepSub_iff haQ hX hY hR0R hN hZ (K := (S.Lbar ((h : G) * g) : Set S.O))
      (fun x hx => mem_sup_right hx) (fun e he => ?_) hw]
    · exact forall_apply_sub_mem_Vt_iff_b H hNo C ht ht1 hVQ hh hb hPI hw
    · rw [SetLike.mem_coe, ← hEb]
      constructor
      · rintro ⟨x, hx, hex⟩
        exact ⟨x, hx, LinearEquiv.ext fun v =>
          Subtype.ext ((hex v).trans
            (coe_resV_apply haQ ⟨x, hR0R (mem_sup_right hx)⟩ v).symm)⟩
      · rintro ⟨x, hx, rfl⟩
        exact resV_mem_LhmodN haQ hth hx
  have hdec := sup_eq_Wt H C ht ht1 hVQ hh hb hP
  have hsup : ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) ⊔
      ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) = Wt S g t := by
    refine le_antisymm (sup_le (sup_le inf_le_right (Vt_le_Wt H ht1))
      (sup_le inf_le_right (Vt_le_Wt H ht1))) ?_
    conv_lhs => rw [← hdec]
    exact sup_le_sup le_sup_left le_sup_left
  have hc := isCompl_comap_map le_sup_right hsup (sup_Vt_inf_sup_Vt H C ht ht1 hVQ hh hb hP)
  have hc' := isCompl_of_eq hfa hfb hc
  refine ⟨radDecomp_bot_of_isCompl hc', ?_⟩
  have h4 := S2.timmesfeld_2_1_b_dvd_minus_omega
    (secRepSub S g haQ t (Vt S g t) (Wt S g t) hX hY hR0R hN hZ) (m := 2) le_rfl
    (by rw [hA.finrank_eq]) hmin (aV_ne_zero H ht) hQa hQb (by rw [hpol]; exact hab) hc'
  simpa using h4

include hNo in
theorem timmesfeld_6_2_two_dvd : 4 ∣ finrank (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h4⟩ :=
    timmesfeld_6_2_two hCE H hNo C ht ht1 hVQ hA hh hb
  exact h4

end A6

end CFSG.LargeExtraspecial.S6
