module

public import CFSG.LargeExtraspecial.S9Cent
public import CFSG.LargeExtraspecial.S9FourC
public import CFSG.LargeExtraspecial.S9FusB
public import CFSG.LargeExtraspecial.S9ModB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem apply_eq_of_commSpace_le {x : S.O} {X : Submodule (ZMod 2) S.Qt}
    (hx : commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ X) {w : S.Qt}
    (hw : ∀ v ∈ X, polar S.q v w = 0) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  rw [← sub_eq_zero]
  refine S.q_nondegenerate.1 _ fun v => ?_
  rw [polarBilin_apply_apply]
  set y := ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v with hy
  have hv : v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y := (apply_inv_apply_O x v).symm
  have h1 := hw _ (hx (sub_mem_commSpace _ y))
  rw [hv, polar_sub_left, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2]
  rw [polar_comm, polar_sub_right] at h1
  rw [sub_eq_zero.mp h1, sub_self]

theorem add_mem_of_not_mem_hyperplane {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {H U : Submodule (ZMod 2) V} (hHU : H ≤ U)
    (hdim : finrank (ZMod 2) H + 1 = finrank (ZMod 2) U) {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (hxH : x ∉ H) (hyH : y ∉ H) : x + y ∈ H := by
  have hsup : H ⊔ (ZMod 2) ∙ x = U := by
    refine Submodule.eq_of_le_of_finrank_le
      (sup_le hHU ((Submodule.span_singleton_le_iff_mem _ _).mpr hx)) ?_
    have hlt : H < H ⊔ (ZMod 2) ∙ x := lt_of_le_of_ne le_sup_left fun h =>
      hxH (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  rw [← hsup] at hy
  obtain ⟨h', hh', z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, add_zero] at hyH
    exact absurd hh' hyH
  · rw [one_smul, add_comm h' x, ← add_assoc, vec_add_self, zero_add]
    exact hh'

section Five

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem apply_sub_mem_Vone_of_center_clSub {n : S.O} (hnN : n ∈ Nbar S g t)
    (hnc : ∀ x ∈ Nbar S g t, n * x = x * n) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) {p : S.Qt}
    (hp : p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g))) :
    (n : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ Vone S g t g ((h : G) * g) := by
  have haQ := H.conj_mem
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have hkQ := conj_mem_QG' S k.2 haQ
  have hkz := conj_ne_z' S k.2 H.conj_ne
  have hcV := cl_mem_Vt htk
  obtain ⟨j, hj, hjk, -⟩ := exists_common_partner H C ht ht1 hVQ hSp hk hk
  have hfix := clSub_inf_Vone_eq hCE H hNo C ht ht1 hVQ hSp hk hj hjk
  rw [Vone_pair_eq hCE H hNo C ht ht1 hVQ hSp hh hb hk hj hjk] at hfix
  have hnp : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) :=
    sub_mem (Nbar_apply_mem_clSub hkQ hkz hcV hnN hp) hp
  have hmem : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t) := by
    refine ⟨hnp, (mem_fixSub S).mpr fun α hα => ?_⟩
    have h1 := Lbar_apply_sub_mem_span' hkQ hp hα.1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    have hαp : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) p =
        p + c • S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
      rw [hc]
      abel
    have hnc' : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) p) =
        (n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) p) := by
      rw [← coe_mul_apply, ← coe_mul_apply, hnc α hα.2]
    rw [map_sub, hnc', hαp, map_add, map_smul, (mem_Nbar.mp hnN).2 _ hcV]
    abel
  rw [← hfix] at hmem
  exact hmem.2

theorem apply_sub_mem_Vone_of_center {n : S.O} (hnN : n ∈ Nbar S g t)
    (hnc : ∀ x ∈ Nbar S g t, n * x = x * n) (v : S.Qt) :
    (n : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vone S g t g ((h : G) * g) := by
  have haQ := H.conj_mem
  set S' : Submodule (ZMod 2) S.Qt := (Vone S g t g ((h : G) * g)).comap
    ((n : S.Qt →ₗ[ZMod 2] S.Qt) - 1) with hS'
  have hmemS' : ∀ {w : S.Qt}, w ∈ S' ↔
      (n : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g) := by
    intro w
    simp [hS']
  have hperp : LinearMap.BilinForm.orthogonal S.q.polarBilin S' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
    rw [Submodule.mem_bot]
    have hwV : w ∈ Vone S g t g ((h : G) * g) := by
      refine mem_Vone_of_polar_eq_zero _ _ fun w' hw' => ?_
      have := hw w' (hmemS'.mpr (Nbar_apply_sub_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hnN
        hw'))
      rwa [polarBilin_apply_apply, polar_comm] at this
    refine eq_zero_of_forall_mem_clSub H C ht ht1 hVQ fun k hk => ?_
    have hkQ := conj_mem_QG' S k.2 haQ
    have horth := orthogonal_clSub_eq hkQ (conj_ne_z' S k.2 H.conj_ne)
      (C.mul k).card_QG_inf_Qa
    rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    exact hw p (hmemS'.mpr
      (apply_sub_mem_Vone_of_center_clSub hCE H hNo C ht ht1 hVQ hSp hh hb hnN hnc hk hp))
  have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate S'
  rw [hperp, finrank_bot] at h1
  have h2 := Submodule.finrank_le S'
  have htop : S' = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  have : v ∈ S' := htop ▸ Submodule.mem_top
  exact hmemS'.mp this

theorem mem_zpowers_of_mem_Abar_center {α : S.O} (hαA : α ∈ S.Lbar g ⊓ Nbar S g t)
    (hαc : ∀ x ∈ Nbar S g t, α * x = x * α) : α ∈ zpowers t := by
  have haQ := H.conj_mem
  have htt := mul_self_of_mem_Lbar S haQ ht
  have hdV := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have hdV1 := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
  by_contra hαt
  have key : ∀ x ∈ S.Lbar g ⊓ Nbar S g t, (∀ y ∈ Nbar S g t, x * y = y * x) → x ∉ zpowers t →
      ∃ u ∈ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt), u ∉ S.clSub (S.QG ⊓ S.Qa g) ∧
        commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔
          (ZMod 2) ∙ u ∧ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vone S g t g ((h : G) * g) ∧
        commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ Vt S g t ∧
        finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
          finrank (ZMod 2) (Vt S g t) := by
    intro x hxA hxc hxt
    have hx1 : x ≠ 1 := fun h1 => hxt (h1 ▸ one_mem _)
    have hxV1 : commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vone S g t g ((h : G) * g) := by
      intro w hw
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
      exact apply_sub_mem_Vone_of_center hCE H hNo C ht ht1 hVQ hSp hh hb hxA.2 hxc v
    have haV : S.cl (g * S.z * g⁻¹) ∈ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      by_contra hna
      apply hx1
      refine C.faithful _ hxA.1 fun v hv => ?_
      rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' haQ hv hxA.1) with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd (h0 ▸ sub_mem_commSpace _ v) hna
    obtain ⟨u, hu, huP⟩ : ∃ u ∈ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt),
        u ∉ S.clSub (S.QG ⊓ S.Qa g) := by
      by_contra hcon
      push Not at hcon
      exact hx1 (C.faithful _ hxA.1 (fix_of_commSpace_le_isotropic
        (fun u hu v hv => polar_eq_zero_of_mem_clSub H.conj_ne hu hv) hcon))
    have hsub := inf_le_commSpace H C ht ht1 hVQ hSp hxA.1 haV (zero_mem _) (hxV1 hu) huP
      (by rw [zero_add]; exact hu)
    have hle : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (ZMod 2) ∙ u ≤
        commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      sup_le hsub ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)
    have hlt : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t <
        (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (ZMod 2) ∙ u :=
      lt_of_le_of_ne le_sup_left fun h0 => huP (by
        have : u ∈ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (ZMod 2) ∙ u :=
          Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
        rw [← h0] at this
        exact this.1)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_mono hle
    have h3 := Submodule.finrank_mono hxV1
    have h6 := Submodule.finrank_add_le_finrank_add_finrank
      (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ((ZMod 2) ∙ u)
    have h7 := finrank_span_le_card (R := ZMod 2) ({u} : Set S.Qt)
    rw [Set.toFinset_singleton, Finset.card_singleton] at h7
    have hxx : x * x = 1 := mul_self_of_mem_Lbar S haQ hxA.1
    have heven := even_finrank_commSpace_of_forall_eq_zero S.q_nondegenerate x.2
      (by rw [← Subgroup.coe_mul, hxx]; rfl)
      (fun v hv => q_eq_zero_of_mem_Vone H C ht ht1 hVQ hh hb (hxV1 hv))
    obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
    obtain ⟨e, he⟩ := heven
    have hdim : finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
        finrank (ZMod 2) (Vt S g t) := by omega
    have heq : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (ZMod 2) ∙ u =
        commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    refine ⟨u, hu, huP, heq.symm, hxV1, fun hV => hxt ?_, hdim⟩
    refine mem_zpowers_of_fix_clSub_inf_Wt H C ht ht1 hVQ hxA.1 fun w hw => ?_
    exact apply_eq_of_commSpace_le hV.le fun v hv => mem_Wt.mp hw.2 v hv
  have hout : ∀ x ∈ S.Lbar g ⊓ Nbar S g t, (∀ y ∈ Nbar S g t, x * y = y * x) →
      x ∉ zpowers t → ∀ y ∈ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt),
        y ∉ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t → y ∉ Vt S g t ∧ y ∉ S.clSub (S.QG ⊓ S.Qa g) := by
    intro x hxA hxc hxt y hy hyD
    obtain ⟨u, hu, huP, hE, -, hEV, hdim⟩ := key x hxA hxc hxt
    have hle : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (ZMod 2) ∙ y ≤
        commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      refine sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr hy)
      rw [hE]
      exact le_sup_left
    have hlt : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t <
        (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (ZMod 2) ∙ y :=
      lt_of_le_of_ne le_sup_left fun h0 => hyD (by
        rw [h0]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have hsp : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ (ZMod 2) ∙ y =
        commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    refine ⟨fun hyV => hEV ?_, fun hyP => huP ?_⟩
    · refine Submodule.eq_of_le_of_finrank_le ?_ (by omega)
      rw [← hsp]
      exact sup_le inf_le_right ((Submodule.span_singleton_le_iff_mem _ _).mpr hyV)
    · rw [← hsp] at hu
      obtain ⟨d, hd, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      exact add_mem hd.1 (Submodule.smul_mem _ _ hyP)
  have hαtA : α * t ∈ S.Lbar g ⊓ Nbar S g t :=
    mul_mem hαA ⟨ht, self_mem_Nbar H ht⟩
  have hαtc : ∀ y ∈ Nbar S g t, α * t * y = y * (α * t) := by
    intro y hy
    rw [mul_assoc, ← commute_of_mem_Rbar haQ (Nbar_le_Rbar hy), ← mul_assoc, hαc y hy,
      mul_assoc]
  have hαtt : α * t ∉ zpowers t := fun hm => hαt (by
    have := mul_mem hm (mem_zpowers t)
    rwa [mul_assoc, htt, mul_one] at this)
  obtain ⟨u, hu, huP, hE, hEV1, hEV, hdimα⟩ := key α hαA hαc hαt
  obtain ⟨-, -, -, -, hEV1', -, -⟩ := key (α * t) hαtA hαtc hαtt
  have huD : u ∉ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := fun h0 => huP h0.1
  have huV := (hout α hαA hαc hαt u hu huD).1
  have hVV1 : Vt S g t ≤ Vone S g t g ((h : G) * g) := Vt_le_Vone _ _
  have hP1 : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g)) + 1 =
      finrank (ZMod 2) (Vone S g t g ((h : G) * g)) := by
    have := finrank_clSub_inf_Vone H C ht ht1 hVQ (k := 1)
      (by rw [map_one]; exact one_mem _) ((h : G) * g)
    rwa [show ((1 : S.M) : G) * g = g by simp] at this
  have hPV : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g) ≤
      Vone S g t g ((h : G) * g) := inf_le_right
  have hsub : commSpace ((α * t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro y hy
    by_cases hyD : y ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t
    · rw [hE]
      exact Submodule.mem_sup_left hyD
    obtain ⟨hyV, hyP⟩ := hout (α * t) hαtA hαtc hαtt y hy hyD
    have hyV1 := hEV1' hy
    have huV1 := hEV1 hu
    have h1 := add_mem_of_not_mem_hyperplane hVV1 (by omega) hyV1 huV1 hyV huV
    have h2 := add_mem_of_not_mem_hyperplane hPV (by omega) hyV1 huV1
      (fun h0 => hyP h0.1) (fun h0 => huP h0.1)
    have h3 : y + u ∈ commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [hE]
      exact Submodule.mem_sup_left ⟨h2.1, h1⟩
    have := sub_mem h3 hu
    rwa [add_sub_cancel_right] at this
  apply hEV
  have hct := (commSpace_t_eq H C ht ht1 hVQ).1
  have hαα : α * α = 1 := mul_self_of_mem_Lbar S haQ hαA.1
  have ht' : t = α * (α * t) := by rw [← mul_assoc, hαα, one_mul]
  have hle : Vt S g t ≤ commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← hct, ht', Subgroup.coe_mul]
    exact (commSpace_mul_le _ _).trans (sup_le le_rfl hsub)
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

omit hCE hNo hSp hh hb in
theorem nqImage_center_invariant (hSp : SpCase H C ht ht1 hVQ) [NQHyp S g t]
    (e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) :
    ∀ u ∈ S8.nqImage S g t (centralizer (Nbar S g t : Set S.O)),
      nqRep S g t hSp.eq_sp e u ∈ S8.nqImage S g t (centralizer (Nbar S g t : Set S.O)) := by
  have haQ := H.conj_mem
  rintro _ ⟨n', hn', rfl⟩
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hSp.eq_sp]
    exact e.2
  rw [← range_resV haQ t] at heR
  obtain ⟨r, hr⟩ := heR
  rw [nqRep_apply hSp.eq_sp hr.symm n']
  refine ⟨nConj r n', mem_centralizer_iff.mpr fun x hx => ?_, rfl⟩
  rw [coe_nConj]
  have hrx : (r : S.O)⁻¹ * x * r ∈ Nbar S g t := by
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar r.2)
    have hkt := commute_of_mem_Rbar haQ (hk ▸ r.2)
    have hkt' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
      rw [map_inv]
      calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hkt]
        _ = t * (S.ρ k)⁻¹ := by group
    have := conj_mem_Nbar haQ hkt' hx
    rwa [map_inv, inv_inv, hk] at this
  have h2 := mem_centralizer_iff.mp hn' _ hrx
  calc x * (r * n' * (r : S.O)⁻¹) = r * (((r : S.O)⁻¹ * x * r) * n') * (r : S.O)⁻¹ := by group
    _ = r * (n' * ((r : S.O)⁻¹ * x * r)) * (r : S.O)⁻¹ := by rw [h2]
    _ = r * n' * (r : S.O)⁻¹ * x := by group

theorem mem_zpowers_of_mem_Bbar_center {n : S.O} (hnB : n ∈ S.Lbar ((h : G) * g) ⊓ Nbar S g t)
    (hnc : ∀ x ∈ Nbar S g t, n * x = x * n) : n ∈ zpowers t := by
  have haQ := H.conj_mem
  have hht := commute_of_mem_Rbar haQ hh
  have hht' : S.ρ h⁻¹ * t = t * S.ρ h⁻¹ := by
    rw [map_inv]
    calc (S.ρ h)⁻¹ * t = (S.ρ h)⁻¹ * (t * S.ρ h) * (S.ρ h)⁻¹ := by group
      _ = (S.ρ h)⁻¹ * (S.ρ h * t) * (S.ρ h)⁻¹ := by rw [hht]
      _ = t * (S.ρ h)⁻¹ := by group
  have hconjN : ∀ x ∈ Nbar S g t, (S.ρ h)⁻¹ * x * S.ρ h ∈ Nbar S g t := fun x hx => by
    have := conj_mem_Nbar haQ hht' hx
    rwa [map_inv, inv_inv] at this
  have hc : (S.ρ h)⁻¹ * n * S.ρ h ∈ zpowers t := by
    refine mem_zpowers_of_mem_Abar_center hCE H hNo C ht ht1 hVQ hSp hh hb
      ⟨(mem_Lbar_mul_iff S h g).mp hnB.1, hconjN _ hnB.2⟩ fun x hx => ?_
    have hx' : S.ρ h * x * (S.ρ h)⁻¹ ∈ Nbar S g t := conj_mem_Nbar haQ hht hx
    have h2 := hnc _ hx'
    calc (S.ρ h)⁻¹ * n * S.ρ h * x = (S.ρ h)⁻¹ * (n * (S.ρ h * x * (S.ρ h)⁻¹)) * S.ρ h := by
          group
      _ = (S.ρ h)⁻¹ * ((S.ρ h * x * (S.ρ h)⁻¹) * n) * S.ρ h := by rw [h2]
      _ = x * ((S.ρ h)⁻¹ * n * S.ρ h) := by group
  have e : n = S.ρ h * ((S.ρ h)⁻¹ * n * S.ρ h) * (S.ρ h)⁻¹ := by group
  rw [e, ← commute_of_mem_zpowers hc hht, mul_inv_cancel_right]
  exact hc

theorem mem_zpowers_of_mem_center {n : S.O} (hnN : n ∈ Nbar S g t)
    (hnc : ∀ x ∈ Nbar S g t, n * x = x * n) : n ∈ zpowers t := by
  have haQ := H.conj_mem
  have h1 := pair_one (t := t) hb
  have hth := mem_Lbar_of_pair H ht hh
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have hD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have htK : t ∈ centralizer (Nbar S g t : Set S.O) :=
    mem_centralizer_iff.mpr fun x hx => commute_of_mem_Rbar haQ (Nbar_le_Rbar hx)
  have hdec := spRadDecomp_of_invariant (nqRep S g t hSp.eq_sp) (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (m := m) (by omega) (beta_aV_bV H C ht ht1 hVQ hh hb)
    hD (nqImage_center_invariant H C ht ht1 hVQ hSp)
  have hfa := fixOf_nqRep_eq H hNo C ht ht1 hVQ hgen hN0 hh hb hSp.eq_sp h1.1
    (T := (S2.spRadFix (beta H C ht ht1 hVQ) ⊥ (aV ht) : Set _)) (by
      rw [S2.spRadFix_bot, ← hSp.LmodN_eq]
      ext e
      simp only [SetLike.mem_coe, LmodN, LhmodN, OneMemClass.coe_one, one_mul])
  have hfb := fixOf_nqRep_eq H hNo C ht ht1 hVQ hgen hN0 hh hb hSp.eq_sp hh
    (T := (S2.spRadFix (beta H C ht ht1 hVQ) ⊥ (bV hth) : Set _)) (by
      rw [S2.spRadFix_bot, LhmodN_eq_spPointRadical H C ht ht1 hVQ hSp hh])
  rw [show ((1 : S.M) : G) * g = g by simp] at hfa
  have htop := hdec.1
  rw [hfa, hfb] at htop
  have hmem := (S8.mem_nqImage_mk htK ⟨n, hnN⟩).mpr (mem_centralizer_iff.mpr fun x hx =>
    (hnc x hx).symm)
  rw [← htop] at hmem
  obtain ⟨y, ⟨⟨n₁, hn₁, rfl⟩, hn₁L⟩, z, ⟨⟨n₂, hn₂, rfl⟩, hn₂L⟩, hyz⟩ :=
    Submodule.mem_sup.mp hmem
  rw [SetLike.mem_coe, mem_nqSub ht] at hn₁L
  rw [SetLike.mem_coe, mem_nqSub hth] at hn₂L
  have e1 := mem_zpowers_of_mem_Abar_center hCE H hNo C ht ht1 hVQ hSp hh hb ⟨hn₁L, n₁.2⟩
    fun x hx => (mem_centralizer_iff.mp hn₁ x hx).symm
  have e2 := mem_zpowers_of_mem_Bbar_center hCE H hNo C ht ht1 hVQ hSp hh hb ⟨hn₂L, n₂.2⟩
    fun x hx => (mem_centralizer_iff.mp hn₂ x hx).symm
  rw [(nqMk_eq_zero_iff n₁).mpr e1, (nqMk_eq_zero_iff n₂).mpr e2, add_zero, eq_comm,
    nqMk_eq_zero_iff] at hyz
  exact hyz

end Five

end CFSG.LargeExtraspecial.S9
