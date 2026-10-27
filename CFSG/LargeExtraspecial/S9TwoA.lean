module

public import CFSG.LargeExtraspecial.S8Dim4
public import CFSG.LargeExtraspecial.S6TwoD
public import CFSG.LargeExtraspecial.S8DimB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2
  CFSG.LargeExtraspecial.OrthoF2

universe u

section Abstract

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem not_isTypeA_of_minus (hq : q.polarBilin.Nondegenerate)
    (hmin : ∀ T : Submodule (ZMod 2) V, (∀ x ∈ T, q x = 0) → finrank (ZMod 2) T < 2)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1)
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ pointRadical q p) (hx1 : x ≠ 1) : ¬ IsTypeA q x 2 := by
  intro hxa
  obtain ⟨u', hu'K, hu'0, hxu⟩ := S8.exists_eichler_of_mem_pointRadical hq hp0 hp hpp₁ hx hx1
  obtain ⟨-, hpu', hp₁u'⟩ := mem_perp_sup_span_pair.mp hu'K
  have hqu' : q u' = 0 := by
    rcases zmod2_eq_zero_or_eq_one (q u') with h | h
    · exact h
    · rw [hxu] at hxa
      exact absurd hxa (not_isTypeA_eichler hq hp0 hp hpu' h)
  have hli : LinearIndependent (ZMod 2) ![p, u'] := by
    refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
    have h0 : polar q p₁ (a • p) = 0 := by rw [ha, hp₁u']
    rw [polar_smul_right, polar_comm, hpp₁, smul_eq_mul, mul_one] at h0
    rw [h0, zero_smul] at ha
    exact hu'0 ha.symm
  have hT : ∀ v ∈ Submodule.span (ZMod 2) {p, u'}, q v = 0 := by
    intro v hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    have h0 : q (a • p + b • u') = q (a • p) + q (b • u') + polar q (a • p) (b • u') := by
      rw [polar]; abel
    rw [h0, QuadraticMap.map_smul, QuadraticMap.map_smul, hp, hqu', polar_smul_left,
      polar_smul_right, hpu']
    simp
  have h2 := hmin _ hT
  rw [finrank_span_pair hli] at h2
  omega

variable {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem finrank_eq_two_mul_finrank_commSpace_minus (hdim : finrank (ZMod 2) V = 4)
    (hmin : ∀ T : Submodule (ZMod 2) V, (∀ x ∈ T, q x = 0) → finrank (ZMod 2) T < 2)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hD : RadDecomp ρ ⊥ ⊤ p p₁) (x : omegaGroup q hq)
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p) (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) :
    finrank (ZMod 2) M = 2 * finrank (ZMod 2) (commSpace (ρ x)) :=
  S8.finrank_eq_two_mul_finrank_commSpace ρ le_rfl (by rw [hdim]) hp hp₁ hpp₁ hD x hx hx1
    (not_isTypeA_of_minus hq hmin hp0 hp hpp₁ hx hx1)

theorem false_of_finrank_eq_four_minus (hdim : finrank (ZMod 2) V = 4)
    (hmin : ∀ T : Submodule (ZMod 2) V, (∀ x ∈ T, q x = 0) → finrank (ZMod 2) T < 2)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hD : RadDecomp ρ ⊥ ⊤ p p₁) {qM : QuadraticForm (ZMod 2) M}
    (hqM : qM.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) M = 4)
    (hinv : ∀ e u, qM (ρ e u) = qM u) : False := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hmem : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hK := sup_span_pair_inf_perp_eq_bot hF (hmem p) (hmem p₁) hpp₁
  have hKdim := finrank_perp_sup_span_pair hq hF (hmem p) (hmem p₁) hpp₁
  rw [perp_bot, finrank_top, hdim] at hKdim
  obtain ⟨u, huK, u', hu'K, hu, hu', huu'⟩ := S8.exists_nonsingular_pair hq hK (by
    right
    refine ⟨by omega, fun w hwK hw => ?_⟩
    by_contra hw0
    obtain ⟨-, hpw, -⟩ := mem_perp_sup_span_pair.mp hwK
    have hli : LinearIndependent (ZMod 2) ![p, w] := by
      refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
      have h0 : polar q p₁ (a • p) = 0 := by
        rw [ha]; exact (mem_perp_sup_span_pair.mp hwK).2.2
      rw [polar_smul_right, polar_comm, hpp₁, smul_eq_mul, mul_one] at h0
      rw [h0, zero_smul] at ha
      exact hw0 ha.symm
    have hT : ∀ v ∈ Submodule.span (ZMod 2) {p, w}, q v = 0 := by
      intro v hv
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
      rw [QuadraticMap.map_add q (a • p) (b • w), QuadraticMap.map_smul,
        QuadraticMap.map_smul, hp, hw, polar_smul_left, polar_smul_right, hpw]
      simp
    have h2' := hmin _ hT
    rw [finrank_span_pair hli] at h2'
    omega)
  obtain ⟨-, hpu, -⟩ := mem_perp_sup_span_pair.mp huK
  obtain ⟨-, hpu', -⟩ := mem_perp_sup_span_pair.mp hu'K
  have hpuu' : polar q p (u + u') = 0 := by rw [polar_add_right, hpu, hpu', add_zero]
  have hquu' : q (u + u') = 1 := by
    rw [QuadraticMap.map_add q u u', hu, hu', huu']
    rfl
  have hli : ∀ {w : V}, q w = 1 → LinearIndependent (ZMod 2) ![p, w] := by
    intro w hw
    refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
    have h0 : q (a • p) = 1 := by rw [ha, hw]
    rw [QuadraticMap.map_smul, hp, smul_zero] at h0
    exact zero_ne_one h0
  have hrad : ∀ {w : V}, polar q p w = 0 →
      CFSG.ClassicalGroups.Orthogonal.eichler q p w ∈ omegaGroup q hq := fun hw =>
    S2.pointRadical_le_omegaGroup hq hp0 hp (eichler_mem_pointRadical hp hw)
  set x : omegaGroup q hq := ⟨_, hrad hpu⟩ with hx
  set y : omegaGroup q hq := ⟨_, hrad hpu'⟩ with hy
  have hxy : ((x * y : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) =
      CFSG.ClassicalGroups.Orthogonal.eichler q p (u + u') := by
    rw [Subgroup.coe_mul]
    exact CFSG.ClassicalGroups.Orthogonal.eichler_mul hpu hpu'
  have hdim' : finrank (ZMod 2) V = 2 * 2 := by rw [hdim]
  obtain ⟨hXf, hXc⟩ := S8.fixSpace_eq_and_commSpace_eq ρ le_rfl hdim' hp hp₁ hpp₁ hD x
    (eichler_mem_pointRadical hp hpu) (eichler_ne_one hq hp hpu (hli hu))
    (not_isTypeA_eichler hq hp0 hp hpu hu)
  obtain ⟨hYf, hYc⟩ := S8.fixSpace_eq_and_commSpace_eq ρ le_rfl hdim' hp hp₁ hpp₁ hD y
    (eichler_mem_pointRadical hp hpu') (eichler_ne_one hq hp hpu' (hli hu'))
    (not_isTypeA_eichler hq hp0 hp hpu' hu')
  obtain ⟨hXYf, -⟩ := S8.fixSpace_eq_and_commSpace_eq ρ le_rfl hdim' hp hp₁ hpp₁ hD (x * y)
    (by rw [hxy]; exact eichler_mem_pointRadical hp hpuu')
    (by rw [hxy]; exact eichler_ne_one hq hp hpuu' (hli hquu'))
    (by rw [hxy]; exact not_isTypeA_eichler hq hp0 hp hpuu' hquu')
  rw [map_mul] at hXYf
  exact S8.false_of_unipotent_triple hqM h4 (hinv x) (hinv y) hXf hXc hYf hYc hXYf

end Abstract

section Setting

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}
variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hA6 : A6Case H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hA6 hh hb

theorem finrank_WV_ne_four_a6 : finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≠ 4 := by
  intro h4
  obtain ⟨Q, hQ, hpolβ, hQa, hQb, hmin, -, -, hR0, ρ, hρ, hD, -⟩ :=
    timmesfeld_6_2_two hCE H hNo C ht ht1 hVQ hA6 hh hb
  obtain ⟨qM, hqM, hqMsec⟩ := S8.exists_quadraticForm_WV H ht1 (g := g)
  have hpol : polar Q (aV ht) (bV (mem_Lbar_of_pair H ht hh)) = 1 := by
    rw [← polarBilin_apply_apply, hpolβ]
    exact beta_aV_bV H C ht ht1 hVQ hh hb
  have hinv : ∀ (e : omegaGroup Q hQ) u, qM (ρ e u) = qM u := by
    intro e u
    have he : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈
        ((R0bar S g h).subgroupOf (Rbar S g t)).map (resV H.conj_mem t) := by
      rw [hR0]; exact e.2
    obtain ⟨r, hr, hre⟩ := Subgroup.mem_map.mp he
    have hr' : (r : S.O) ∈ R0bar S g h := mem_subgroupOf.mp hr
    obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.mp u.2
    have hu : u = secMk (Vt S g t) hw := Subtype.ext hwu.symm
    have hrw : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t := apply_mem_Wt H r.2 hw
    have hρu : ρ e u = secMk (Vt S g t) hrw := by
      rw [hu]
      exact Subtype.ext (hρ e hr' hre.symm w hw)
    rw [hρu, hqMsec, hu, hqMsec]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (r : S.O).2 w
  exact false_of_finrank_eq_four_minus ρ hA6.finrank_eq hmin (aV_ne_zero H ht) hQa hQb hpol hD
    hqM h4 hinv

theorem finrank_commSpace_resV_eq_two_a6 {τ : S.O} (hτL : τ ∈ S.Lbar g)
    (hτN : τ ∉ Nbar S g t) :
    finrank (ZMod 2) (commSpace (resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩)) = 2 := by
  obtain ⟨Q, hQ, hpolβ, hQa, -, -, hEa, -⟩ := timmesfeld_6_2_two hCE H hNo C ht ht1 hVQ hA6 hh hb
  have hth := mem_Lbar_of_pair H ht hh
  have hpol : polar Q (aV ht) (bV hth) = 1 := by
    rw [← polarBilin_apply_apply, hpolβ]
    exact beta_aV_bV H C ht ht1 hVQ hh hb
  have hx : resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩ ∈ pointRadical Q (aV ht) := by
    rw [← hEa]
    exact ⟨τ, hτL, fun v => coe_resV_apply H.conj_mem _ v⟩
  have hx1 : resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩ ≠ 1 := fun h =>
    hτN ((resV_eq_one_iff H.conj_mem _).mp h)
  obtain ⟨u, huK, hu0, hxu⟩ := S8.exists_eichler_of_mem_pointRadical hQ (aV_ne_zero H ht) hQa
    hpol hx hx1
  obtain ⟨-, hau, hbu⟩ := mem_perp_sup_span_pair.mp huK
  have hli : LinearIndependent (ZMod 2) ![aV ht, u] := by
    refine (LinearIndependent.pair_iff' (aV_ne_zero H ht)).mpr fun c hc => ?_
    have h0 : polar Q (bV hth) (c • aV ht) = 0 := by rw [hc, hbu]
    rw [polar_smul_right, polar_comm, hpol, smul_eq_mul, mul_one] at h0
    rw [h0, zero_smul] at hc
    exact hu0 hc.symm
  rw [hxu, commSpace_eichler hQ hQa hau hli, finrank_span_pair hli]

theorem finrank_WV_eq_two_mul_commWV_a6 {τ : S.O} (hτL : τ ∈ S.Lbar g)
    (hτN : τ ∉ Nbar S g t) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) =
      2 * finrank (ZMod 2) (S8.commWV S g t τ) := by
  obtain ⟨Q, hQ, hpolβ, hQa, hQb, hmin, hEa, -, hR0, ρ, hρ, hD, -⟩ :=
    timmesfeld_6_2_two hCE H hNo C ht ht1 hVQ hA6 hh hb
  have hpol : polar Q (aV ht) (bV (mem_Lbar_of_pair H ht hh)) = 1 := by
    rw [← polarBilin_apply_apply, hpolβ]
    exact beta_aV_bV H C ht ht1 hVQ hh hb
  have hτR0 : τ ∈ R0bar S g h := mem_sup_left hτL
  have heΩ : resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩ ∈ omegaGroup Q hQ := by
    rw [← hR0]; exact ⟨⟨τ, Lbar_le_Rbar ht hτL⟩, mem_subgroupOf.mpr hτR0, rfl⟩
  set e : omegaGroup Q hQ := ⟨_, heΩ⟩ with he
  have hx : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical Q (aV ht) := by
    rw [← hEa]
    exact ⟨τ, hτL, fun v => coe_resV_apply H.conj_mem _ v⟩
  have hx1 : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ≠ 1 := fun h =>
    hτN ((resV_eq_one_iff H.conj_mem _).mp h)
  have h2 := finrank_eq_two_mul_finrank_commSpace_minus ρ hA6.finrank_eq hmin (aV_ne_zero H ht)
    hQa hQb hpol hD e hx hx1
  have e1 : (commSpace (ρ e)).map ((Wt S g t).map (Vt S g t).mkQ).subtype =
      S8.commWV S g t τ := by
    ext y
    constructor
    · rintro ⟨_, hz, rfl⟩
      obtain ⟨z, rfl⟩ := mem_commSpace.mp hz
      obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp z.2
      have hz' : z = secMk (Vt S g t) hw := Subtype.ext hwz.symm
      refine S8.mem_commWV.mpr ⟨w, hw, ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, hz', hρ e hτR0 rfl w hw, map_sub]
      rfl
    · intro hy
      obtain ⟨w, hw, rfl⟩ := S8.mem_commWV.mp hy
      refine ⟨ρ e (secMk (Vt S g t) hw) - secMk (Vt S g t) hw, sub_mem_commSpace _ _, ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, hρ e hτR0 rfl w hw, map_sub]
      rfl
  rw [← e1, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (Submodule.injective_subtype _) _).symm, h2]

theorem finrank_commSpace_ge_a6 {τ : S.O} (hτL : τ ∈ S.Lbar g) (hτN : τ ∉ Nbar S g t) :
    8 + finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≤
      2 * finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have h2 := finrank_commSpace_resV_eq_two_a6 hCE H hNo C ht ht1 hVQ hA6 hh hb hτL hτN
  have hWV := finrank_WV_eq_two_mul_commWV_a6 hCE H hNo C ht ht1 hVQ hA6 hh hb hτL hτN
  have hQW : finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Wt S g t).mkQ) = 2 :=
    (S8.finrank_commQW_eq H C ht ht1 hVQ ⟨τ, Lbar_le_Rbar ht hτL⟩).trans h2
  have hV : finrank (ZMod 2)
      ((Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) = 2 := by
    have e2 : (Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) =
        (commSpace (resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩)).map (Vt S g t).subtype := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨resV H.conj_mem t ⟨τ, Lbar_le_Rbar ht hτL⟩ ⟨v, hv⟩ - ⟨v, hv⟩,
          sub_mem_commSpace _ _, ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub, coe_resV_apply]
        rfl
      · rintro ⟨_, hz, rfl⟩
        obtain ⟨z, rfl⟩ := mem_commSpace.mp hz
        refine ⟨z, z.2, ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub, coe_resV_apply]
        rfl
    rw [e2, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (Submodule.injective_subtype _) _).symm]
    exact h2
  have hτt : τ * t = t * τ := commute_of_mem_Rbar H.conj_mem (Lbar_le_Rbar ht hτL)
  have hτC : τ ∈ S8.CMt S t := S8.mem_CMt.mpr ⟨Rbar_le_Mbar (Lbar_le_Rbar ht hτL), hτt⟩
  have hfilt := S8.finrank_commSpace_ge (S := S) (g := g) (t := t) (τ := τ)
    (fun v hv => S8.apply_mem_Vt_of_mem_CMt H.conj_mem hτC hv)
    (fun w hw => S8.apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hw) (Vt_le_Wt H ht1)
  rw [hQW, hV] at hfilt
  omega

omit hNo in
theorem finrank_commSpace_le_seven_a6 {α : S.O} (hα : α ∈ S.Lbar g ⊓ Nbar S g t) :
    finrank (ZMod 2) (commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 7 := by
  obtain ⟨hαL, hαN⟩ := mem_inf.mp hα
  have hαR0 : α ∈ R0bar S g h ⊓ Nbar S g t := mem_inf.mpr ⟨mem_sup_left hαL, hαN⟩
  obtain ⟨-, h1⟩ := timmesfeld_6_2_one hCE H C ht ht1 hVQ hA6 hh hb
  set f := (α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1 with hf
  have hfW : (Wt S g t).map f ≤ Vt S g t ⊓ S.clSub (S.QG ⊓ S.Qa g) := by
    rintro _ ⟨w, hw, rfl⟩
    exact Submodule.mem_inf.mpr ⟨h1 α hαR0 w hw,
      apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem hw hαL⟩
  have hlt : Vt S g t ⊓ S.clSub (S.QG ⊓ S.Qa g) < Vt S g t := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hbV : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t :=
      (bV (mem_Lbar_of_pair H ht hh)).2
    rw [← heq] at hbV
    exact cl_b_not_mem H hb (Submodule.mem_inf.mp hbV).2
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hA6.finrank_eq] at h3
  have h4 := Submodule.finrank_mono hfW
  have hk1 := S8.finrank_map_add_finrank_inf_ker f (⊤ : Submodule (ZMod 2) S.Qt)
  have hk2 := S8.finrank_map_add_finrank_inf_ker f (Wt S g t)
  have hk3 : finrank (ZMod 2) (Wt S g t ⊓ LinearMap.ker f : Submodule (ZMod 2) S.Qt) ≤
      finrank (ZMod 2) (⊤ ⊓ LinearMap.ker f : Submodule (ZMod 2) S.Qt) :=
    Submodule.finrank_mono (inf_le_inf_right _ le_top)
  have hW := finrank_Wt (S := S) (g := g) (t := t)
  rw [hA6.finrank_eq] at hW
  have hC : commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt) = (⊤ : Submodule (ZMod 2) S.Qt).map f := by
    rw [Submodule.map_top]
  rw [hC]
  rw [finrank_top] at hk1
  omega

end Setting

end CFSG.LargeExtraspecial.S9
