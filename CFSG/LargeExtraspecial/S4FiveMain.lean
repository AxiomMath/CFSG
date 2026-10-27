module

public import CFSG.LargeExtraspecial.S4FiveSp
public import CFSG.LargeExtraspecial.S4FiveOmega
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLGenerate

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem RmodN_eq_top (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (hVQ : V S g t ≤ S.Qa g) :
    RmodN S g t = ⊤ := by
  set f := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Vt S g t) with hf
  have htop : (RmodN S g t).comap f.toMonoidHom = ⊤ := by
    refine CFSG.ComponentClassification.OutcomeLocal.eq_top_of_forall_inG fun φ c hφc =>
      ⟨hφc, ?_⟩
    change f _ ∈ RmodN S g t
    have : f (CFSG.ComponentClassification.OutcomeLocal.tv φ c hφc) =
        LinearEquiv.transvection hφc := by
      ext x
      rfl
    rw [this]
    exact centreGroup_le_RmodN H ht hVQ c (transvection_mem_centreGroup hφc)
  rw [eq_top_iff]
  intro e _
  have : f.symm e ∈ (RmodN S g t).comap f.toMonoidHom := htop ▸ mem_top _
  change f (f.symm e) ∈ RmodN S g t at this
  rwa [MulEquiv.apply_symm_apply] at this

theorem two_le_finrank_Vt (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hR : Rbar S g t ≠ S.Lbar g) : 2 ≤ finrank (ZMod 2) (Vt S g t) := by
  by_contra h2
  apply hR
  refine Rbar_eq_of_Vt_le H ht ?_
  have hle : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
  have h1 := finrank_span_singleton (K := ZMod 2) (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).ge

variable (S) in
structure LinCase (g : G) {t : S.O} (ht : t ∈ S.Lbar g) : Prop where
  le_Qa : V S g t ≤ S.Qa g
  eq_top : RmodN S g t = ⊤
  two_le_finrank : 2 ≤ finrank (ZMod 2) (Vt S g t)
  LmodN_eq : LmodN S g t = centreGroup (Vt S g t) (aV ht)
  mem_orbit : ∀ v : Vt S g t, v ≠ 0 → (v : S.Qt) ∈ orbit S g t

structure SpCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) : Prop where
  eq_sp : RmodN S g t = TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)
  LmodN_eq : LmodN S g t = spPointRadical (beta H C ht ht1 hVQ) (aV ht)
  transitive : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v

structure A6Case (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) : Prop where
  finrank_eq : finrank (ZMod 2) (Vt S g t) = 4
  eq_commutator : RmodN S g t = ⁅TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ),
    TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)⁆
  transitive : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v
  tau_not_mem : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t
  no_typeA : ∀ d (hd : beta H C ht ht1 hVQ (aV ht) d = 0), d ∉ (ZMod 2) ∙ aV ht →
    spRho (beta_isAlt H C ht ht1 hVQ) hd 0 ∉ LmodN S g t

structure OmegaCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) : Prop where
  not_transitive : ∃ v : Vt S g t, v ≠ 0 ∧ v ∉ orbitOf (RmodN S g t) (aV ht)
  exists_form : ∃ (Q : QuadraticForm (ZMod 2) (Vt S g t)) (hQ : Q.polarBilin.Nondegenerate),
    Q.polarBilin = beta H C ht ht1 hVQ ∧ RmodN S g t = omegaGroup Q hQ ∧
      LmodN S g t = pointRadical Q (aV ht) ∧
      ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))

structure PGL25Case (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) : Prop where
  finrank_eq : finrank (ZMod 2) (Vt S g t) = 4
  transitive : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v
  le_closure : RmodN S g t ≤ closure {u | ∃ x ∈ RmodN S g t, ∃ e ∈ LmodN S g t, u = x * e * x⁻¹}
  tau_not_mem : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t
  exists_typeA : ∃ d, ∃ hd : beta H C ht ht1 hVQ (aV ht) d = 0, d ∉ (ZMod 2) ∙ aV ht ∧
    spRho (beta_isAlt H C ht ht1 hVQ) hd 0 ∈ LmodN S g t

theorem timmesfeld_4_5_of_not_le (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) :
    SpCase H C ht ht1 hVQ ∨ A6Case H C ht ht1 hVQ ∨ OmegaCase H C ht ht1 hVQ ∨
      PGL25Case H C ht ht1 hVQ := by
  by_cases htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v
  · have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
    by_cases h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)
    · obtain ⟨hSp, hτ⟩ := RmodN_eq_isometryGroup_of_six H C ht ht1 hVQ h6 htr
      exact Or.inl ⟨hSp, LmodN_eq_spPointRadical H C ht ht1 hVQ hSp hτ, htr⟩
    have h4' : finrank (ZMod 2) (Vt S g t) = 4 := by
      obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
      omega
    by_cases hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∈ LmodN S g t
    · have hSp := RmodN_eq_isometryGroup_of_tau_mem H C ht ht1 hVQ hτ htr
      exact Or.inl ⟨hSp, LmodN_eq_spPointRadical H C ht ht1 hVQ hSp hτ, htr⟩
    by_cases hno : ∀ d (hd : beta H C ht ht1 hVQ (aV ht) d = 0), d ∉ (ZMod 2) ∙ aV ht →
        spRho (beta_isAlt H C ht ht1 hVQ) hd 0 ∉ LmodN S g t
    · exact Or.inr (Or.inl ⟨h4', RmodN_eq_commutator H C ht ht1 hVQ h4' htr hτ hno, htr, hτ, hno⟩)
    · push Not at hno
      obtain ⟨d, hd, hdP, hdL⟩ := hno
      exact Or.inr (Or.inr (Or.inr ⟨h4', htr, RmodN_le_closure_conj_of_transitive H ht htr, hτ,
        d, hd, hdP, hdL⟩))
  · push Not at htr
    obtain ⟨v, hv0, hv⟩ := htr
    have hntr : ∃ v : Vt S g t, v ≠ 0 ∧ v ∉ orbitOf (RmodN S g t) (aV ht) :=
      ⟨v, hv0, fun ⟨x, hx, hxv⟩ => hv x hx hxv⟩
    set RC := radConfig H C ht ht1 hVQ hNo hntr
    refine Or.inr (Or.inr (Or.inl ⟨hntr, RC.qOrbitForm hntr, RC.qOrbitForm_nondegenerate hntr,
      RC.polarBilin_qOrbitForm hntr, RmodN_eq_omegaGroup H C ht ht1 hVQ hNo hntr,
      RC.E_eq_pointRadical hntr, fun w hw0 => ?_⟩))
    rw [RadConfig.qOrbitForm_apply, RadConfig.qOrbit_eq_zero_iff]
    exact ⟨fun h => h.resolve_left hw0, Or.inr⟩

theorem timmesfeld_4_5 (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    Rbar S g t = S.Lbar g ∨ LinCase S g ht ∨
      ∃ hVQ : ¬ V S g t ≤ S.Qa g, SpCase H C ht ht1 hVQ ∨ A6Case H C ht ht1 hVQ ∨
        OmegaCase H C ht ht1 hVQ ∨ PGL25Case H C ht ht1 hVQ := by
  by_cases hR : Rbar S g t = S.Lbar g
  · exact Or.inl hR
  right
  by_cases hVQ : V S g t ≤ S.Qa g
  · exact Or.inl ⟨hVQ, RmodN_eq_top H ht hVQ, two_le_finrank_Vt H ht hR,
      LmodN_eq_centreGroup H ht hVQ, fun v hv0 => mem_orbit_of_V_le H ht hVQ v.2
        fun h => hv0 (Subtype.ext h)⟩
  · exact Or.inr ⟨hVQ, timmesfeld_4_5_of_not_le H hNo C ht ht1 hVQ⟩

end CFSG.LargeExtraspecial.S4
