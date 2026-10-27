module

public import CFSG.LargeExtraspecial.S4FiveConj
public import CFSG.LargeExtraspecial.S4FiveApp
public import CFSG.LargeExtraspecial.S4FiveRad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

section Abstract

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {β : LinearMap.BilinForm (ZMod 2) U}

theorem eq_spPointRadical_of_normalized (hβ : β.IsAlt) (hnd : β.Nondegenerate) {a : U}
    (ha : a ≠ 0) {E : Subgroup (U ≃ₗ[ZMod 2] U)} (hEU : E ≤ spPointRadical β a)
    (hidx : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E) (hτ : spTransvection β hβ a ∈ E)
    (hnorm : ∀ x ∈ TauCeti.BilinForm.isometryGroup β, x a = a →
      x ∈ normalizer (E : Set (U ≃ₗ[ZMod 2] U))) :
    E = spPointRadical β a := by
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have : Finite (U ≃ₗ[ZMod 2] U) := finite_linearEquiv_of_finite
  refine le_antisymm hEU fun u hu => ?_
  by_contra huE
  obtain ⟨d, had, l, rfl⟩ := exists_eq_spRho hβ hnd ha hu
  have h0 : β a 0 = 0 := map_zero _
  have hρ0 : ∀ l', spRho hβ h0 l' ∈ E := by
    intro l'
    rcases zmod2_eq_zero_or_eq_one l' with rfl | rfl
    · rw [spRho_zero_zero]
      exact one_mem _
    · rw [spRho_zero_one]
      exact hτ
  have hdP : d ∉ (ZMod 2) ∙ a := by
    intro hdP
    apply huE
    rcases mem_span_singleton_iff.mp hdP with hd0 | hda
    · rw [spRho_congr hβ had h0 rfl hd0 rfl]
      exact hρ0 l
    · have h' : β a (0 + a) = 0 := by rw [zero_add]; exact hβ.self_eq_zero a
      rw [spRho_congr hβ had h' rfl (by rw [zero_add, hda]) rfl, spRho_add_self hβ h0 l h']
      exact hρ0 l
  have key : ∀ c (hac : β a c = 0), β d c = 1 → ∀ l', spRho hβ hac l' ∈ E := by
    intro c hac hdc l'
    have hcI := spTransvection_mem_isometryGroup hβ c
    have hca : spTransvection β hβ c a = a := by
      rw [spTransvection_apply, hac, zero_smul, add_zero]
    have hcd : spTransvection β hβ c d = d + c := by
      rw [spTransvection_apply, hdc, one_smul]
    have hadc : β a (d + c) = 0 := by rw [map_add, had, hac, add_zero]
    have hconj : spTransvection β hβ c * spRho hβ had l * (spTransvection β hβ c)⁻¹ =
        spRho hβ hadc l := by
      rw [conj_spRho hβ had l hcI (by rw [hca, hcd]; exact hadc)]
      exact spRho_congr hβ _ _ hca hcd rfl
    have hnot : spRho hβ hadc l ∉ E := by
      intro hmem
      apply huE
      have := (mem_normalizer_iff.mp (hnorm _ hcI hca) (spRho hβ had l)).mpr
      rw [hconj] at this
      exact this hmem
    rcases mem_or_mul_mem_of_card hEU hidx hu huE (spRho_mem_spPointRadical hβ hadc l) with
      h | h
    · exact absurd h hnot
    · have hac' : β a (d + c + d) = 0 := by rw [map_add, hadc, had, add_zero]
      rw [spRho_mul hβ hadc had l l hac'] at h
      have hl : l + l + β (d + c) d = 1 := by
        rw [zmod2_add_self, zero_add, map_add, LinearMap.add_apply, hβ.self_eq_zero, zero_add,
          isAlt_symm hβ, hdc]
      have hdcd : d + c + d = c := by
        rw [add_comm d c, add_assoc, vec_add_self, add_zero]
      rw [spRho_congr hβ hac' hac rfl hdcd hl] at h
      rcases zmod2_eq_zero_or_eq_one l' with rfl | rfl
      · have h2 := mul_mem h hτ
        rwa [← spRho_zero_one hβ a h0, spRho_mul hβ hac h0 1 1 (by rw [add_zero]; exact hac),
          spRho_congr hβ _ hac rfl (add_zero c) (by rw [map_zero, add_zero, zmod2_add_self])]
          at h2
      · exact h
  obtain ⟨c, hac, -, hdc⟩ := exists_dual_triple hβ hnd (b := a) (c := a) (e := d)
    (by rwa [Set.pair_eq_singleton])
  have hac2 : β a (d + c) = 0 := by rw [map_add, had, hac, add_zero]
  have hdc2 : β d (d + c) = 1 := by rw [map_add, hβ.self_eq_zero, zero_add, hdc]
  have h1 := key c hac hdc (l + 1)
  have h2 := key (d + c) hac2 hdc2 0
  have hacc : β a (c + (d + c)) = 0 := by rw [map_add, hac, hac2, add_zero]
  have := mul_mem h1 h2
  rw [spRho_mul hβ hac hac2 (l + 1) 0 hacc] at this
  refine huE ?_
  have hsum : c + (d + c) = d := by rw [add_comm d c, ← add_assoc, vec_add_self, zero_add]
  have hl : l + 1 + 0 + β c (d + c) = l := by
    have hcd : β c d = 1 := by rw [isAlt_symm hβ, hdc]
    rw [map_add, hcd, hβ.self_eq_zero]
    rcases zmod2_eq_zero_or_eq_one l with rfl | rfl <;> rfl
  rwa [spRho_congr hβ hacc had rfl hsum hl] at this

end Abstract

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H C ht ht1 hVQ

omit C ht1 hVQ in
theorem RmodN_le_closure_conj_of_transitive
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v) :
    RmodN S g t ≤ closure {u | ∃ x ∈ RmodN S g t, ∃ e ∈ LmodN S g t, u = x * e * x⁻¹} :=
  RmodN_le_closure_conj H ht fun _ hth => htr _ (bV_ne_zero H hth)

theorem LmodN_eq_spPointRadical
    (hSp : RmodN S g t = TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ))
    (hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∈ LmodN S g t) :
    LmodN S g t = spPointRadical (beta H C ht ht1 hVQ) (aV ht) :=
  eq_spPointRadical_of_normalized (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ)
    (aV_ne_zero H ht) (LmodN_le_spPointRadical H C ht ht1 hVQ)
    (card_spPointRadical_le_two_mul H C ht ht1 hVQ) hτ fun _ hx hxa =>
      mem_normalizer_LmodN H ht (hSp ▸ hx) hxa

theorem RmodN_eq_isometryGroup_of_six (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t))
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v) :
    RmodN S g t = TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) ∧
      spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∈ LmodN S g t :=
  ⟨eq_isometryGroup_of_transitive (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ)
      h6 (RmodN_le_isometryGroup H C ht ht1 hVQ) (aV_ne_zero H ht) (LmodN_le_RmodN ht)
      (LmodN_le_spPointRadical H C ht ht1 hVQ) (card_spPointRadical_le_two_mul H C ht ht1 hVQ)
      (fun _ hx hxa => mem_normalizer_LmodN H ht hx hxa) htr,
    spTransvection_mem_of_transitive (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) h6 (RmodN_le_isometryGroup H C ht ht1 hVQ)
      (aV_ne_zero H ht) (LmodN_le_RmodN ht) (LmodN_le_spPointRadical H C ht ht1 hVQ)
      (card_spPointRadical_le_two_mul H C ht ht1 hVQ)
      (fun _ hx hxa => mem_normalizer_LmodN H ht hx hxa) htr⟩

theorem RmodN_eq_isometryGroup_of_tau_mem
    (hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∈ LmodN S g t)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v) :
    RmodN S g t = TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) :=
  eq_isometryGroup_of_spTransvection_mem (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (RmodN_le_isometryGroup H C ht ht1 hVQ)
    (spTransvection_mem_of_one (beta_isAlt H C ht ht1 hVQ) (RmodN_le_isometryGroup H C ht ht1 hVQ)
      (LmodN_le_RmodN ht hτ) htr)

theorem RmodN_eq_commutator (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    (hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t)
    (hno : ∀ d (hd : beta H C ht ht1 hVQ (aV ht) d = 0), d ∉ (ZMod 2) ∙ aV ht →
      spRho (beta_isAlt H C ht ht1 hVQ) hd 0 ∉ LmodN S g t) :
    RmodN S g t = ⁅TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ),
      TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)⁆ :=
  eq_commutator_of_transitive_four (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ)
    h4 (RmodN_le_isometryGroup H C ht ht1 hVQ) (aV_ne_zero H ht) (LmodN_le_RmodN ht)
    (LmodN_le_spPointRadical H C ht ht1 hVQ) (card_spPointRadical_le_two_mul H C ht ht1 hVQ) hτ
    htr (RmodN_le_closure_conj_of_transitive H ht htr) hno

end CFSG.LargeExtraspecial.S4
