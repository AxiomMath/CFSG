module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldRowCT
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Field

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)


theorem mem_normalizer_sup_q2 {G : Type*} [Group G] {A B : Subgroup G} {t : G}
    (hA : t ∈ normalizer (A : Set G)) (hB : t ∈ normalizer (B : Set G)) :
    t ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

section Step3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {t : G}

theorem map_C3Levi_le_centralizer_of_comp (e : L ≃* adjointGroup .F4 (fixSubfield σ))
    {X : Subgroup G} (hXL : X ≤ L)
    (hXD : ∀ a : adjointGroup .F4 (fixSubfield σ), ((e.symm a : L) : G) ∈ X →
      C3Levi K ≤ centralizer ({fixedFieldInclusion σ a} : Set (adjointGroup .F4 K)))
    {Φ : adjointGroup .F4 K →* G}
    (hΦ : ∀ x : adjointGroup .F4 (fixSubfield σ),
      Φ (fixedFieldInclusion σ x) = ((e.symm x : L) : G)) :
    (C3Levi K).map Φ ≤ centralizer (X : Set G) := by
  rintro _ ⟨d, hd, rfl⟩
  rw [mem_centralizer_iff]
  intro x hx
  set a : adjointGroup .F4 (fixSubfield σ) := e ⟨x, hXL hx⟩ with ha
  have hax : ((e.symm a : L) : G) = x := by rw [ha, MulEquiv.symm_apply_apply]
  have hc := mem_centralizer_singleton_iff.1 (hXD a (hax ▸ hx) hd)
  rw [← hax, ← hΦ a, ← map_mul, ← map_mul, hc]

theorem map_C3Levi_le_centralizerPerfectCore_of_comp
    (e : L ≃* adjointGroup .F4 (fixSubfield σ)) {X : Subgroup G} (hXL : X ≤ L)
    (hXD : ∀ a : adjointGroup .F4 (fixSubfield σ), ((e.symm a : L) : G) ∈ X →
      C3Levi K ≤ centralizer ({fixedFieldInclusion σ a} : Set (adjointGroup .F4 K)))
    {Φ : adjointGroup .F4 K →* G}
    (hΦ : ∀ x : adjointGroup .F4 (fixSubfield σ),
      Φ (fixedFieldInclusion σ x) = ((e.symm x : L) : G)) :
    (C3Levi K).map Φ ≤ centralizerPerfectCore X := by
  have hDp : ⁅C3Levi K, C3Levi K⁆ = C3Levi K := isPerfect_iff.mp isQuasisimple_C3Levi.1
  refine le_centralizerPerfectCore ?_ (map_C3Levi_le_centralizer_of_comp e hXL hXD hΦ)
  rw [← map_commutator, hDp]

theorem conjugate_eq_q2FieldRow (hw : F4Work L (fixSubfield σ) t 1)
    (hq : QuadraticFrobenius K σ 1) (e : L ≃* adjointGroup .F4 (fixSubfield σ))
    {X : Subgroup G} (hXL : X ≤ L)
    (hXD : ∀ a : adjointGroup .F4 (fixSubfield σ), ((e.symm a : L) : G) ∈ X →
      C3Levi K ≤ centralizer ({fixedFieldInclusion σ a} : Set (adjointGroup .F4 K)))
    (e₀ : ↥(centralizerPerfectCore X ⊔ L) ≃* adjointGroup .F4 K) (h : G)
    (htM : t ∈ normalizer (CFSG.conjugate (centralizerPerfectCore X ⊔ L) h : Set G))
    (hML : CFSG.conjugate (centralizerPerfectCore X ⊔ L) h ⊓ centralizer ({t} : Set G) = L) :
    CFSG.conjugate (centralizerPerfectCore X ⊔ L) h = centralizerPerfectCore X ⊔ L := by
  set G₀ := centralizerPerfectCore X ⊔ L with hG₀
  set M := CFSG.conjugate G₀ h with hM
  let eM : M ≃* adjointGroup .F4 K := (conjugateSymmEquiv G₀ h).trans e₀
  obtain ⟨Φ, hΦinj, hΦrange, hΦ⟩ := exists_injective_comp_fixedFieldInclusion_eq hw.standard
    le_rfl hq.card_eq hq.apply_eq hw.card_eq e hw.mem_centralizer hw.orderOf_eq eM htM hML
  have hMr := range_eq_sup_of_map_C3Levi (EX := (C3Levi K).map Φ) hΦ rfl
  have hle : M ≤ G₀ := by
    rw [← hΦrange, hMr, hG₀]
    exact sup_le_sup_right (map_C3Levi_le_centralizerPerfectCore_of_comp e hXL hXD hΦ) L
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm)

end Step3

section Endgame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {t : G}

theorem false_of_q2FieldRow_of_injective (hw : F4Work L (fixSubfield σ) t 1)
    (hq : QuadraticFrobenius K σ 1) (e : L ≃* adjointGroup .F4 (fixSubfield σ))
    {X : Subgroup G} (hXL : X ≤ L)
    (hXD : ∀ a : adjointGroup .F4 (fixSubfield σ), ((e.symm a : L) : G) ∈ X →
      C3Levi K ≤ centralizer ({fixedFieldInclusion σ a} : Set (adjointGroup .F4 K)))
    {ψ : adjointGroup .F4 K →* G} (hinj : Function.Injective ψ)
    (hfix : ∀ x : adjointGroup .F4 (fixSubfield σ),
      ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G))
    (hD : (C3Levi K).map ψ = centralizerPerfectCore X) : False := by
  have hrange := range_eq_sup_of_map_C3Levi hfix hD
  set G₀ := centralizerPerfectCore X ⊔ L with hG₀
  let e₀ : G₀ ≃* adjointGroup .F4 K :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm
  have htC := hw.mem_centralizer
  have hLG : L ≤ G₀ := le_sup_right
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have htN : t ∈ normalizer (G₀ : Set G) :=
    mem_normalizer_sup_q2
      (normalizer_le_normalizer_centralizerPerfectCore X (centralizer_le_normalizer X htX))
      (centralizer_le_normalizer L htC)
  have htG : t ∉ G₀ := not_mem_F4_field hw.standard hw.card_eq e htC hw.orderOf_eq hq.card_eq e₀
  have htCG : t ∉ centralizer (G₀ : Set G) := by
    intro hc
    refine not_exists_inner_F4_field hw.standard hw.card_eq e htC hw.orderOf_eq hq.card_eq e₀
      ⟨1, one_mem _, fun x hx => ?_⟩
    have h1 := mem_centralizer_iff.1 hc x hx
    rw [← h1, mul_inv_cancel_right, one_mul, inv_one, mul_one]
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hw.inf_eq hLG hw.orderOf_eq htN htCG
  have huniq := unique_of_step3_F4_field hw.standard hw.card_eq e htC hw.orderOf_eq hq.card_eq e₀
    fun h htM hML => conjugate_eq_q2FieldRow hw hq e hXL hXD e₀ h htM hML
  have := hw.standard.simple
  exact false_of_simple_of_F4_odd hZ hq.card_eq e₀ htN hw.orderOf_eq htG huniq

end Endgame

end CFSG.SeitzReduction.F4Pilot
