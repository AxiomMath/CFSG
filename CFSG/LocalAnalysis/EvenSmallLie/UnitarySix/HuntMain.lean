module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntCentralizer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRank
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClass

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit CFSG.EvenSmallLie.UnitarySix.MathieuExt
  CFSG.ComponentClassification.WittDesign

theorem toddRankBounds
    : ToddRankBounds :=
  ⟨fun _ hX hsq hout => card_mul_card_fixed_le_outer hX hsq hout,
    fun _ _ hsq hin hne => card_mul_card_fixed_le_inner hin hsq hne⟩

variable {G : Type*} [Group G] [Finite G] {t : G} {L E : Subgroup G}
  {p : L →* Equiv.Perm (Fin 693)}

theorem Hyp.of_simple
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (H : ToddOrbit.Hyp t L E p) (D : DavisSolomonFacts G t L E)
    (hCE : centralizer (E : Set G) ≤ E ⊔ centralizer (L : Set G))
    (hCL : centralizer (L : Set G) = zpowers t) : Hyp t L E p :=
  ⟨H, D, centralizer_le_of_le_sup H.t_mem_E hCE hCL,
    SolomonWong.index_ne_two_of_isSimpleGroup (card_ne_two_of_nonabelian hnonab)⟩

section Main

variable
    (H : Hyp t L E p)
include H

theorem Hyp.centralizer_eq' :
    centralizer ({t} : Set G) = L ∧ Nat.card (normalizer (E : Set G)) = 2 ^ 10 * 443520 ∧
      Nonempty (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G)) ≃* M22) ∧
      normalizer (E : Set G) ⊓ centralizer ({t} : Set G) = normalizer (E : Set G) ⊓ L :=
  ⟨H.centralizer_eq toddRankBounds, H.card_normalizer toddRankBounds,
    H.nonempty_quotient_equiv_M22 toddRankBounds, H.normalizer_inf_centralizer toddRankBounds⟩

omit [Finite G] in
theorem Hyp.todd' :
    ToddOrbit.Hyp t L E p := H.todd

theorem Hyp.m22
    : ∃ f : orb E t ≃ Fin 22, ∀ σ : Equiv.Perm (Fin 22), σ ∈ M22 ↔
    ∃ n ∈ normalizer (E : Set G), ∀ s : orb E t, (f.symm (σ (f s)) : G) = n * s * n⁻¹ := by
  obtain ⟨f, hf, -⟩ := H.exists_M22 toddRankBounds
  refine ⟨f, fun σ => ?_⟩
  rw [← hf]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, n.2, fun s => by rw [rhoF_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      coe_actHom_apply]⟩
  · rintro ⟨n, hn, hσ⟩
    refine ⟨⟨n, hn⟩, Equiv.ext fun i => f.symm.injective (Subtype.ext ?_)⟩
    have h := hσ (f.symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [rhoF_apply, Equiv.symm_apply_apply, coe_actHom_apply, h]

theorem Hyp.ker
    : ∀ n ∈ normalizer (E : Set G), (∀ s ∈ orb E t, n * s * n⁻¹ = s) → n ∈ E := by
  intro n hn hs
  obtain ⟨f, hf, -⟩ := H.exists_M22 toddRankBounds
  have h : (⟨n, hn⟩ : normalizer (E : Set G)) ∈ (rhoF f).ker := by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun i => ?_
    rw [rhoF_apply, Equiv.Perm.one_apply]
    have : actHom (⟨n, hn⟩ : normalizer (E : Set G)) (f.symm i) = f.symm i :=
      Subtype.ext (hs _ (f.symm i).2)
    rw [this, Equiv.apply_symm_apply]
  rw [H.ker_rhoF f hf.ge] at h
  exact mem_subgroupOf.1 h

end Main

section Classes

variable
    {G : Type} [Group G] [Finite G] {t : G} {L E : Subgroup G}
  {p : L →* Equiv.Perm (Fin 693)} (H : Hyp t L E p)
include H

theorem Hyp.transposition_class :
    ∃ a ∈ orb E t, a ≠ t ∧ pe p a = j1 ∧
      (∀ s : G, (IsConj t s ∧ s * t = t * s) ↔ s = t ∨ s ∈ lclass L a) ∧
      t ∉ lclass L a ∧ (∀ b ∈ lclass L a, b * t ∉ lclass L a) ∧ (lclass L a).ncard = 693 ∧
      ThreeTransposition.IsThreeTranspositionSet {y : L | (y : G) ∈ lclass L a} :=
  exists_transposition_class H.todd H.ds (H.centralizer_eq toddRankBounds)

omit [Finite G] in
theorem Hyp.mem_lclass_of_isConj
    {s : G} (hs : s ∈ L) (hst : IsConj t s) (hne : s ≠ t) {a : G}
    (hD : ∀ s : G, (IsConj t s ∧ s * t = t * s) ↔ s = t ∨ s ∈ lclass L a) : s ∈ lclass L a :=
  ((hD s).1 ⟨hst, H.todd.comm_t hs⟩).resolve_left hne

theorem Hyp.tv
    : ∀ s (hs : s ∈ L), IsConj t s → s ≠ t → ∃ m, p ⟨s, hs⟩ = tvP m := by
  intro s hs hst hne
  obtain ⟨a, ha, -, hpa, hD, -⟩ := H.transposition_class
  obtain ⟨m, hm⟩ := exists_pe_eq_tvP H.todd (H.todd.orb_subset_L ha) hpa
    (H.mem_lclass_of_isConj hs hst hne hD)
  exact ⟨m, by rw [← pe_of_mem p hs, hm]⟩

theorem Hyp.inj
    : ∀ s s' (hs : s ∈ L) (hs' : s' ∈ L), IsConj t s → IsConj t s' → s ≠ t →
    s' ≠ t → p ⟨s, hs⟩ = p ⟨s', hs'⟩ → s = s' := by
  intro s s' hs hs' hst hst' hne hne' e
  obtain ⟨a, -, -, -, hD, -, hbt, -⟩ := H.transposition_class
  have h1 := H.mem_lclass_of_isConj hs hst hne hD
  have h2 := H.mem_lclass_of_isConj hs' hst' hne' hD
  rw [← pe_of_mem p hs, ← pe_of_mem p hs'] at e
  rcases (H.todd.pe_eq_pe_iff hs hs').1 e.symm with h | h
  · exact h.symm
  · exact absurd (h ▸ h2) (hbt s h1)

theorem Hyp.card_sylow
    : ∀ P : Sylow 2 G, Nat.card P = 2 ^ 17 :=
  Hunt.card_sylow H.todd H.ds (H.centralizer_eq toddRankBounds) H.index_ne_two

theorem Hyp.card_sylowN
    : ∀ P : Sylow 2 (normalizer (E : Set G)), Nat.card P = 2 ^ 17 :=
  card_sylow_normalizer (H.card_normalizer toddRankBounds)

end Classes

end CFSG.EvenSmallLie.UnitarySix.Hunt
