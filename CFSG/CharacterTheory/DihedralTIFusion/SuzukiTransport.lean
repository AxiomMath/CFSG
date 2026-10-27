module

public import CFSG.CharacterTheory.DihedralTIFusion.DegreeOnePair

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

theorem exists_degree_gap_representations {E : Type*} [Group E] [Finite E] {W : Subgroup E}
    (hWcyclic : IsCyclic W) (hWodd : Odd (Nat.card W)) (hWcard : 3 ≤ Nat.card W)
    (hcentralizer : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set E) = W) {u : E}
    (hu : orderOf u = 2) (huW : u ∉ W) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (hnormalizer : Subgroup.normalizer (W : Set E) = W ⊔ Subgroup.zpowers u) :
    ∃ (V U : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (_ : AddCommGroup U) (_ : Module ℂ U) (_ : FiniteDimensional ℂ U)
      (ρ : Representation ℂ E V) (σ : Representation ℂ E U),
      ρ.IsIrreducible ∧ σ.IsIrreducible ∧ ρ.character 1 = σ.character 1 + 1 ∧
      (∀ g ∉ ⋃ a : E, (fun x => a⁻¹ * x * a) '' ((W : Set E) \ {1}),
        ρ.character g - σ.character g - 1 = 0) ∧
      ∃ w ∈ W, ρ.character w - σ.character w - 1 ≠ 0 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  set e : Shrink.{0} E ≃* E := Shrink.mulEquiv with he
  have : Fintype (Shrink.{0} E) := Fintype.ofFinite _
  set W' : Subgroup (Shrink.{0} E) := W.comap e.toMonoidHom with hW'
  have hmemW' : ∀ x, x ∈ W' ↔ e x ∈ W := fun x => Subgroup.mem_comap
  set u' : Shrink.{0} E := e.symm u with hu'def
  have heu : e u' = u := e.apply_symm_apply u
  let eW : W' ≃* W :=
    { toFun := fun x => ⟨e x, (hmemW' x).mp x.2⟩
      invFun := fun y => ⟨e.symm y, (hmemW' _).mpr (by rw [e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (e.map_mul x y) }
  have hWcyclic' : IsCyclic W' := isCyclic_of_surjective eW.symm.toMonoidHom eW.symm.surjective
  have hcard' : Nat.card W' = Nat.card W := Nat.card_congr eW.toEquiv
  have hu' : orderOf u' = 2 := (orderOf_injective e.symm.toMonoidHom e.symm.injective u).trans hu
  have hu'W : u' ∉ W' := by
    rw [hmemW', heu]
    exact huW
  have hinvert' : ∀ w ∈ W', u'⁻¹ * w * u' = w⁻¹ := by
    intro w hw
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv, heu]
    exact hinvert _ ((hmemW' w).mp hw)
  have hu'2 : u' * u' = 1 := by rw [← pow_two, ← hu']; exact pow_orderOf_eq_one u'
  have hcentralizer' : ∀ w ∈ W', w ≠ 1 → Subgroup.centralizer ({w} : Set _) = W' := by
    intro w hw hw1
    have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (h.trans (map_one e).symm))
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, hmemW', ← hcentralizer (e w) ((hmemW' w).mp hw)
      hew1, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, e.injective.eq_iff]
  have hnormalizer' : Subgroup.normalizer (W' : Set _) = W' ⊔ Subgroup.zpowers u' := by
    ext g
    rw [mem_sup_zpowers_iff hu'2 hinvert' g, hmemW', hmemW', map_mul, heu,
      ← mem_sup_zpowers_iff hu2 hinvert (e g), ← hnormalizer, Subgroup.mem_set_normalizer_iff,
      Subgroup.mem_set_normalizer_iff]
    constructor
    · intro h m
      have hm := h (e.symm m)
      rw [SetLike.mem_coe, SetLike.mem_coe, hmemW', hmemW', map_mul, map_mul, map_inv,
        e.apply_symm_apply] at hm
      exact hm
    · intro h n
      have hn := h (e n)
      rw [SetLike.mem_coe, SetLike.mem_coe, hmemW', hmemW', map_mul, map_mul, map_inv]
      exact hn
  obtain ⟨⟨χ', hχ', ψ', hψ', -, hdeg', hsupp', w', hw'W, hw'⟩, -⟩ :=
    dihedral_TI_induction_degree_one_character_pair hWcyclic' (hcard' ▸ hWodd)
      (hcard' ▸ hWcard) hcentralizer' hu' hu'W hinvert' hnormalizer'
  obtain ⟨V, _, _, _, ρ', hρ', rfl⟩ := hχ'.1
  obtain ⟨U, _, _, _, σ', hσ', rfl⟩ := hψ'.1
  let ρ : Representation ℂ E V := ρ'.comp e.symm.toMonoidHom
  let σ : Representation ℂ E U := σ'.comp e.symm.toMonoidHom
  have hρchar : ∀ g : E, ρ.character g = ρ'.character (e.symm g) := fun g => rfl
  have hσchar : ∀ g : E, σ.character g = σ'.character (e.symm g) := fun g => rfl
  refine ⟨V, U, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ρ, σ,
    LyonsUnitaryFour.isIrreducible_comp_surjective _ e.symm.surjective ρ' hρ',
    LyonsUnitaryFour.isIrreducible_comp_surjective _ e.symm.surjective σ' hσ', ?_, ?_, ?_⟩
  · rw [hρchar, hσchar, map_one]
    exact hdeg'
  · intro g hg
    have hg' : e.symm g ∉ ⋃ a : Shrink.{0} E, (fun x => a⁻¹ * x * a) '' ((W' : Set _) \ {1}) := by
      intro hmem
      apply hg
      obtain ⟨a', ha'⟩ := mem_iUnion_conj_image_iff.mp hmem
      have hconj : e (a' * e.symm g * a'⁻¹) = e a' * g * (e a')⁻¹ := by
        rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
      refine mem_iUnion_conj_image_iff.mpr ⟨e a', ?_, ?_⟩
      · rw [← hconj]
        exact (hmemW' _).mp ha'.1
      · rw [← hconj]
        exact fun h1 => ha'.2 (e.injective (h1.trans (map_one e).symm))
    have h0 := hsupp' (e.symm g) hg'
    rw [hρchar, hσchar]
    simpa only [Pi.sub_apply, Pi.one_apply] using h0
  · refine ⟨e w', (hmemW' w').mp hw'W, ?_⟩
    rw [hρchar, hσchar, e.symm_apply_apply]
    simpa only [Pi.sub_apply, Pi.one_apply] using hw'

end CFSG.DihedralTIFusion
