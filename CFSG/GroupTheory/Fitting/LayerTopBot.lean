module

public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.WholeGroup

variable {G : Type*} [Group G]

theorem layer_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (layer A).map e.toMonoidHom = layer B := by
  have hbij := (LocalCores.component_isomorphism e).2
  change MulEquiv.mapSubgroup e (sSup {K : Subgroup A | IsComponent K}) = layer B
  rw [OrderIso.map_sSup, ← sSup_image]
  exact congrArg sSup hbij.image_eq

theorem layer_layer_eq_top : layer (layer G) = ⊤ := by
  have hle : layer G ≤ (layer (layer G)).map (layer G).subtype := by
    refine sSup_le fun K hK => ?_
    have hKl : K ≤ layer G := le_sSup hK
    have hc' : K.subgroupOf (layer G) ≤ layer (layer G) :=
      le_sSup (LocalCores.component_overgroup hK hKl)
    intro x hx
    exact ⟨⟨x, hKl hx⟩, hc' (show (⟨x, hKl hx⟩ : layer G) ∈ K.subgroupOf (layer G) from hx),
      rfl⟩
  refine top_unique fun y _ => ?_
  obtain ⟨z, hz, hzy⟩ := hle y.2
  rwa [Subtype.ext hzy] at hz

theorem layer_eq_top_of_isQuasisimple (h : IsQuasisimple G) : layer G = ⊤ :=
  eq_top_iff.2 (LocalCores.component_le_layer
    ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h, Subgroup.IsSubnormal.top⟩)

theorem layer_eq_bot_of_isSolvable [Group.IsSolvable G] : layer G = ⊥ := by
  by_contra hne
  have : Nontrivial (layer G) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have : Group.IsPerfect (layer G) := LocalCores.layer_isPerfect
  exact Group.IsPerfect.not_isSolvable (layer G) inferInstance

theorem layer_eq_top_of_isSimpleGroup [IsSimpleGroup G] (hG : ∃ a b : G, a * b ≠ b * a) :
    layer G = ⊤ :=
  LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => G) (fun _ => hG)
    (MulEquiv.piUnique fun _ : Unit => G).symm

theorem generalizedFitting_eq_fittingSubgroup_of_isSolvable [Group.IsSolvable G] :
    generalizedFitting G = fittingSubgroup G := by
  rw [generalizedFitting, layer_eq_bot_of_isSolvable, sup_bot_eq]

theorem center_layer_le_fittingSubgroup :
    (Subgroup.center (layer G)).map (layer G).subtype ≤ fittingSubgroup G := by
  have := LocalCores.layer_characteristic (G := G)
  have : ((Subgroup.center (layer G)).map (layer G).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have : Group.IsNilpotent ((Subgroup.center (layer G)).map (layer G).subtype) :=
    (Group.isNilpotent_congr ((Subgroup.center (layer G)).equivMapOfInjective
      (layer G).subtype (layer G).subtype_injective)).mp inferInstance
  exact le_sSup ⟨inferInstance, inferInstance⟩

theorem center_layer_eq_bot_of_solvableRadical_eq_bot (hG : solvableRadical G = ⊥) :
    (Subgroup.center (layer G)).map (layer G).subtype = ⊥ := by
  have := LocalCores.layer_characteristic (G := G)
  have hn : ((Subgroup.center (layer G)).map (layer G).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hs : Group.IsSolvable ((Subgroup.center (layer G)).map (layer G).subtype) :=
    Group.isSolvable_of_surjective (f := ((Subgroup.center (layer G)).equivMapOfInjective
      (layer G).subtype (layer G).subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  rw [← le_bot_iff, ← hG]
  exact le_sSup ⟨hn, hs⟩

theorem pCore_le_centralizer_layer [Finite G] (p : ℕ) [Fact p.Prime] :
    pCore p G ≤ Subgroup.centralizer (layer G : Set G) := by
  have hle : pCore p G ≤ fittingSubgroup G :=
    le_sSup ⟨pCore_normal, (pCore_isPGroup (p := p) (G := G)).isNilpotent⟩
  exact hle.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (LocalCores.fitting_layer_commute (G := G)))

theorem center_layer_le_pCore_of_pPrimeCore_eq_bot [Finite G] (p : ℕ) [Fact p.Prime]
    (hO : pPrimeCore p G = ⊥) :
    (Subgroup.center (layer G)).map (layer G).subtype ≤ pCore p G :=
  center_layer_le_fittingSubgroup.trans (Fitting_eq_pcore G p hO).le

theorem mem_centralizer_layer_of_mem_component [Finite G] {L : Subgroup G} (hL : IsComponent L)
    {a : G} (ha : a ∈ L) (hcen : ∀ w ∈ L, w * a = a * w) :
    a ∈ Subgroup.centralizer (layer G : Set G) := by
  have hle : layer G ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sSup_le fun K hK => ?_
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases LocalCores.distinct_components_commute hK hL with rfl | h
    · exact hcen k hk
    · exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk) a ha).symm
  exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem generalizedFitting_eq_top_of_isQuasisimple (h : IsQuasisimple G) :
    generalizedFitting G = ⊤ :=
  eq_top_iff.mpr (by rw [← layer_eq_top_of_isQuasisimple h]; exact le_sup_right)

theorem layer_eq_sup_others [Finite G] {S : Subgroup G} (hS : IsComponent S) :
    sSup {T : Subgroup G | IsComponent T ∧ T ≠ S} ≤ Subgroup.centralizer (S : Set G) ∧
      layer G = S ⊔ sSup {T : Subgroup G | IsComponent T ∧ T ≠ S} := by
  refine ⟨sSup_le fun T hT => Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((LocalCores.distinct_components_commute hT.1 hS).resolve_left hT.2), ?_⟩
  apply le_antisymm
  · refine sSup_le fun T hT => ?_
    by_cases h : T = S
    · rw [h]
      exact le_sup_left
    · exact le_sup_of_le_right (le_sSup ⟨hT, h⟩)
  · exact sup_le (LocalCores.component_le_layer hS)
      (sSup_le fun T hT => LocalCores.component_le_layer hT.1)

theorem fittingSubgroup_le_pCore_two_sup_oddCore [Finite G] :
    fittingSubgroup G ≤ pCore 2 G ⊔ oddCore G := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  by_cases hp : p.1.1 = 2
  · rw [hp]
    exact le_sup_left
  · refine le_sup_of_le_right (le_sSup ⟨pCore_normal, ?_⟩)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := p.1.1) (G := G))
    rw [hn]
    exact Odd.pow ((Nat.prime_of_mem_primeFactors p.1.2).odd_of_ne_two hp)

end CFSG.WholeGroup
