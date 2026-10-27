module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Vec
public import CFSG.Monster.B.E6.StdF4FiberCount
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer
import all CFSG.Fischer.F4
public import Certificates.Data.TabBThreeL1

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Fischer
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Overlap (K bar bar_bar barHom barHom_apply)

@[expose] def orbAt (j : Fin 15) : ℕ × ℕ := orbs.getD j (0, 0)

theorem orbAt_mem : ∀ j : Fin 15, orbAt j ∈ orbs := by decide

@[expose] def labRoot (a : ℕ) : Fin Tag.E6.rank → ℤ := e6Certificate.root (a - 6)

theorem orbs_facts : ∀ o ∈ orbs, 6 ≤ o.1 ∧ o.1 < 78 ∧ 6 ≤ o.2 ∧ o.2 < 78 ∧
    0 < height (labRoot o.1) ∧
    (o.1 = o.2 → permLattice (τ := Tag.E6) TwistTag.E6.perm (labRoot o.1) = labRoot o.1) ∧
    (o.1 ≠ o.2 → permLattice (τ := Tag.E6) TwistTag.E6.perm (labRoot o.1) = labRoot o.2) ∧
    (o.1 ≠ o.2 → labRoot o.1 ≠ labRoot o.2) := by
  decide +kernel

@[expose] def orbEnum (j : Fin 15) : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  TwistTag.E6.diagramOrbit (labRoot (orbAt j).1)

theorem image_orbEnum : Finset.univ.image orbEnum = fibOrbits 0 := by
  decide +kernel

theorem orbEnum_injective : Function.Injective orbEnum := by
  decide +kernel

@[expose] def ofK (c : K) : F4 := c

theorem toK_ofK (c : K) : toK (ofK c) = c := rfl

theorem eq_zero_or_one_of_bar_eq : ∀ c : K, bar c = c → c = 0 ∨ c = 1 := by
  decide

theorem bar_mul_bar : ∀ c : K, bar c * bar c = c := by
  decide

theorem twistHom_pinnedX_bar {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (c : K) : twistHom TwistTag.E6 K barHom (pinnedX TwistTag.E6.tag K α c) =
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) (bar c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.E6 hα
  have hσ : Units.map (entrywiseHom barHom) (pinnedX TwistTag.E6.tag K α c) =
      pinnedX TwistTag.E6.tag K α (barHom c) :=
    Units.ext (entrywise_pinnedX barHom α c)
  rw [twistHom_apply, hσ, h, eq_one_of_mul_self_eq_one_of_two_eq_zero CharTwo.two_eq_zero hε,
    one_mul, barHom_apply]

theorem permLattice_perm_perm (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm v) = v := by
  funext j
  simp only [permLattice, Function.comp_apply]
  congr 1
  revert j
  decide

theorem commute_pinnedX_perm {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hρ : permLattice TwistTag.E6.perm α ≠ α) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c)
      (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) d) := by
  have hmem := TwistTag.E6.permLattice_mem_diagramOrbit (TwistTag.E6.self_mem_diagramOrbit α)
  have hnr := TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hα
    (TwistTag.E6.self_mem_diagramOrbit α) hmem (le_refl 1) (le_refl 1)
  rw [one_smul, one_smul] at hnr
  have hne' : α ≠ -permLattice TwistTag.E6.perm α := fun e => by
    have h1 := congrArg height e
    rw [height_neg, height_permLattice] at h1
    rcases IsRoot.height_pos_or_neg hα with h2 | h2 <;> omega
  exact (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag (Or.inr (Or.inl rfl)) hα
    (hα.permLattice TwistTag.E6.cartan_perm) (Ne.symm hρ) hne').2 hnr K _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem eq_orbitElt {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hαp : 0 < height α) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K barHom) :
    (permLattice TwistTag.E6.perm α = α ∧ ∃ c : K, (c = 0 ∨ c = 1) ∧
        u = pinnedX TwistTag.E6.tag K α c) ∨
      (permLattice TwistTag.E6.perm α ≠ α ∧ ∃ c : K, u = pinnedX TwistTag.E6.tag K α c *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) (c * c)) := by
  obtain ⟨huS, huΓ⟩ := Subgroup.mem_inf.1 hu
  have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1 huΓ).2
  by_cases hρ : permLattice TwistTag.E6.perm α = α
  · rw [diagramOrbit_eq_singleton_of_fixed hρ, Finset.coe_singleton, rootSpan_singleton] at huS
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 huS
    rw [twistHom_pinnedX_bar hα, hρ] at hfix
    exact Or.inl ⟨hρ, c, eq_zero_or_one_of_bar_eq c (pinnedX_injective TwistTag.E6.tag K α hfix),
      rfl⟩
  · right
    have hβ : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) :=
      hα.permLattice TwistTag.E6.cartan_perm
    have hβh : height (permLattice TwistTag.E6.perm α) = height α := height_permLattice _ _
    have hmemO : ∀ γ, γ ∈ [α, permLattice TwistTag.E6.perm α] ↔
        γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) := by
      intro γ
      simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_coe]
      constructor
      · rintro (rfl | rfl)
        · exact TwistTag.E6.self_mem_diagramOrbit _
        · exact TwistTag.E6.permLattice_mem_diagramOrbit (TwistTag.E6.self_mem_diagramOrbit _)
      · intro hγ
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ
        rw [Finset.mem_range, show TwistTag.E6.order = 2 from rfl] at hj
        interval_cases j
        · exact Or.inl rfl
        · exact Or.inr (by rw [pow_one])
    have hS : ∀ γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        IsRoot TwistTag.E6.tag γ ∧ 0 < height γ := fun γ hγ =>
      ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit hα hγ,
        by rw [TwistTag.E6.height_of_mem_diagramOrbit hγ]; exact hαp⟩
    have hcl : ∀ γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        ∀ δ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)), ∀ a b : ℕ,
          1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • γ + b • δ) →
            a • γ + b • δ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) :=
      fun γ hγ δ hδ a b ha hb hr =>
        absurd hr (TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hα hγ hδ ha hb)
    have hnd : [α, permLattice TwistTag.E6.perm α].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        and_true]
      exact ⟨Ne.symm hρ, not_false⟩
    obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq K hS hcl hnd hmemO huS
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
    subst hc
    rw [map_mul, twistHom_pinnedX_bar hα, twistHom_pinnedX_bar hβ, permLattice_perm_perm,
      ← (commute_pinnedX_perm hα hρ _ _).eq] at hfix
    have hX : ∀ d : K, pinnedX TwistTag.E6.tag K α d ∈ heightSeries TwistTag.E6.tag K (height α) :=
      fun d => pinnedX_mem_heightSeries_height ⟨hα, hαp⟩ d
    have hY : ∀ d : K, pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) d ∈
        heightSeries TwistTag.E6.tag K (height α) := fun d =>
      pinnedX_mem_rootSpan (S := {γ | IsRoot TwistTag.E6.tag γ ∧ 0 < height γ ∧
        height α ≤ height γ}) ⟨hβ, by rw [hβh]; exact hαp, hβh.ge⟩ d
    have hc' := congrArg (rootCoord ⟨hα, hαp⟩) hfix
    rw [rootCoord_mul _ (hX _) (hY _), rootCoord_mul _ (hX _) (hY _), rootCoord_self,
      rootCoord_self, rootCoord_pinnedX_of_ne _ ⟨hβ, by rw [hβh]; exact hαp⟩ hβh.ge hρ,
      rootCoord_pinnedX_of_ne _ ⟨hβ, by rw [hβh]; exact hαp⟩ hβh.ge hρ, add_zero,
      add_zero] at hc'
    refine ⟨hρ, c α, ?_⟩
    rw [← hc', bar_mul_bar]

@[expose] noncomputable def yElt (o : ℕ × ℕ) (c : F4) : ModGL Tag.E6 K :=
  if o.1 = o.2 then pinnedX Tag.E6 K (labRoot o.1) (toK c)
  else pinnedX Tag.E6 K (labRoot o.1) (toK c) * pinnedX Tag.E6 K (labRoot o.2) (toK (c * c))

theorem fibV_zero_eq : fibV 0 = stdRadical firstJ := by
  have h1 : Nat.card (stdRadical firstJ) = 2 ^ 21 := card_stdRadical_firstJ
  have : Finite (stdRadical firstJ) := Nat.finite_of_card_ne_zero (by rw [h1]; positivity)
  refine Subgroup.eq_of_le_of_card_ge (fibV_le_stdRadical 0) ?_
  rw [h1, card_fibV]
  rfl

theorem range_orbEnum : Set.range orbEnum =
    {O | O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ fibRoots 0} := by
  ext O
  rw [Set.mem_setOf_eq, ← mem_fibOrbits, ← image_orbEnum, Finset.mem_image]
  simp only [Finset.mem_univ, true_and, Set.mem_range]

theorem exists_param_of_mem {j : Fin 15} {u : ModGL Tag.E6 K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (orbEnum j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
      twistedFixedGroup TwistTag.E6 K barHom) :
    ∃ c : F4, c ∈ choices (orbAt j) ∧ u = yElt (orbAt j) c := by
  obtain ⟨h1, h1', -, -, hpos, hfix, hpair, hne⟩ := orbs_facts (orbAt j) (orbAt_mem j)
  have hα : IsRoot TwistTag.E6.tag (labRoot (orbAt j).1) := isRoot_certRoot (by omega)
  rcases eq_orbitElt hα hpos hu with ⟨hρ, c, hc, rfl⟩ | ⟨hρ, c, rfl⟩
  · have ho : (orbAt j).1 = (orbAt j).2 := by
      by_contra h
      exact hne h ((hpair h).symm.trans hρ).symm
    refine ⟨ofK c, ?_, ?_⟩
    · rw [choices, if_pos ho]
      rcases hc with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [yElt, if_pos ho, toK_ofK]
      rfl
  · have ho : (orbAt j).1 ≠ (orbAt j).2 := fun h => hρ (hfix h)
    refine ⟨ofK c, ?_, ?_⟩
    · rw [choices, if_neg ho]
      rcases F4_cases (ofK c) with h | h | h | h <;> rw [h] <;> simp
    · rw [yElt, if_neg ho, toK_ofK, ← hpair ho]
      rfl

theorem exists_params_of_mem_stdRadical {u : ModGL Tag.E6 K} (hu : u ∈ stdRadical firstJ) :
    ∃ cs : Fin 15 → F4, (∀ j, cs j ∈ choices (orbAt j)) ∧
      u = (List.ofFn fun j => yElt (orbAt j) (cs j)).prod := by
  rw [← fibV_zero_eq] at hu
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (fun α hα => ⟨hα.1, hα.2.1⟩) (fibRoots_perm 0) (fibRoots_closed 0) orbEnum orbEnum_injective
    range_orbEnum
  obtain ⟨f, -, hf⟩ := hbij.surjOn hu
  choose cs hcs hcs' using fun j => exists_param_of_mem (f j).2
  exact ⟨cs, hcs, by rw [← hf]; exact congrArg (fun g => (List.ofFn g).prod) (funext hcs')⟩

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1
