module

public import CFSG.LieType.Chevalley.C2E6FirstResidueLevi
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
open scoped Pointwise

abbrev posRootSetA : Set (Fin TwistTag.E6.tag.rank → ℤ) := parabolicPosRoots Tag.E6 setA

@[expose] def posOrbitsA : Finset (Finset (Fin TwistTag.E6.tag.rank → ℤ)) :=
  (Finset.univ.filter fun k : Fin 72 => 0 < height (e6Root k) ∧ e6Root k (i6 1) = 0).image
    fun k => TwistTag.E6.diagramOrbit (e6Root k)

theorem prod_posOrbitsA : ∏ O ∈ posOrbitsA, (if O.card = 1 then 2 else 4) = 2 ^ 15 := by
  decide +kernel

theorem diagramOrbit_apply_i6_one : ∀ k : Fin 72, ∀ β ∈ TwistTag.E6.diagramOrbit (e6Root k),
    β (i6 1) = e6Root k (i6 1) := by
  decide +kernel

theorem mem_posRootSetA {α : Fin TwistTag.E6.tag.rank → ℤ} :
    α ∈ posRootSetA ↔ IsRoot Tag.E6 α ∧ 0 < height α ∧ α (i6 1) = 0 := by
  constructor
  · rintro ⟨⟨hr, hA⟩, -, hpos⟩
    exact ⟨hr, hpos, hA _ ((not_mem_setA_iff _).mpr rfl)⟩
  · rintro ⟨hr, hpos, h1⟩
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, hpos⟩
    rw [(not_mem_setA_iff i).mp hi]
    exact h1

theorem mem_posOrbitsA
    {O : Finset (Fin TwistTag.E6.tag.rank → ℤ)} :
    O ∈ posOrbitsA ↔ O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSetA := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    have hk' := (Finset.mem_filter.mp hk).2
    refine ⟨⟨e6Root k, isRoot_e6Root k, rfl⟩, fun β hβ => mem_posRootSetA.mpr
      ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit (isRoot_e6Root k) hβ, ?_, ?_⟩⟩
    · rw [TwistTag.E6.height_of_mem_diagramOrbit hβ]
      exact hk'.1
    · rw [diagramOrbit_apply_i6_one k β hβ]
      exact hk'.2
  · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
    have h := mem_posRootSetA.mp (hsub (TwistTag.E6.self_mem_diagramOrbit _))
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.1, h.2.2⟩, rfl⟩

@[expose] def posOrbitEnumA (j : Fin posOrbitsA.card) :
    Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  (posOrbitsA.equivFin.symm j).val

theorem posOrbitEnumA_injective : Function.Injective posOrbitEnumA :=
  fun _ _ h => posOrbitsA.equivFin.symm.injective (Subtype.ext h)

theorem range_posOrbitEnumA :
    Set.range posOrbitEnumA =
    {O | O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSetA} := by
  ext O
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨j, rfl⟩
    exact mem_posOrbitsA.mp (posOrbitsA.equivFin.symm j).2
  · refine ⟨posOrbitsA.equivFin ⟨O, mem_posOrbitsA.mpr h⟩, ?_⟩
    rw [posOrbitEnumA, Equiv.symm_apply_apply]

theorem perm_symm_i6_one :
    TwistTag.E6.perm.symm (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) = ⟨1, by decide⟩ := by
  decide

theorem posRootSetA_perm
    : ∀ α ∈ posRootSetA, permLattice TwistTag.E6.perm α ∈ posRootSetA := by
  intro α hα
  obtain ⟨hr, hpos, h1⟩ := mem_posRootSetA.mp hα
  refine mem_posRootSetA.mpr ⟨hr.permLattice TwistTag.E6.cartan_perm, ?_, ?_⟩
  · rw [height_permLattice]
    exact hpos
  · change α (TwistTag.E6.perm.symm (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank)) = 0
    rw [perm_symm_i6_one]
    exact h1

theorem posRootSetA_closed : ∀ α ∈ posRootSetA, ∀ β ∈ posRootSetA, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ posRootSetA := by
  intro α hα β hβ a b ha hb hr
  obtain ⟨-, hαpos, hα1⟩ := mem_posRootSetA.mp hα
  obtain ⟨-, hβpos, hβ1⟩ := mem_posRootSetA.mp hβ
  refine mem_posRootSetA.mpr ⟨hr, ?_, ?_⟩
  · have e : height (a • α + b • β) = a * height α + b * height β := by
      simp only [height, Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum, nsmul_eq_mul,
        Pi.mul_apply, Pi.natCast_apply]
    have h1 : (0 : ℤ) < a * height α := mul_pos (by exact_mod_cast ha) hαpos
    have h2 : (0 : ℤ) < b * height β := mul_pos (by exact_mod_cast hb) hβpos
    rw [e]
    linarith
  · change a • α (i6 1) + b • β (i6 1) = 0
    rw [hα1, hβ1, smul_zero, smul_zero, add_zero]

theorem card_stdLeviUnipotent_firstJ
    : Nat.card (stdLeviUnipotent firstJ) = 2 ^ 15 := by
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (fun α hα => (mem_posRootSetA.mp hα).1 |> fun h => ⟨h, (mem_posRootSetA.mp hα).2.1⟩)
    posRootSetA_perm posRootSetA_closed posOrbitEnumA posOrbitEnumA_injective
    range_posOrbitEnumA
  have hmem : ∀ j, posOrbitEnumA j ∈ TwistTag.E6.diagramRootOrbits := fun j =>
    (mem_posOrbitsA.mp (posOrbitsA.equivFin.symm j).2).1
  have e : stdLeviUnipotent firstJ =
      rootSpan TwistTag.E6.tag K posRootSetA ⊓ twistedFixedGroup TwistTag.E6 K barHom := by
    rw [stdLeviUnipotent_firstJ]
    rfl
  rw [e]
  calc Nat.card ↥(rootSpan TwistTag.E6.tag K posRootSetA ⊓ twistedFixedGroup TwistTag.E6 K barHom)
      = Nat.card (Set.univ : Set ((j : Fin posOrbitsA.card) →
          ↥(rootSpan TwistTag.E6.tag K (posOrbitEnumA j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom))) := (Nat.card_congr hbij.equiv).symm
    _ = ∏ j, Nat.card ↥(rootSpan TwistTag.E6.tag K
          (posOrbitEnumA j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom) := by
        rw [Nat.card_univ, Nat.card_pi]
    _ = ∏ j, (if (posOrbitEnumA j).card = 1 then 2 else 4) :=
        Finset.prod_congr rfl fun j _ => card_rootSpan_orbit (hmem j)
    _ = ∏ O ∈ posOrbitsA, (if O.card = 1 then 2 else 4) := by
        rw [← Finset.prod_coe_sort posOrbitsA]
        exact Fintype.prod_equiv posOrbitsA.equivFin.symm _ _ fun j => rfl
    _ = 2 ^ 15 := prod_posOrbitsA

theorem stdLeviUnipotent_firstJ_le_posUnipotent :
    stdLeviUnipotent firstJ ≤ posUnipotent Tag.E6 K := by
  rw [stdLeviUnipotent_firstJ]
  exact inf_le_left.trans (rootSpan_le_posUnipotent fun α hα =>
    ⟨(mem_posRootSetA.mp hα).1, (mem_posRootSetA.mp hα).2.1⟩)

theorem card_stdLeviBorel_firstJ
    : Nat.card (stdLeviBorel firstJ) = 3 * 2 ^ 15 := by
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := triangular_borel_structure.{0, 0} Tag.E6 K
  have hset := coe_stdLeviBorel firstJ
  let f : stdTorus × stdLeviUnipotent firstJ → stdLeviBorel firstJ := fun p => ⟨p.1 * p.2, by
    have h : (p.1 : ModGL Tag.E6 K) * p.2 ∈ (stdLeviBorel firstJ : Set (ModGL Tag.E6 K)) := by
      rw [hset]
      exact Set.mul_mem_mul p.1.2 p.2.2
    exact h⟩
  have hT : ∀ t : stdTorus, (t : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K := fun t =>
    (stdTorus0_eq_stdTorus.symm.le t.2).1
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun b => ?_⟩
    · obtain ⟨e1, e2⟩ := huniq _ (hT p.1) _ (hT q.1) _
        (stdLeviUnipotent_firstJ_le_posUnipotent p.2.2) _
        (stdLeviUnipotent_firstJ_le_posUnipotent q.2.2) (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
    · have hb : (b : ModGL Tag.E6 K) ∈ (stdLeviBorel firstJ : Set (ModGL Tag.E6 K)) := b.2
      rw [hset] at hb
      obtain ⟨h, hh, u, hu, hhu⟩ := hb
      exact ⟨(⟨h, hh⟩, ⟨u, hu⟩), Subtype.ext hhu⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_stdLeviUnipotent_firstJ,
    ← stdTorus0_eq_stdTorus, card_stdTorus0]

end CFSG.LieType.Chevalley.C2E6Std
