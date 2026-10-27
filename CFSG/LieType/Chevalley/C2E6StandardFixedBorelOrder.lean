module

public import CFSG.LieType.Chevalley.C2E6StandardFixedTorus
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap

theorem card_orbitField (a : Fin TwistTag.E6.foldedTag.rank) :
    Nat.card (orbitField TwistTag.E6 K barHom a) =
      if (TwistTag.E6.orbit a).card = 1 then 2 else 4 := by
  rcases TwistTag.E6.card_orbit a with h | h
  · have e : orbitField TwistTag.E6 K barHom a ≃ {c : K // bar c = c} :=
      Equiv.subtypeEquivRight fun c => mem_orbitField_iff_of_card_eq_one h
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, h]
    decide
  · have htop : ∀ c, c ∈ orbitField TwistTag.E6 K barHom a := fun c => by
      rw [mem_orbitField, h, show TwistTag.E6.order = 2 from rfl, pow_two, RingHom.coe_mul,
        Function.comp_apply]
      exact bar_bar c
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv htop), Nat.card_eq_fintype_card, card_K, h]
    rfl

theorem card_rootSpan_orbit
    {O : Finset (Fin TwistTag.E6.tag.rank → ℤ)}
    (hO : O ∈ TwistTag.E6.diagramRootOrbits) :
    Nat.card ↥(rootSpan TwistTag.E6.tag K (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
      twistedFixedGroup TwistTag.E6 K barHom) = if O.card = 1 then 2 else 4 := by
  obtain ⟨α, hα, rfl⟩ := hO
  obtain ⟨w, hw, a, hOa, hcard, -⟩ := (diagram_root_orbit_reduction TwistTag.E6).1 α hα
  rw [hcard, hOa, Finset.coe_image,
    ← Nat.card_congr (orbitConjEquiv TwistTag.E6 barHom a hw).toEquiv,
    Nat.card_congr Multiplicative.toAdd, card_orbitField]

@[expose] def posOrbits : Finset (Finset (Fin TwistTag.E6.tag.rank → ℤ)) :=
  (Finset.univ.filter fun k : Fin 72 => 0 < height (e6Root k)).image
    fun k => TwistTag.E6.diagramOrbit (e6Root k)

theorem prod_posOrbits : ∏ O ∈ posOrbits, (if O.card = 1 then 2 else 4) = 2 ^ 36 := by
  decide +kernel

theorem card_posOrbits : posOrbits.card = 24 := by
  decide +kernel

abbrev posRootSet : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α}

theorem mem_posOrbits
    {O : Finset (Fin TwistTag.E6.tag.rank → ℤ)} :
    O ∈ posOrbits ↔ O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSet := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    have hk' := (Finset.mem_filter.mp hk).2
    refine ⟨⟨e6Root k, isRoot_e6Root k, rfl⟩, fun β hβ =>
      ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit (isRoot_e6Root k) hβ, ?_⟩⟩
    rw [TwistTag.E6.height_of_mem_diagramOrbit hβ]
    exact hk'
  · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hsub (TwistTag.E6.self_mem_diagramOrbit _)).2⟩, rfl⟩

@[expose] def posOrbitEnum (j : Fin posOrbits.card) : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  (posOrbits.equivFin.symm j).val

theorem posOrbitEnum_injective : Function.Injective posOrbitEnum :=
  fun _ _ h => posOrbits.equivFin.symm.injective (Subtype.ext h)

theorem range_posOrbitEnum :
    Set.range posOrbitEnum =
    {O | O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSet} := by
  ext O
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨j, rfl⟩
    exact mem_posOrbits.mp (posOrbits.equivFin.symm j).2
  · refine ⟨posOrbits.equivFin ⟨O, mem_posOrbits.mpr h⟩, ?_⟩
    rw [posOrbitEnum, Equiv.symm_apply_apply]

theorem posRootSet_perm :
    ∀ α ∈ posRootSet, permLattice TwistTag.E6.perm α ∈ posRootSet :=
  fun _ hα => ⟨hα.1.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hα.2⟩

theorem posRootSet_closed : ∀ α ∈ posRootSet, ∀ β ∈ posRootSet, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ posRootSet := by
  intro α hα β hβ a b ha hb hr
  refine ⟨hr, ?_⟩
  have e : height (a • α + b • β) = a * height α + b * height β := by
    simp only [height, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : (0 : ℤ) < a * height α := mul_pos (by exact_mod_cast ha) hα.2
  have h2 : (0 : ℤ) < b * height β := mul_pos (by exact_mod_cast hb) hβ.2
  rw [e]
  linarith

theorem card_stdUnipotent0
    : Nat.card stdUnipotent0 = 2 ^ 36 := by
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (fun α hα => hα) posRootSet_perm posRootSet_closed posOrbitEnum posOrbitEnum_injective
    range_posOrbitEnum
  have hmem : ∀ j, posOrbitEnum j ∈ TwistTag.E6.diagramRootOrbits := fun j =>
    (mem_posOrbits.mp (posOrbits.equivFin.symm j).2).1
  calc Nat.card stdUnipotent0
      = Nat.card (Set.univ : Set ((j : Fin posOrbits.card) →
          ↥(rootSpan TwistTag.E6.tag K (posOrbitEnum j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom))) := (Nat.card_congr hbij.equiv).symm
    _ = ∏ j, Nat.card ↥(rootSpan TwistTag.E6.tag K
          (posOrbitEnum j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom) := by
        rw [Nat.card_univ, Nat.card_pi]
    _ = ∏ j, (if (posOrbitEnum j).card = 1 then 2 else 4) :=
        Finset.prod_congr rfl fun j _ => card_rootSpan_orbit (hmem j)
    _ = ∏ O ∈ posOrbits, (if O.card = 1 then 2 else 4) := by
        rw [← Finset.prod_coe_sort posOrbits]
        exact Fintype.prod_equiv posOrbits.equivFin.symm _ _ fun j => rfl
    _ = 2 ^ 36 := prod_posOrbits

theorem card_stdBorel0
    : Nat.card stdBorel0 = Nat.card stdTorus0 * Nat.card stdUnipotent0 := by
  have hset := graphFixedBorel_eq_mul (t := TwistTag.E6) (K := K) (σ := barHom) barHom_surjective
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := triangular_borel_structure.{0, 0} Tag.E6 K
  let f : stdTorus0 × stdUnipotent0 → stdBorel0 := fun p => ⟨p.1 * p.2, by
    have h : (p.1 : ModGL Tag.E6 K) * p.2 ∈
        (graphFixedBorel TwistTag.E6 K barHom : Set (ModGL TwistTag.E6.tag K)) := by
      rw [hset]
      exact Set.mul_mem_mul p.1.2 p.2.2
    exact h⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun b => ?_⟩
    · obtain ⟨e1, e2⟩ := huniq _ p.1.2.1 _ q.1.2.1 _ p.2.2.1 _ q.2.2.1 (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
    · have hb : (b : ModGL Tag.E6 K) ∈
          (graphFixedBorel TwistTag.E6 K barHom : Set (ModGL TwistTag.E6.tag K)) := b.2
      rw [hset] at hb
      obtain ⟨h, hh, u, hu, hhu⟩ := hb
      exact ⟨(⟨h, hh⟩, ⟨u, hu⟩), Subtype.ext hhu⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

theorem card_stdBorel
    : Nat.card stdBorel = 3 * 2 ^ 36 := by
  rw [stdBorel_eq_stdBorel0, card_stdBorel0, card_stdTorus0, card_stdUnipotent0]

theorem standard_fixed_torus_and_borel_order :
    stdTorus0 = stdTorus ∧
    stdTorus0 = Subgroup.zpowers
      (torusElt Tag.E6 K (i6 2) omegaUnit * torusElt Tag.E6 K (i6 4) (omegaUnit ^ 2)) ∧
    Nat.card stdTorus0 = 3 ∧
    stdTorus0 ≤ groupA ⊓ groupD ∧
    stdFixedGroup = stdGroup ∧
    stdBorel = stdBorel0 ∧
    Nat.card stdUnipotent0 = 2 ^ 36 ∧
    Nat.card stdBorel = 3 * 2 ^ 36 ∧ 3 * 2 ^ 36 = 206158430208 ∧
    (∀ h : ModGL Tag.E6 K, h ∈ torusGroup Tag.E6 K ↔ ∃ c : Fin 6 → ZMod 3, h = torusWord i6 c) ∧
    (∀ h : ModGL Tag.E6 K, h ∈ stdTorus0 ↔
      ∃ a b : ZMod 3, h = torusWord i6 ![a, 0, b, 0, 2 * b, 2 * a]) ∧
    (∀ c : Fin 6 → ZMod 3,
      torusWord i6 c ∈ stdTorus0 ↔ ∃ a b : ZMod 3, c = ![a, 0, b, 0, 2 * b, 2 * a]) ∧
    (∀ c d : Fin 6 → ZMod 3, torusWord i6 c = torusWord i6 d ↔
      c - d = 0 ∨ c - d = ![1, 0, 2, 0, 1, 2] ∨ c - d = ![2, 0, 1, 0, 2, 1]) :=
  ⟨stdTorus0_eq_stdTorus, stdTorus0_eq_zpowers, card_stdTorus0, stdTorus0_le_groupA_inf_groupD,
    stdFixedGroup_eq_stdGroup, stdBorel_eq_stdBorel0, card_stdUnipotent0, card_stdBorel,
    by norm_num, fun _ => mem_torusGroup_iff, fun _ => mem_stdTorus0_iff,
    torusWord_mem_stdTorus0_iff, torusWord6_eq_iff⟩

end CFSG.LieType.Chevalley.C2E6Std
