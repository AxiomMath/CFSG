module

public import CFSG.LieType.Chevalley.C2E6FourthResidueRestriction
public import CFSG.LieType.Chevalley.C2E6FirstResidueGeometry
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Chevalley.CosetBuilding
open scoped Pointwise commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev posRootSetD : Set (Fin TwistTag.E6.tag.rank → ℤ) := parabolicPosRoots Tag.E6 setD

@[expose] def posOrbitsD : Finset (Finset (Fin TwistTag.E6.tag.rank → ℤ)) :=
  (Finset.univ.filter fun k : Fin 72 =>
      0 < height (e6Root k) ∧ e6Root k (i6 0) = 0 ∧ e6Root k (i6 5) = 0).image
    fun k => TwistTag.E6.diagramOrbit (e6Root k)

theorem prod_posOrbitsD : ∏ O ∈ posOrbitsD, (if O.card = 1 then 2 else 4) = 2 ^ 12 := by
  decide +kernel

theorem diagramOrbit_apply_zero_five : ∀ k : Fin 72, ∀ β ∈ TwistTag.E6.diagramOrbit (e6Root k),
    (β (i6 0) = 0 ∧ β (i6 5) = 0) ↔ (e6Root k (i6 0) = 0 ∧ e6Root k (i6 5) = 0) := by
  decide +kernel

theorem mem_posRootSetD {α : Fin TwistTag.E6.tag.rank → ℤ} :
    α ∈ posRootSetD ↔ IsRoot Tag.E6 α ∧ 0 < height α ∧ α (i6 0) = 0 ∧ α (i6 5) = 0 := by
  constructor
  · rintro ⟨⟨hr, hD⟩, -, hpos⟩
    exact ⟨hr, hpos, hD _ ((not_mem_setD_iff _).mpr (Or.inl rfl)),
      hD _ ((not_mem_setD_iff _).mpr (Or.inr rfl))⟩
  · rintro ⟨hr, hpos, h0, h5⟩
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, hpos⟩
    rcases (not_mem_setD_iff i).mp hi with rfl | rfl
    exacts [h0, h5]

theorem mem_posOrbitsD
    {O : Finset (Fin TwistTag.E6.tag.rank → ℤ)} :
    O ∈ posOrbitsD ↔ O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSetD := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    have hk' := (Finset.mem_filter.mp hk).2
    refine ⟨⟨e6Root k, isRoot_e6Root k, rfl⟩, fun β hβ => mem_posRootSetD.mpr
      ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit (isRoot_e6Root k) hβ, ?_,
        ((diagramOrbit_apply_zero_five k β hβ).mpr hk'.2).1,
        ((diagramOrbit_apply_zero_five k β hβ).mpr hk'.2).2⟩⟩
    rw [TwistTag.E6.height_of_mem_diagramOrbit hβ]
    exact hk'.1
  · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
    have h := mem_posRootSetD.mp (hsub (TwistTag.E6.self_mem_diagramOrbit _))
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩, rfl⟩

@[expose] def posOrbitEnumD (j : Fin posOrbitsD.card) :
    Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  (posOrbitsD.equivFin.symm j).val

theorem posOrbitEnumD_injective : Function.Injective posOrbitEnumD :=
  fun _ _ h => posOrbitsD.equivFin.symm.injective (Subtype.ext h)

theorem range_posOrbitEnumD :
    Set.range posOrbitEnumD =
    {O | O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSetD} := by
  ext O
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨j, rfl⟩
    exact mem_posOrbitsD.mp (posOrbitsD.equivFin.symm j).2
  · refine ⟨posOrbitsD.equivFin ⟨O, mem_posOrbitsD.mpr h⟩, ?_⟩
    rw [posOrbitEnumD, Equiv.symm_apply_apply]

theorem perm_symm_i6_zero : TwistTag.E6.perm.symm (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) =
    ⟨5, by decide⟩ := by
  decide

theorem perm_symm_i6_five : TwistTag.E6.perm.symm (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) =
    ⟨0, by decide⟩ := by
  decide

theorem posRootSetD_perm
    : ∀ α ∈ posRootSetD, permLattice TwistTag.E6.perm α ∈ posRootSetD := by
  intro α hα
  obtain ⟨hr, hpos, h0, h5⟩ := mem_posRootSetD.mp hα
  refine mem_posRootSetD.mpr ⟨hr.permLattice TwistTag.E6.cartan_perm, ?_, ?_, ?_⟩
  · rw [height_permLattice]
    exact hpos
  · change α (TwistTag.E6.perm.symm (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank)) = 0
    rw [perm_symm_i6_zero]
    exact h5
  · change α (TwistTag.E6.perm.symm (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank)) = 0
    rw [perm_symm_i6_five]
    exact h0

theorem posRootSetD_closed : ∀ α ∈ posRootSetD, ∀ β ∈ posRootSetD, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ posRootSetD := by
  intro α hα β hβ a b ha hb hr
  obtain ⟨-, hαpos, hα0, hα5⟩ := mem_posRootSetD.mp hα
  obtain ⟨-, hβpos, hβ0, hβ5⟩ := mem_posRootSetD.mp hβ
  refine mem_posRootSetD.mpr ⟨hr, ?_, ?_, ?_⟩
  · have e : height (a • α + b • β) = a * height α + b * height β := by
      simp only [height, Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum, nsmul_eq_mul,
        Pi.mul_apply, Pi.natCast_apply]
    have h1 : (0 : ℤ) < a * height α := mul_pos (by exact_mod_cast ha) hαpos
    have h2 : (0 : ℤ) < b * height β := mul_pos (by exact_mod_cast hb) hβpos
    rw [e]
    linarith
  · change a • α (i6 0) + b • β (i6 0) = 0
    rw [hα0, hβ0, smul_zero, smul_zero, add_zero]
  · change a • α (i6 5) + b • β (i6 5) = 0
    rw [hα5, hβ5, smul_zero, smul_zero, add_zero]

theorem card_stdLeviUnipotent_fourthJ
    : Nat.card (stdLeviUnipotent fourthJ) = 2 ^ 12 := by
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (fun α hα => (mem_posRootSetD.mp hα).1 |> fun h => ⟨h, (mem_posRootSetD.mp hα).2.1⟩)
    posRootSetD_perm posRootSetD_closed posOrbitEnumD posOrbitEnumD_injective
    range_posOrbitEnumD
  have hmem : ∀ j, posOrbitEnumD j ∈ TwistTag.E6.diagramRootOrbits := fun j =>
    (mem_posOrbitsD.mp (posOrbitsD.equivFin.symm j).2).1
  have e : stdLeviUnipotent fourthJ =
      rootSpan TwistTag.E6.tag K posRootSetD ⊓ twistedFixedGroup TwistTag.E6 K barHom := by
    rw [stdLeviUnipotent_fourthJ]
    rfl
  rw [e]
  calc Nat.card ↥(rootSpan TwistTag.E6.tag K posRootSetD ⊓ twistedFixedGroup TwistTag.E6 K barHom)
      = Nat.card (Set.univ : Set ((j : Fin posOrbitsD.card) →
          ↥(rootSpan TwistTag.E6.tag K (posOrbitEnumD j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom))) := (Nat.card_congr hbij.equiv).symm
    _ = ∏ j, Nat.card ↥(rootSpan TwistTag.E6.tag K
          (posOrbitEnumD j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom) := by
        rw [Nat.card_univ, Nat.card_pi]
    _ = ∏ j, (if (posOrbitEnumD j).card = 1 then 2 else 4) :=
        Finset.prod_congr rfl fun j _ => card_rootSpan_orbit (hmem j)
    _ = ∏ O ∈ posOrbitsD, (if O.card = 1 then 2 else 4) := by
        rw [← Finset.prod_coe_sort posOrbitsD]
        exact Fintype.prod_equiv posOrbitsD.equivFin.symm _ _ fun j => rfl
    _ = 2 ^ 12 := prod_posOrbitsD

theorem stdLeviUnipotent_fourthJ_le_posUnipotent :
    stdLeviUnipotent fourthJ ≤ posUnipotent Tag.E6 K := by
  rw [stdLeviUnipotent_fourthJ]
  exact inf_le_left.trans (rootSpan_le_posUnipotent fun α hα =>
    ⟨(mem_posRootSetD.mp hα).1, (mem_posRootSetD.mp hα).2.1⟩)

theorem card_stdLeviBorel_fourthJ
    : Nat.card (stdLeviBorel fourthJ) = 3 * 2 ^ 12 := by
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := triangular_borel_structure.{0, 0} Tag.E6 K
  have hset := coe_stdLeviBorel fourthJ
  let f : stdTorus × stdLeviUnipotent fourthJ → stdLeviBorel fourthJ := fun p => ⟨p.1 * p.2, by
    have h : (p.1 : ModGL Tag.E6 K) * p.2 ∈ (stdLeviBorel fourthJ : Set (ModGL Tag.E6 K)) := by
      rw [hset]
      exact Set.mul_mem_mul p.1.2 p.2.2
    exact h⟩
  have hT : ∀ t : stdTorus, (t : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K := fun t =>
    (stdTorus0_eq_stdTorus.symm.le t.2).1
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun b => ?_⟩
    · obtain ⟨e1, e2⟩ := huniq _ (hT p.1) _ (hT q.1) _
        (stdLeviUnipotent_fourthJ_le_posUnipotent p.2.2) _
        (stdLeviUnipotent_fourthJ_le_posUnipotent q.2.2) (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
    · have hb : (b : ModGL Tag.E6 K) ∈ (stdLeviBorel fourthJ : Set (ModGL Tag.E6 K)) := b.2
      rw [hset] at hb
      obtain ⟨h, hh, u, hu, hhu⟩ := hb
      exact ⟨(⟨h, hh⟩, ⟨u, hu⟩), Subtype.ext hhu⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_stdLeviUnipotent_fourthJ,
    ← stdTorus0_eq_stdTorus, card_stdTorus0]

@[expose] def chamberOf
    (J : Set (Fin 4)) : ParabolicCosets J → stdChamber :=
  Quotient.lift (fun p : nativeParabolic J =>
    ((⟨p, nativeParabolic_le_stdGroup _ p.2⟩ : stdGroup) : stdChamber)) fun x y hxy => by
    have h : x⁻¹ * y ∈ stdBorel.subgroupOf (nativeParabolic J) :=
      QuotientGroup.leftRel_apply.mp hxy
    exact QuotientGroup.eq.mpr h

theorem chamberOf_mk
    (J : Set (Fin 4)) (p : nativeParabolic J) :
    chamberOf J (QuotientGroup.mk p) =
      ((⟨p, nativeParabolic_le_stdGroup _ p.2⟩ : stdGroup) : stdChamber) :=
  rfl

theorem chamberOf_injective
    (J : Set (Fin 4)) : Function.Injective (chamberOf J) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [chamberOf_mk, chamberOf_mk, QuotientGroup.eq] at hxy
  exact QuotientGroup.eq.mpr hxy

theorem range_chamberOf
    (J : Set (Fin 4)) : Set.range (chamberOf J) =
    residue nativeCoxeterSystem stdDistance J ((1 : stdGroup) : stdChamber) := by
  rw [residue_stdDistance, one_smul]
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with | H x => ?_
    exact ⟨⟨x, nativeParabolic_le_stdGroup _ x.2⟩, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩

theorem fourthJ_eq : fourthJ = {i : Fin 4 | (i : ℕ) ≠ 3} := by
  ext i
  fin_cases i <;> simp [fourthJ]

theorem card_parabolicCosets_fourthJ
    : Nat.card (ParabolicCosets fourthJ) = 16065 := by
  rw [← Set.ncard_range_of_injective (chamberOf_injective _), range_chamberOf, fourthJ_eq]
  exact ncard_residue_compl_stdDistance.2.2.2 _

theorem card_stdLevi_fourthJ
    : Nat.card (stdLevi fourthJ) = 197406720 := by
  rw [← ((stdLeviBorel fourthJ).subgroupOf (stdLevi fourthJ)).index_mul_card, Subgroup.index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (stdLeviBorel_le_stdLevi two_mem_fourthJ)).toEquiv, card_stdLeviBorel_fourthJ,
    ← Nat.card_congr (Equiv.ofBijective _ (residueMap_bijective two_mem_fourthJ)),
    card_parabolicCosets_fourthJ]
  norm_num

theorem commutatorElement_mem_of_index_two {G : Type*} [Group G] {H : Subgroup G}
    (h : H.index = 2) (a b : G) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff,
    inv_mem_iff]
  tauto

theorem card_range_rhoMinus
    : Nat.card rhoMinus.range = 197406720 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective rhoMinus_injective).toEquiv, card_stdLevi_fourthJ]

theorem range_rhoMinus
    : rhoMinus.range = orthElementaryGroup Qminus := by
  have hRO : rhoMinus.range ≤ TauCeti.QuadraticMap.orthogonalGroup Qminus := by
    rintro _ ⟨l, rfl⟩
    exact rhoMinus_mem_orthogonalGroup l
  have hindex :
      (rhoMinus.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Qminus)).index = 2 := by
    have h :=
      (rhoMinus.range.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Qminus)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRO).toEquiv, card_range_rhoMinus,
      card_orthogonalGroup_Qminus] at h
    omega
  have hle : orthElementaryGroup Qminus ≤ rhoMinus.range := by
    rw [← commutator_orthogonalGroup_Qminus, Subgroup.commutator_le]
    intro g hg g' hg'
    exact commutatorElement_mem_of_index_two hindex ⟨g, hg⟩ ⟨g', hg'⟩
  have : Finite rhoMinus.range :=
    Nat.finite_of_card_ne_zero (by rw [card_range_rhoMinus]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_range_rhoMinus, card_elementaryGroup_Qminus])).symm

theorem rhoMinus_mem_elementaryGroup
    (l : stdLevi fourthJ) :
    rhoMinus l ∈ orthElementaryGroup Qminus :=
  range_rhoMinus ▸ ⟨l, rfl⟩

@[expose] def leviEquiv
    : stdLevi fourthJ ≃* orthElementaryGroup Qminus :=
  (MonoidHom.ofInjective rhoMinus_injective).trans (MulEquiv.subgroupCongr range_rhoMinus)

theorem coe_leviEquiv
    (l : stdLevi fourthJ) :
    ((leviEquiv l : orthElementaryGroup Qminus) : V0 ≃ₗ[ZMod 2] V0) = rhoMinus l :=
  rfl

theorem rhoMinus_mem_tailBorel_of_mem
    {l : stdLevi fourthJ}
    (hl : (l : ModGL Tag.E6 K) ∈ stdLeviBorel fourthJ) : rhoMinus l ∈ tailBorel 3 qBin :=
  mem_tailBorel.2 ⟨rhoMinus_mem_elementaryGroup l,
    fun _ hk1 hk3 => map_tailFlag_rhoMinus_of_mem hl hk1 hk3⟩

theorem card_tailBorel : Nat.card (tailBorel 3 qBin) = 3 * 2 ^ 12 := by
  have h := index_tailBorel_subgroupOf (r := 3) qBin_anisotropic ⟨a₀, a₀_ne_zero⟩
  have h2 := ((tailBorel 3 qBin).subgroupOf (orthElementaryGroup Qminus)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tailBorel_le).toEquiv, h,
    card_singularFlags_Qminus, card_elementaryGroup_Qminus] at h2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 16065) (h2.trans (by norm_num))

theorem mem_stdLeviBorel_iff
    (l : stdLevi fourthJ) :
    (l : ModGL Tag.E6 K) ∈ stdLeviBorel fourthJ ↔ rhoMinus l ∈ tailBorel 3 qBin := by
  refine ⟨rhoMinus_mem_tailBorel_of_mem, fun h => ?_⟩
  have hle : (stdLeviBorel fourthJ).subgroupOf (stdLevi fourthJ) ≤
      (tailBorel 3 qBin).comap rhoMinus := fun x hx => rhoMinus_mem_tailBorel_of_mem hx
  have hcardT : Nat.card ((tailBorel 3 qBin).comap rhoMinus) = 3 * 2 ^ 12 := by
    rw [Nat.card_congr (((tailBorel 3 qBin).comap rhoMinus).equivMapOfInjective _
      rhoMinus_injective).toEquiv, Subgroup.map_comap_eq, range_rhoMinus,
      inf_of_le_right tailBorel_le, card_tailBorel]
  have hcardB : Nat.card ((stdLeviBorel fourthJ).subgroupOf (stdLevi fourthJ)) = 3 * 2 ^ 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (stdLeviBorel_le_stdLevi two_mem_fourthJ)).toEquiv, card_stdLeviBorel_fourthJ]
  have : Finite ((tailBorel 3 qBin).comap rhoMinus) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; norm_num)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardT, hcardB])
  have hmem : l ∈ (tailBorel 3 qBin).comap rhoMinus := h
  rw [← heq] at hmem
  exact hmem

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue
