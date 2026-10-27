module

public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourMatrix
public import CFSG.LocalAnalysis.LargeEvenClassification.HomocyclicOuterResidue

public section

namespace CFSG.LargeEvenClassification.Helpers

private theorem smallCfour_coefficient_residue
    (c : CyclicPairCoefficients 1 4) : cyclicPairCoefficientResidue 1 4 (by decide) c = c := by
  change ((ZMod.castHom (by decide : 4 ∣ 4) (ZMod 4) c.1.1,
    ZMod.castHom (by decide : 4 ∣ 4) (ZMod 4) c.1.2),
    (ZMod.castHom (by decide : 4 ∣ 4) (ZMod 4) c.2.1,
      ZMod.castHom (by decide : 4 ∣ 4) (ZMod 4) c.2.2)) = c
  simp only [ZMod.castHom_self, RingHom.id_apply]

@[expose] noncomputable def smallCfourEndRingEquiv :
    AddMonoid.End (ZMod 4 × ZMod 4) ≃+* ResidualRing 1 :=
  RingEquiv.ofBijective (cyclicPairEndResidualHom 1 4 (by decide)) (by
    constructor
    · intro f g h
      apply cyclicPairEndCoefficients_injective 1 4
      change cyclicPairCoefficientResidue 1 4 (by decide) (cyclicPairEndCoefficients 1 4 f) =
        cyclicPairCoefficientResidue 1 4 (by decide) (cyclicPairEndCoefficients 1 4 g) at h
      have hf := smallCfour_coefficient_residue (cyclicPairEndCoefficients 1 4 f)
      have hg := smallCfour_coefficient_residue (cyclicPairEndCoefficients 1 4 g)
      exact hf.symm.trans (h.trans hg)
    · intro c
      let coefficients : CyclicPairCoefficients 1 4 := ((c.1.1, c.1.2), (c.2.1, c.2.2))
      refine ⟨cyclicPairEndFromCoefficients 1 4 coefficients, ?_⟩
      change cyclicPairCoefficientResidue 1 4 (by decide)
        (cyclicPairEndCoefficients 1 4 (cyclicPairEndFromCoefficients 1 4 coefficients)) = c
      rw [cyclicPairEndCoefficients_from, smallCfour_coefficient_residue]
      rfl)

theorem smallCfourEndRingEquiv_coefficients (f : AddMonoid.End (ZMod 4 × ZMod 4)) :
    smallCfourEndRingEquiv f = cyclicPairEndCoefficients 1 4 f :=
  smallCfour_coefficient_residue _

@[expose] def smallCfourBinaryCoordinates (x : ResidualRing 1) : RankTwoBinaryResidue 1 :=
  let reduction := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  ((reduction x.1.1, reduction x.1.2), (reduction x.2.1, reduction x.2.2))

@[expose] def smallCfourBinaryHom : ResidualRing 1 →+* RankTwoBinaryResidue 1 where
  toFun := smallCfourBinaryCoordinates
  map_zero' := by decide +kernel
  map_one' := by decide +kernel
  map_add' := by
    intro x y
    change smallCfourBinaryCoordinates (residualAdd x y) =
      rankTwoBinaryResidueAdd (smallCfourBinaryCoordinates x) (smallCfourBinaryCoordinates y)
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [smallCfourBinaryCoordinates, residualAdd, rankTwoBinaryResidueAdd, map_add]
  map_mul' := by
    intro x y
    change smallCfourBinaryCoordinates (residualMultiply 1 x y) =
      rankTwoBinaryResidueProduct 1 (smallCfourBinaryCoordinates x) (smallCfourBinaryCoordinates y)
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [smallCfourBinaryCoordinates, residualMultiply, rankTwoBinaryResidueProduct,
        map_add, map_mul, one_mul]

@[expose] def smallCfourEvenMatrix (f : RankTwoBinaryResidue 1) : ResidualRing 1 :=
  ((1 + 2 * (f.1.1.val : ZMod 4), 2 * (f.1.2.val : ZMod 4)),
    (2 * (f.2.1.val : ZMod 4), 1 + 2 * (f.2.2.val : ZMod 4)))

theorem smallCfourEvenMatrix_square :
    ∀ f : RankTwoBinaryResidue 1, smallCfourEvenMatrix f * smallCfourEvenMatrix f = 1 := by
  decide +kernel

@[expose] def smallCfourEvenUnit (f : RankTwoBinaryResidue 1) : (ResidualRing 1)ˣ :=
  ⟨smallCfourEvenMatrix f, smallCfourEvenMatrix f,
    smallCfourEvenMatrix_square f, smallCfourEvenMatrix_square f⟩

@[expose] def smallCfourEvenHom : Multiplicative (RankTwoBinaryResidue 1) →* (ResidualRing 1)ˣ where
  toFun f := smallCfourEvenUnit f.toAdd
  map_one' := by apply Units.ext; decide +kernel
  map_mul' := by
    intro f g
    apply Units.ext
    have h : ∀ f g : RankTwoBinaryResidue 1,
        smallCfourEvenMatrix (f + g) = smallCfourEvenMatrix f * smallCfourEvenMatrix g := by
      decide +kernel
    exact h f.toAdd g.toAdd

theorem smallCfourEvenHom_injective : Function.Injective smallCfourEvenHom := by
  intro f g h
  have hval := congrArg Units.val h
  have hinj : ∀ f g : RankTwoBinaryResidue 1,
      smallCfourEvenMatrix f = smallCfourEvenMatrix g → f = g := by decide +kernel
  exact congrArg Multiplicative.ofAdd (hinj f.toAdd g.toAdd hval)

@[expose] def smallCfourEvenSubgroup : Subgroup (ResidualRing 1)ˣ := smallCfourEvenHom.range

theorem smallCfourEvenSubgroup_mem (u : (ResidualRing 1)ˣ) :
    u ∈ smallCfourEvenSubgroup ↔ smallCfourBinaryHom u.val = 1 := by
  have h : ∀ x : ResidualRing 1, smallCfourBinaryHom x = 1 ↔
      ∃ f : RankTwoBinaryResidue 1, smallCfourEvenMatrix f = x := by decide +kernel
  rw [h]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.toAdd, congrArg Units.val hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨Multiplicative.ofAdd f, Units.ext hf⟩

theorem smallCfourEvenSubgroup_kernel : smallCfourEvenSubgroup =
    (Units.map smallCfourBinaryHom.toMonoidHom).ker := by
  ext u
  rw [smallCfourEvenSubgroup_mem]
  change _ ↔ Units.map smallCfourBinaryHom.toMonoidHom u = 1
  exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩

instance smallCfourEvenSubgroup_normal : smallCfourEvenSubgroup.Normal := by
  rw [smallCfourEvenSubgroup_kernel]
  infer_instance

theorem smallCfourEvenSubgroup_card : Nat.card smallCfourEvenSubgroup = 16 := by
  let equivalence := MonoidHom.ofInjective smallCfourEvenHom_injective
  change Nat.card smallCfourEvenHom.range = 16
  rw [← Nat.card_congr equivalence.toEquiv]
  exact rankTwoBinaryResidue_card 1

theorem smallCfourEvenSubgroup_elementary : CFSG.Open.IsElemAbelian 2 smallCfourEvenSubgroup := by
  constructor
  · apply isMulCommutative_iff.mpr
    intro u v
    obtain ⟨f, hf⟩ := u.property
    obtain ⟨g, hg⟩ := v.property
    apply Subtype.ext
    change u.val * v.val = v.val * u.val
    rw [← hf, ← hg]
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro u ⟨f, rfl⟩
    rw [← map_pow]
    have h : ∀ f : Multiplicative (RankTwoBinaryResidue 1), f ^ 2 = 1 := by decide +kernel
    rw [h, map_one]

@[expose] def smallCfourBinaryShear : (RankTwoBinaryResidue 1)ˣ :=
  ⟨1 + smallCfourUpper, 1 + smallCfourUpper, by decide +kernel, by decide +kernel⟩

theorem smallCfourBinaryShear_square : smallCfourBinaryShear ^ 2 = 1 := by
  apply Units.ext
  decide +kernel

@[expose] def smallCfourBinaryShearSubgroup : Subgroup (RankTwoBinaryResidue 1)ˣ :=
  Subgroup.zpowers smallCfourBinaryShear

theorem smallCfourBinaryShearSubgroup_mem (u : (RankTwoBinaryResidue 1)ˣ) :
    u ∈ smallCfourBinaryShearSubgroup ↔ u = 1 ∨ u = smallCfourBinaryShear := by
  constructor
  · exact zpowers_involution_cases smallCfourBinaryShear smallCfourBinaryShear_square
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

@[expose] def smallCfourSylow : Subgroup (ResidualRing 1)ˣ :=
  smallCfourBinaryShearSubgroup.comap (Units.map smallCfourBinaryHom.toMonoidHom)

theorem smallCfourSylow_mem (u : (ResidualRing 1)ˣ) :
    u ∈ smallCfourSylow ↔ smallCfourBinaryHom u.val = 1 ∨
      smallCfourBinaryHom u.val = 1 + smallCfourUpper := by
  change Units.map smallCfourBinaryHom.toMonoidHom u ∈ smallCfourBinaryShearSubgroup ↔ _
  rw [smallCfourBinaryShearSubgroup_mem]
  exact ⟨fun h => h.elim (fun h => Or.inl (congrArg Units.val h))
    (fun h => Or.inr (congrArg Units.val h)),
    fun h => h.elim (fun h => Or.inl (Units.ext h)) (fun h => Or.inr (Units.ext h))⟩

theorem smallCfourEvenSubgroup_le_sylow : smallCfourEvenSubgroup ≤ smallCfourSylow := by
  intro u hu
  exact (smallCfourSylow_mem u).mpr (Or.inl ((smallCfourEvenSubgroup_mem u).mp hu))

private abbrev SmallCfourSylowCandidates := {x : ResidualRing 1 //
  (residualDeterminant x = 1 ∨ residualDeterminant x = 3) ∧
    (smallCfourBinaryHom x = 1 ∨ smallCfourBinaryHom x = 1 + smallCfourUpper)}

theorem smallCfourSylow_card : Nat.card smallCfourSylow = 32 := by
  let candidate : smallCfourSylow → SmallCfourSylowCandidates := fun u =>
    ⟨u.val.val, residual_unit_determinant u.val, (smallCfourSylow_mem u.val).mp u.property⟩
  have hinj : Function.Injective candidate := by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective candidate := by
    intro x
    obtain ⟨u, hu⟩ := residualUnitCandidate_surjective ⟨x.val, x.property.1⟩
    have hval : u.val = x.val := congrArg Subtype.val hu
    refine ⟨⟨u, (smallCfourSylow_mem u).mpr (hval.symm ▸ x.property.2)⟩, ?_⟩
    exact Subtype.ext hval
  rw [Nat.card_congr (Equiv.ofBijective candidate ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card]
  decide +kernel

theorem smallCfour_two_subgroup_conjugate
    (H : Subgroup (ResidualRing 1)ˣ) (hpgroup : IsPGroup 2 H) :
    ∃ u : (ResidualRing 1)ˣ, H.map (MulAut.conj u).toMonoidHom ≤ smallCfourSylow := by
  let chosen : Sylow 2 (ResidualRing 1)ˣ := Sylow.ofCard smallCfourSylow (by
    rw [smallCfourSylow_card, residual_unit_card_eq_one]
    norm_num
    decide +kernel)
  obtain ⟨containing, hcontained⟩ := hpgroup.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (ResidualRing 1)ˣ containing chosen
  have hmap := Subgroup.map_mono (f := (MulAut.conj u).toMonoidHom) hcontained
  have heq := congrArg (fun P : Sylow 2 (ResidualRing 1)ˣ => (P : Subgroup (ResidualRing 1)ˣ)) hu
  change (containing : Subgroup (ResidualRing 1)ˣ).map (MulAut.conj u).toMonoidHom = smallCfourSylow at heq
  exact ⟨u, heq ▸ hmap⟩

@[expose] def smallCfourShearDifference :
    RankTwoBinaryResidue 1 →ₗ[ZMod 2] RankTwoBinaryResidue 1 :=
  binaryResidueConjugationDifference smallCfourBinaryShear

@[expose] def smallCfourShearPlane : Submodule (ZMod 2) (RankTwoBinaryResidue 1) :=
  Submodule.span (ZMod 2) {1, smallCfourUpper}

theorem smallCfourShearDifference_kernel : smallCfourShearDifference.ker = smallCfourShearPlane := by
  apply le_antisymm
  · intro x hx
    have hcoordinates : ∀ x : RankTwoBinaryResidue 1,
        smallCfourShearDifference x = 0 → x.2.1 = 0 ∧ x.2.2 = x.1.1 := by
      decide +kernel
    have hexpansion : ∀ a b : ZMod 2,
        (((a, b), (0, a)) : RankTwoBinaryResidue 1) = a • (1 : RankTwoBinaryResidue 1) + b • smallCfourUpper := by
      intro a b
      have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases hbinary a with rfl | rfl <;> rcases hbinary b with rfl | rfl
      · simp only [zero_smul, zero_add]; rfl
      · simp only [zero_smul, one_smul, zero_add]; rfl
      · simp only [zero_smul, one_smul, add_zero]; rfl
      · simp only [one_smul]
        change (((1, 1), (0, 1)) : RankTwoBinaryResidue 1) =
          rankTwoBinaryResidueAdd ((1, 0), (0, 1)) ((0, 1), (0, 0))
        apply Prod.ext <;> apply Prod.ext <;> simp only [rankTwoBinaryResidueAdd, add_zero, zero_add]
    have heq : x = (((x.1.1, x.1.2), (0, x.1.1)) : RankTwoBinaryResidue 1) := by
      apply Prod.ext
      · rfl
      · exact Prod.ext (hcoordinates x hx).1 (hcoordinates x hx).2
    rw [heq, hexpansion]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert 1 _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl) <;> change smallCfourShearDifference _ = 0 <;> decide +kernel

theorem smallCfourShearDifference_range : smallCfourShearDifference.range = smallCfourShearPlane := by
  rw [← smallCfourShearDifference_kernel]
  ext x
  have h : ∀ x : RankTwoBinaryResidue 1,
      (∃ y, smallCfourShearDifference y = x) ↔ smallCfourShearDifference x = 0 := by decide +kernel
  exact h x

theorem smallCfourShearPlane_finrank : Module.finrank (ZMod 2) smallCfourShearPlane = 2 := by
  have hcard : Nat.card smallCfourShearDifference.ker = 4 := by
    change Nat.card {x : RankTwoBinaryResidue 1 // smallCfourShearDifference x = 0} = 4
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [smallCfourShearDifference_kernel, ← FiniteField.pow_finrank_eq_natCard 2 smallCfourShearPlane] at hcard
  have hlog := congrArg (Nat.log 2) hcard
  simpa only [Nat.log_pow (by decide : 1 < 2), show Nat.log 2 4 = 2 by decide] using hlog

theorem smallCfourSylow_conjugation_even
    (u : (ResidualRing 1)ˣ) (hu : u ∈ smallCfourSylow) (houtside : u ∉ smallCfourEvenSubgroup)
    (f : RankTwoBinaryResidue 1) :
    u * smallCfourEvenUnit f * u⁻¹ =
      smallCfourEvenUnit (smallCfourBinaryShear.val * f * smallCfourBinaryShear.val) := by
  have hresidue : smallCfourBinaryHom u.val = 1 + smallCfourUpper := by
    rcases (smallCfourSylow_mem u).mp hu with h | h
    · exact False.elim (houtside ((smallCfourEvenSubgroup_mem u).mpr h))
    · exact h
  apply Units.ext
  have hcertificate : ∀ x : ResidualRing 1,
      (residualDeterminant x = 1 ∨ residualDeterminant x = 3) →
      smallCfourBinaryHom x = 1 + smallCfourUpper →
      ∀ f : RankTwoBinaryResidue 1,
        x * smallCfourEvenMatrix f * residualInverse x =
          smallCfourEvenMatrix (smallCfourBinaryShear.val * f * smallCfourBinaryShear.val) := by
    decide +kernel
  have hinv : u.inv = residualInverse u.val := by
    have hcertificate : ∀ x : ResidualRing 1,
        (residualDeterminant x = 1 ∨ residualDeterminant x = 3) →
        x * residualInverse x = 1 := by decide +kernel
    have hright := hcertificate u.val (residual_unit_determinant u)
    calc
      u.inv = u.inv * (u.val * residualInverse u.val) := by rw [hright, mul_one]
      _ = residualInverse u.val := by rw [← mul_assoc, u.inv_val, one_mul]
  change u.val * smallCfourEvenMatrix f * u.inv = _
  rw [hinv]
  exact hcertificate u.val (residual_unit_determinant u) hresidue f

theorem smallCfourCentralShear :
    ∀ u : (ResidualRing 1)ˣ, u ∈ smallCfourSylow → Commute (smallCfourEvenUnit smallCfourUpper) u := by
  intro u hu
  have h : ∀ x : ResidualRing 1,
      (smallCfourBinaryHom x = 1 ∨ smallCfourBinaryHom x = 1 + smallCfourUpper) →
      smallCfourEvenMatrix smallCfourUpper * x = x * smallCfourEvenMatrix smallCfourUpper := by
    decide +kernel
  exact Units.ext (h u.val ((smallCfourSylow_mem u).mp hu))

theorem smallCfour_invariant_hyperplane_contains_plane
    (W : Submodule (ZMod 2) (RankTwoBinaryResidue 1))
    (hdimension : Module.finrank (ZMod 2) W = 3)
    (hstable : ∀ x ∈ W, smallCfourBinaryShear.val * x * smallCfourBinaryShear.val ∈ W) :
    smallCfourShearPlane ≤ W := by
  have hproper : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    rw [htop, finrank_top, rankTwoBinaryResidue_finrank] at hdimension
    omega
  obtain ⟨functional, hnonzero, hle⟩ := Submodule.exists_le_ker_of_lt_top W hproper
  have hkerSmall := Submodule.finrank_lt_finrank_of_lt
    (lt_top_iff_ne_top.mpr (mt LinearMap.ker_eq_top.mp hnonzero))
  rw [finrank_top, rankTwoBinaryResidue_finrank] at hkerSmall
  have hkerLarge := Submodule.finrank_mono hle
  have hkernel : W = functional.ker := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hexists : ∃ x : RankTwoBinaryResidue 1, functional x = 1 := by
    by_contra hnone
    apply hnonzero
    ext x
    have hbinary : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
    exact hbinary _ (fun h => hnone ⟨x, h⟩)
  obtain ⟨v, hv⟩ := hexists
  have hconjugateOne : functional (smallCfourBinaryShear.val * v * smallCfourBinaryShear.val) = 1 := by
    have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hbinary (functional (smallCfourBinaryShear.val * v * smallCfourBinaryShear.val)) with hz | hone
    · have hmem : smallCfourBinaryShear.val * v * smallCfourBinaryShear.val ∈ W := hkernel.symm ▸ hz
      have hmem' := hstable _ hmem
      have hinvolution : ∀ x : RankTwoBinaryResidue 1,
          smallCfourBinaryShear.val * (smallCfourBinaryShear.val * x * smallCfourBinaryShear.val) *
            smallCfourBinaryShear.val = x := by decide +kernel
      rw [hinvolution] at hmem'
      have hzero : functional v = 0 := hle hmem'
      have hbad : (1 : ZMod 2) = 0 := hv.symm.trans hzero
      exact False.elim (by revert hbad; decide)
    · exact hone
  rw [← smallCfourShearDifference_range]
  rintro x ⟨y, rfl⟩
  have hz : y - (functional y) • v ∈ W := by
    rw [hkernel]
    change functional (y - (functional y) • v) = 0
    rw [map_sub, map_smul, hv, smul_eq_mul, mul_one]
    exact sub_self (functional y)
  have hdeltaStable : smallCfourShearDifference (y - (functional y) • v) ∈ W := by
    have h := W.sub_mem (hstable _ hz) hz
    have hinv : (smallCfourBinaryShear⁻¹).val = smallCfourBinaryShear.val := by decide +kernel
    change smallCfourBinaryShear.val * _ * (smallCfourBinaryShear⁻¹).val - _ ∈ W
    rw [hinv]
    exact h
  have hdeltaV : smallCfourShearDifference v ∈ W := by
    rw [hkernel]
    have hinv : (smallCfourBinaryShear⁻¹).val = smallCfourBinaryShear.val := by decide +kernel
    change functional (smallCfourBinaryShear.val * v * (smallCfourBinaryShear⁻¹).val - v) = 0
    rw [hinv, map_sub, hconjugateOne, hv]
    decide +kernel
  have hdecomposition : smallCfourShearDifference y =
      smallCfourShearDifference (y - (functional y) • v) +
        (functional y) • smallCfourShearDifference v := by
    rw [map_sub, map_smul]
    abel
  rw [hdecomposition]
  exact W.add_mem hdeltaStable (W.smul_mem _ hdeltaV)

theorem small_cfour_automorphism_two_subgroup_normal_form :
    smallCfourEvenSubgroup.Normal ∧
    CFSG.Open.IsElemAbelian 2 smallCfourEvenSubgroup ∧
    Nat.card smallCfourEvenSubgroup = 16 ∧ Nat.card smallCfourSylow = 32 ∧
    (∀ H : Subgroup (ResidualRing 1)ˣ, IsPGroup 2 H →
      ∃ u : (ResidualRing 1)ˣ, H.map (MulAut.conj u).toMonoidHom ≤ smallCfourSylow) ∧
    (∀ u : (ResidualRing 1)ˣ, u ∈ smallCfourSylow → u ∉ smallCfourEvenSubgroup →
      ∀ f : RankTwoBinaryResidue 1, u * smallCfourEvenUnit f * u⁻¹ =
        smallCfourEvenUnit (smallCfourBinaryShear.val * f * smallCfourBinaryShear.val)) ∧
    smallCfourShearDifference.ker = smallCfourShearPlane ∧
    smallCfourShearDifference.range = smallCfourShearPlane ∧
    (∀ u : (ResidualRing 1)ˣ, u ∈ smallCfourSylow → Commute (smallCfourEvenUnit smallCfourUpper) u) ∧
    (∀ W : Submodule (ZMod 2) (RankTwoBinaryResidue 1), Module.finrank (ZMod 2) W = 3 →
      (∀ x ∈ W, smallCfourBinaryShear.val * x * smallCfourBinaryShear.val ∈ W) →
        smallCfourShearPlane ≤ W) :=
  ⟨inferInstance, smallCfourEvenSubgroup_elementary, smallCfourEvenSubgroup_card,
    smallCfourSylow_card, smallCfour_two_subgroup_conjugate,
    smallCfourSylow_conjugation_even, smallCfourShearDifference_kernel,
    smallCfourShearDifference_range, smallCfourCentralShear,
    smallCfour_invariant_hyperplane_contains_plane⟩

end CFSG.LargeEvenClassification.Helpers
