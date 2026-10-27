module

public import CFSG.LocalAnalysis.LargeEvenClassification.FullActionGeneratorBound
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourSubgroup

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem smallCfourShearDifference_subspace_rank
    (W : Submodule (ZMod 2) (RankTwoBinaryResidue 1)) :
    ∃ k : ℕ, k ≤ 2 ∧
      Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (W.map smallCfourShearDifference) + k ∧
      (k = 2 → smallCfourShearPlane ≤ W) := by
  let restriction := smallCfourShearDifference.domRestrict W
  let k := Module.finrank (ZMod 2) restriction.ker
  have hrange : restriction.range = W.map smallCfourShearDifference := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : restriction.ker.map W.subtype = W ⊓ smallCfourShearPlane := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype, smallCfourShearDifference_kernel]
  have hdimension : Module.finrank (ZMod 2)
      (W ⊓ smallCfourShearPlane : Submodule (ZMod 2) (RankTwoBinaryResidue 1)) = k := by
    rw [← hker, Submodule.finrank_map_subtype_eq]
  have hsmall := Submodule.finrank_mono (show W ⊓ smallCfourShearPlane ≤ smallCfourShearPlane from inf_le_right)
  rw [hdimension, smallCfourShearPlane_finrank] at hsmall
  refine ⟨k, hsmall, ?_, ?_⟩
  · have h := restriction.finrank_range_add_finrank_ker
    rw [hrange] at h
    exact h.symm
  · intro hk
    have heq : W ⊓ smallCfourShearPlane = smallCfourShearPlane :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hdimension, hk, smallCfourShearPlane_finrank])
    exact heq ▸ inf_le_left

@[expose] def smallCfourEvenKernel (Q : Subgroup (ResidualRing 1)ˣ) : Subgroup Q :=
  smallCfourEvenSubgroup.comap Q.subtype

instance smallCfourEvenKernel_normal (Q : Subgroup (ResidualRing 1)ˣ) : (smallCfourEvenKernel Q).Normal :=
  Subgroup.Normal.comap inferInstance Q.subtype

@[expose] def smallCfourEvenImage (Q : Subgroup (ResidualRing 1)ˣ) : Subgroup (ResidualRing 1)ˣ :=
  Q ⊓ smallCfourEvenSubgroup

@[expose] def smallCfourEvenKernelEquiv (Q : Subgroup (ResidualRing 1)ˣ) :
    smallCfourEvenKernel Q ≃* smallCfourEvenImage Q where
  toFun u := ⟨u.val.val, u.val.property, u.property⟩
  invFun u := ⟨⟨u.val, u.property.1⟩, u.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def smallCfourEvenLeadingHom (Q : Subgroup (ResidualRing 1)ˣ) :
    smallCfourEvenKernel Q →* Multiplicative (RankTwoBinaryResidue 1) :=
  (smallCfourEvenCoordinateHom (smallCfourEvenImage Q) inf_le_right).comp
    (smallCfourEvenKernelEquiv Q).toMonoidHom

theorem smallCfourEvenLeadingHom_injective (Q : Subgroup (ResidualRing 1)ˣ) :
    Function.Injective (smallCfourEvenLeadingHom Q) :=
  (smallCfourEvenCoordinateHom_injective (smallCfourEvenImage Q) inf_le_right).comp
    (smallCfourEvenKernelEquiv Q).injective

theorem smallCfourEvenLeadingHom_spec (Q : Subgroup (ResidualRing 1)ˣ) (u : smallCfourEvenKernel Q) :
    smallCfourEvenUnit (smallCfourEvenLeadingHom Q u).toAdd = u.val.val :=
  smallCfourEvenCoordinateHom_spec (smallCfourEvenImage Q) inf_le_right (smallCfourEvenKernelEquiv Q u)

theorem smallCfourEvenLeadingHom_rank (Q : Subgroup (ResidualRing 1)ˣ) (hpgroup : IsPGroup 2 Q) :
    pGeneratorRank 2 (smallCfourEvenKernel Q) =
      Module.finrank (ZMod 2) (binaryHomRange (smallCfourEvenLeadingHom Q)) :=
  binaryHom_injective_generator_rank (hpgroup.to_subgroup _) _ (smallCfourEvenLeadingHom_injective Q)

theorem smallCfour_even_difference_product (f g : RankTwoBinaryResidue 1) :
    smallCfourEvenUnit (f - g) = smallCfourEvenUnit f * (smallCfourEvenUnit g)⁻¹ := by
  change smallCfourEvenHom (Multiplicative.ofAdd (f - g)) =
    smallCfourEvenHom (Multiplicative.ofAdd f) * (smallCfourEvenHom (Multiplicative.ofAdd g))⁻¹
  rw [ofAdd_sub, map_div, div_eq_mul_inv]

theorem smallCfourEvenLeadingHom_commutator
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourSylow)
    (u : Q) (houtside : u.val ∉ smallCfourEvenSubgroup) (v : smallCfourEvenKernel Q) :
    smallCfourEvenLeadingHom Q
      ⟨u * v.val * u⁻¹ * v.val⁻¹, (smallCfourEvenKernel Q).mul_mem
        (Subgroup.Normal.conj_mem inferInstance v.val v.property u)
        ((smallCfourEvenKernel Q).inv_mem v.property)⟩ =
      Multiplicative.ofAdd (smallCfourShearDifference (smallCfourEvenLeadingHom Q v).toAdd) := by
  let commutator : smallCfourEvenKernel Q :=
    ⟨u * v.val * u⁻¹ * v.val⁻¹, (smallCfourEvenKernel Q).mul_mem
      (Subgroup.Normal.conj_mem inferInstance v.val v.property u)
      ((smallCfourEvenKernel Q).inv_mem v.property)⟩
  let x := (smallCfourEvenLeadingHom Q v).toAdd
  have hspec := smallCfourEvenLeadingHom_spec Q commutator
  have hv : smallCfourEvenUnit x = v.val.val := smallCfourEvenLeadingHom_spec Q v
  have hconj := smallCfourSylow_conjugation_even u.val (hle u.property) houtside x
  have hinv : (smallCfourBinaryShear⁻¹).val = smallCfourBinaryShear.val := by decide +kernel
  have hdelta : smallCfourEvenUnit (smallCfourShearDifference x) = commutator.val.val := by
    change smallCfourEvenUnit (smallCfourBinaryShear.val * x * (smallCfourBinaryShear⁻¹).val - x) = _
    rw [hinv, smallCfour_even_difference_product, ← hconj, hv]
    rfl
  apply smallCfourEvenHom_injective
  exact hspec.trans hdelta.symm

theorem smallCfourShearDifference_le_killed
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourSylow) (hpgroup : IsPGroup 2 Q)
    (u : Q) (houtside : u.val ∉ smallCfourEvenSubgroup) :
    (binaryHomRange (smallCfourEvenLeadingHom Q)).map smallCfourShearDifference ≤
      binaryHomRange ((smallCfourEvenLeadingHom Q).comp
        ((frattini Q).comap (smallCfourEvenKernel Q).subtype).subtype) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨v, hv⟩ := (binaryHomRange_mem _ _).mp hy
  let commutator : smallCfourEvenKernel Q :=
    ⟨u * v.val * u⁻¹ * v.val⁻¹, (smallCfourEvenKernel Q).mul_mem
      (Subgroup.Normal.conj_mem inferInstance v.val v.property u)
      ((smallCfourEvenKernel Q).inv_mem v.property)⟩
  have hkilled : commutator.val ∈ frattini Q := pGroup_commutator_mem_frattini Nat.prime_two hpgroup u v.val
  apply (binaryHomRange_mem _ _).mpr
  refine ⟨⟨commutator, hkilled⟩, ?_⟩
  have h := smallCfourEvenLeadingHom_commutator Q hle u houtside v
  rw [hv] at h
  exact h

theorem smallCfour_outer_quotient_rank
    (Q : Subgroup (ResidualRing 1)ˣ) (hpgroup : IsPGroup 2 Q) :
    pGeneratorRank 2 (Q ⧸ smallCfourEvenKernel Q) ≤ 1 := by
  let outer := (Units.map smallCfourBinaryHom.toMonoidHom).comp Q.subtype
  have hkernel : outer.ker = smallCfourEvenKernel Q := by
    ext u
    change Units.map smallCfourBinaryHom.toMonoidHom u.val = 1 ↔ u.val ∈ smallCfourEvenSubgroup
    rw [smallCfourEvenSubgroup_kernel]
    rfl
  have e : (Q ⧸ smallCfourEvenKernel Q) ≃* outer.range :=
    QuotientGroup.liftEquiv _ outer.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict, hkernel])
  have hcard : Nat.card (Q ⧸ smallCfourEvenKernel Q) ≤ 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact (homocyclic_residue_two_image_card hpgroup outer).1
  have hquotientCard : Nat.card ((Q ⧸ smallCfourEvenKernel Q) ⧸ frattini (Q ⧸ smallCfourEvenKernel Q)) ≤
      Nat.card (Q ⧸ smallCfourEvenKernel Q) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hlog := Nat.log_mono_right (b := 2) (hquotientCard.trans hcard)
  exact hlog

theorem smallCfour_outer_subgroup_generators
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourSylow)
    (hpgroup : IsPGroup 2 Q) (houter : ¬ Q ≤ smallCfourEvenSubgroup) :
    pGeneratorRank 2 Q ≤ 3 ∧ (pGeneratorRank 2 Q = 3 → smallCfourEvenUnit smallCfourUpper ∈ Q) := by
  obtain ⟨u, hu, houtside⟩ := IsConcreteLE.not_le_iff_exists.mp houter
  let outer : Q := ⟨u, hu⟩
  let W := binaryHomRange (smallCfourEvenLeadingHom Q)
  let D := W.map smallCfourShearDifference
  have hsaving := binary_leading_image_frattini_saving hpgroup (smallCfourEvenKernel Q)
    (smallCfourEvenLeadingHom Q) D (smallCfourShearDifference_le_killed Q hle hpgroup outer houtside)
  rw [smallCfourEvenLeadingHom_rank Q hpgroup] at hsaving
  change pGeneratorRank 2 Q + Module.finrank (ZMod 2) D ≤
    pGeneratorRank 2 (Q ⧸ smallCfourEvenKernel Q) + Module.finrank (ZMod 2) W at hsaving
  have hquotient := smallCfour_outer_quotient_rank Q hpgroup
  obtain ⟨k, hk, hdimension, hcritical⟩ := smallCfourShearDifference_subspace_rank W
  change Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) D + k at hdimension
  refine ⟨by omega, ?_⟩
  intro hrank
  have hplane := hcritical (by omega)
  have hN : smallCfourUpper ∈ W := hplane (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨v, hv⟩ := (binaryHomRange_mem _ _).mp hN
  have hspec := smallCfourEvenLeadingHom_spec Q v
  rw [hv] at hspec
  exact hspec.symm ▸ v.val.property

theorem smallCfour_sylow_eq_of_contains_even_and_outer
    (H : Subgroup (ResidualRing 1)ˣ) (hle : H ≤ smallCfourSylow)
    (heven : smallCfourEvenSubgroup ≤ H) (houter : ¬ H ≤ smallCfourEvenSubgroup) :
    H = smallCfourSylow := by
  obtain ⟨u, hu, houtside⟩ := IsConcreteLE.not_le_iff_exists.mp houter
  have hresidueU : Units.map smallCfourBinaryHom.toMonoidHom u = smallCfourBinaryShear := by
    apply Units.ext
    rcases (smallCfourSylow_mem u).mp (hle hu) with h | h
    · exact False.elim (houtside ((smallCfourEvenSubgroup_mem u).mpr h))
    · exact h
  apply le_antisymm hle
  intro v hv
  rcases (smallCfourSylow_mem v).mp hv with hevenV | houterV
  · exact heven ((smallCfourEvenSubgroup_mem v).mpr hevenV)
  · have hresidueV : Units.map smallCfourBinaryHom.toMonoidHom v = smallCfourBinaryShear := Units.ext houterV
    have hkernel : u⁻¹ * v ∈ smallCfourEvenSubgroup := by
      rw [smallCfourEvenSubgroup_kernel]
      change Units.map smallCfourBinaryHom.toMonoidHom (u⁻¹ * v) = 1
      rw [map_mul, map_inv, hresidueU, hresidueV, inv_mul_cancel]
    have hmem := H.mul_mem hu (heven hkernel)
    simpa only [mul_inv_cancel_left] using hmem

theorem smallCfourEvenLeadingHom_stable
    (H : Subgroup (ResidualRing 1)ˣ) (hle : H ≤ smallCfourSylow)
    (houter : ¬ H ≤ smallCfourEvenSubgroup) :
    ∀ x ∈ binaryHomRange (smallCfourEvenLeadingHom H),
      smallCfourBinaryShear.val * x * smallCfourBinaryShear.val ∈
        binaryHomRange (smallCfourEvenLeadingHom H) := by
  obtain ⟨u, hu, houtside⟩ := IsConcreteLE.not_le_iff_exists.mp houter
  let outer : H := ⟨u, hu⟩
  intro x hx
  obtain ⟨v, hv⟩ := (binaryHomRange_mem _ _).mp hx
  let conjugate : smallCfourEvenKernel H :=
    ⟨outer * v.val * outer⁻¹, Subgroup.Normal.conj_mem inferInstance v.val v.property outer⟩
  have hconj := smallCfourSylow_conjugation_even u (hle hu) houtside x
  have hspec := smallCfourEvenLeadingHom_spec H v
  rw [hv] at hspec
  change smallCfourEvenUnit x = v.val.val at hspec
  rw [hspec] at hconj
  have hspecConj := smallCfourEvenLeadingHom_spec H conjugate
  have hconj' : conjugate.val.val =
      smallCfourEvenUnit (smallCfourBinaryShear.val * x * smallCfourBinaryShear.val) := hconj
  have heq : smallCfourEvenLeadingHom H conjugate =
      Multiplicative.ofAdd (smallCfourBinaryShear.val * x * smallCfourBinaryShear.val) := by
    apply smallCfourEvenHom_injective
    exact hspecConj.trans hconj'
  exact (binaryHomRange_mem _ _).mpr ⟨conjugate, heq⟩

theorem smallCfourEvenLeadingHom_image
    (H : Subgroup (ResidualRing 1)ˣ) :
    binaryHomRange (smallCfourEvenLeadingHom H) =
      binaryHomRange (smallCfourEvenCoordinateHom (smallCfourEvenImage H) inf_le_right) := by
  ext x
  rw [binaryHomRange_mem, binaryHomRange_mem]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨smallCfourEvenKernelEquiv H u, hu⟩
  · rintro ⟨u, hu⟩
    refine ⟨(smallCfourEvenKernelEquiv H).symm u, ?_⟩
    change smallCfourEvenCoordinateHom (smallCfourEvenImage H) inf_le_right
      (smallCfourEvenKernelEquiv H ((smallCfourEvenKernelEquiv H).symm u)) = _
    rw [MulEquiv.apply_symm_apply]
    exact hu

theorem smallCfour_proper_action_even_subgroup_generators
    (H Q : Subgroup (ResidualRing 1)ˣ) (hle : H ≤ smallCfourSylow) (hne : H ≠ smallCfourSylow)
    (houter : ¬ H ≤ smallCfourEvenSubgroup) (hQH : Q ≤ H) (hQeven : Q ≤ smallCfourEvenSubgroup)
    (hpH : IsPGroup 2 H) :
    pGeneratorRank 2 Q ≤ 3 ∧ (pGeneratorRank 2 Q = 3 → smallCfourEvenUnit smallCfourUpper ∈ Q) := by
  let E := smallCfourEvenImage H
  have hEproper : E ≠ smallCfourEvenSubgroup := by
    intro h
    apply hne
    exact smallCfour_sylow_eq_of_contains_even_and_outer H hle (h.symm ▸ inf_le_left) houter
  have hpQ := hpH.to_le hQH
  have hpE := hpH.to_le (show E ≤ H from inf_le_left)
  have hErank := smallCfour_proper_even_generator_rank E inf_le_right hEproper hpE
  have hQE : Q ≤ E := le_inf hQH hQeven
  have hQproper : Q ≠ smallCfourEvenSubgroup := by
    intro h
    apply hEproper
    exact le_antisymm inf_le_right (h.symm ▸ hQE)
  have hQrank := smallCfour_proper_even_generator_rank Q hQeven hQproper hpQ
  refine ⟨hQrank, ?_⟩
  intro hrank
  let coordinateQ := smallCfourEvenCoordinateHom Q hQeven
  let coordinateE := smallCfourEvenCoordinateHom E inf_le_right
  let WQ := binaryHomRange coordinateQ
  let WE := binaryHomRange coordinateE
  have hWle : WQ ≤ WE := by
    rintro x ⟨q, hq⟩
    exact ⟨Q.inclusion hQE q, hq⟩
  have hWQrank : Module.finrank (ZMod 2) WQ = 3 :=
    (smallCfourEvenCoordinateHom_generator_rank Q hQeven hpQ).symm.trans hrank
  have hWErank : Module.finrank (ZMod 2) WE ≤ 3 := by
    rw [← smallCfourEvenCoordinateHom_generator_rank E inf_le_right hpE]
    exact hErank
  have hWElarge := Submodule.finrank_mono hWle
  have hWeq : WQ = WE := Submodule.eq_of_le_of_finrank_eq hWle (by omega)
  have hdimension : Module.finrank (ZMod 2) WE = 3 := hWeq ▸ hWQrank
  have hstable : ∀ x ∈ WE, smallCfourBinaryShear.val * x * smallCfourBinaryShear.val ∈ WE := by
    change ∀ x ∈ binaryHomRange (smallCfourEvenCoordinateHom (smallCfourEvenImage H) inf_le_right),
      smallCfourBinaryShear.val * x * smallCfourBinaryShear.val ∈
        binaryHomRange (smallCfourEvenCoordinateHom (smallCfourEvenImage H) inf_le_right)
    rw [← smallCfourEvenLeadingHom_image H]
    exact smallCfourEvenLeadingHom_stable H hle houter
  have hplane := smallCfour_invariant_hyperplane_contains_plane WE hdimension hstable
  have hN : smallCfourUpper ∈ WQ := by
    rw [hWeq]
    exact hplane (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨q, hq⟩ := (binaryHomRange_mem coordinateQ _).mp hN
  have hspec := smallCfourEvenCoordinateHom_spec Q hQeven q
  rw [hq] at hspec
  exact hspec.symm ▸ q.property

theorem small_cfour_proper_action_subgroup_generators
    (H : Subgroup (ResidualRing 1)ˣ) (hproper : H < smallCfourSylow)
    (houter : ¬ H ≤ smallCfourEvenSubgroup) (Q : Subgroup (ResidualRing 1)ˣ) (hQ : Q ≤ H) :
    Group.rank Q ≤ 3 ∧ (Group.rank Q = 3 → smallCfourEvenUnit smallCfourUpper ∈ Q) := by
  have hpSylow : IsPGroup 2 smallCfourSylow := IsPGroup.of_card (n := 5) smallCfourSylow_card
  have hpH := hpSylow.to_le hproper.le
  have hpQ := hpH.to_le hQ
  rw [← pGeneratorRank_eq_group_rank Nat.prime_two hpQ]
  by_cases hQeven : Q ≤ smallCfourEvenSubgroup
  · exact smallCfour_proper_action_even_subgroup_generators H Q hproper.le hproper.ne
      houter hQ hQeven hpH
  · exact smallCfour_outer_subgroup_generators Q (hQ.trans hproper.le) hpQ hQeven

end CFSG.LargeEvenClassification.Helpers
