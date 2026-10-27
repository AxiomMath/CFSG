module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBCentralQuotient

theorem pComponent_exists_le_of_component_image {X : Type*} [Group X] [Finite X]
    (p : ℕ) (V : Subgroup X) (hV : V.IsSubnormal)
    (himage : Open.IsComponentOf (V.map (QuotientGroup.mk' (pPrimeCore p X))) ⊤) :
    ∃ L : Subgroup X, L ≤ V ∧ CFSG.IsPComponent p L ∧
      L.map (QuotientGroup.mk' (pPrimeCore p X)) =
        V.map (QuotientGroup.mk' (pPrimeCore p X)) := by
  obtain ⟨L, hLV, hminimal⟩ := Finite.exists_le_minimal
    (p := fun L : Subgroup X => L.IsSubnormal ∧
      L.map (QuotientGroup.mk' (pPrimeCore p X)) =
        V.map (QuotientGroup.mk' (pPrimeCore p X))) ⟨hV, rfl⟩
  refine ⟨L, hLV, ?_, hminimal.prop.2⟩
  apply (CatalogueBAlternating.pComponent_iff_minimal_image p L).mpr
  refine ⟨Components.chain_of_mathlib_subnormal hminimal.prop.1,
    hminimal.prop.2.symm ▸ himage, ?_⟩
  intro J hJL hJ hmap
  exact ((minimal_iff.mp hminimal).2
    ⟨Components.mathlib_subnormal_of_chain hJ .top, hmap.trans hminimal.prop.2⟩ hJL).symm

theorem pComponent_derivedPreimage {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) (M : Subgroup Y)
    (hM : CFSG.IsPComponent p M) : CFSG.IsPComponent p (derivedPreimage f M) := by
  let qX := QuotientGroup.mk' (pPrimeCore p X)
  let qY := QuotientGroup.mk' (pPrimeCore p Y)
  let g := coreQuotientMap p f hsurjective
  let R := derivedPreimage f M
  let : Group.IsPerfect M := CatalogueBAlternating.pComponent_perfect hM
  let : Group.IsPerfect R := derivedPreimage_perfect f hsurjective hcentral M
  have hRmap : R.map f = M := derivedPreimage_map f hsurjective M
  have hRchain : R.IsSubnormal := derivedPreimage_subnormal f M hM.choose_spec.2.1
  obtain ⟨_, hD, hMminimal⟩ := (CatalogueBAlternating.pComponent_iff_minimal_image p M).mp hM
  have hg : g.ker ≤ Subgroup.center (X ⧸ pPrimeCore p X) :=
    coreQuotientMap_kernel_central p f hsurjective hcentral
  have hCmap : (R.map qX).map g = M.map qY := by
    rw [coreQuotientMap_map_image, hRmap]
  let : Group.IsPerfect (R.map qX) := Group.IsPerfect.ofSurjective
    (imageRestriction_surjective qX R)
  have hCquasisimple : Open.IsQuasisimple (R.map qX) :=
    CentralExtensions.quasisimple_of_surjective
      (hCmap.symm ▸ hD.2.2) (imageRestriction g (R.map qX))
      (imageRestriction_surjective g (R.map qX))
      (imageRestriction_kernel_central g hg (R.map qX))
  apply (CatalogueBAlternating.pComponent_iff_minimal_image p R).mpr
  refine ⟨Components.chain_of_mathlib_subnormal hRchain,
    ⟨le_top, Components.chain_of_mathlib_subnormal
      (hRchain.map (QuotientGroup.mk'_surjective _)), hCquasisimple⟩, ?_⟩
  intro J hJR hJ hJimage
  have himages : (J.map f).map qY = M.map qY := by
    rw [← coreQuotientMap_map_image p f hsurjective J, hJimage, hCmap]
  have hJmap : J.map f = M := hMminimal (J.map f)
    (by rw [← hRmap]; exact Subgroup.map_mono hJR)
    (Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hJ .top).map hsurjective)) himages
  apply le_antisymm hJR
  exact perfect_le_of_map_le f hcentral R J (by rw [hRmap, hJmap])

theorem pComponent_map {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) (L : Subgroup X)
    (hL : CFSG.IsPComponent p L) : CFSG.IsPComponent p (L.map f) := by
  let qX := QuotientGroup.mk' (pPrimeCore p X)
  let qY := QuotientGroup.mk' (pPrimeCore p Y)
  let g := coreQuotientMap p f hsurjective
  let M := L.map f
  obtain ⟨hLchain, hC, hLminimal⟩ :=
    (CatalogueBAlternating.pComponent_iff_minimal_image p L).mp hL
  let : Group.IsPerfect (L.map qX) := ⟨hC.2.2.1⟩
  have hg : g.ker ≤ Subgroup.center (X ⧸ pPrimeCore p X) :=
    coreQuotientMap_kernel_central p f hsurjective hcentral
  have hCmap : (L.map qX).map g = M.map qY := coreQuotientMap_map_image p f hsurjective L
  have hDquasisimple : Open.IsQuasisimple (M.map qY) := by
    rw [← hCmap]
    exact CentralTwoKernel.quasisimple_of_surjective hC.2.2
      (imageRestriction g (L.map qX)) (imageRestriction_surjective g (L.map qX))
      (imageRestriction_kernel_central g hg (L.map qX))
  have hMchain : M.IsSubnormal :=
    (Components.mathlib_subnormal_of_chain hLchain .top).map hsurjective
  have hD : Open.IsComponentOf (M.map qY) ⊤ :=
    ⟨le_top, Components.chain_of_mathlib_subnormal
      (hMchain.map (QuotientGroup.mk'_surjective _)), hDquasisimple⟩
  obtain ⟨M₀, hM₀M, hM₀, hM₀image⟩ := pComponent_exists_le_of_component_image p M hMchain hD
  let R := derivedPreimage f M₀
  have hR : CFSG.IsPComponent p R := pComponent_derivedPreimage p f hsurjective hcentral M₀ hM₀
  let : Group.IsPerfect M₀ := CatalogueBAlternating.pComponent_perfect hM₀
  let : Group.IsPerfect R := CatalogueBAlternating.pComponent_perfect hR
  have hRmap : R.map f = M₀ := derivedPreimage_map f hsurjective M₀
  have hRL : R ≤ L := perfect_le_of_map_le f hcentral R L (by rw [hRmap]; exact hM₀M)
  have hRquotient : (R.map qX).map g = M.map qY := by
    rw [coreQuotientMap_map_image, hRmap]
    exact hM₀image
  have hCcontainment : L.map qX ≤ R.map qX :=
    perfect_le_of_map_le g hg (L.map qX) (R.map qX) (by rw [hCmap, hRquotient])
  have hReq : R = L := hLminimal R hRL
    ((CatalogueBAlternating.pComponent_iff_minimal_image p R).mp hR).1
    (le_antisymm (Subgroup.map_mono hRL) hCcontainment)
  have hM₀eq : M₀ = M := by
    rw [← hRmap, hReq]
  change CFSG.IsPComponent p M
  exact hM₀eq ▸ hM₀

theorem pComponent_left_inverse {X Y : Type*} [Group X] [Group Y]
    (p : ℕ) (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X)
    (L : Subgroup X) (hL : CFSG.IsPComponent p L) :
    derivedPreimage f (L.map f) = L := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  exact derivedPreimage_image_eq f hcentral L

theorem pComponent_right_inverse {X Y : Type*} [Group X] [Group Y]
    (p : ℕ) (f : X →* Y) (hsurjective : Function.Surjective f)
    (M : Subgroup Y) (hM : CFSG.IsPComponent p M) :
    (derivedPreimage f M).map f = M := by
  let : Group.IsPerfect M := CatalogueBAlternating.pComponent_perfect hM
  exact derivedPreimage_map f hsurjective M

theorem pComponent_exists_lift {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) (M : Subgroup Y)
    (hM : CFSG.IsPComponent p M) :
    ∃ L : Subgroup X, CFSG.IsPComponent p L ∧ L.map f = M ∧ L = derivedPreimage f M :=
  ⟨derivedPreimage f M, pComponent_derivedPreimage p f hsurjective hcentral M hM,
    pComponent_right_inverse p f hsurjective M hM, rfl⟩

theorem pComponent_lift_unique {X Y : Type*} [Group X] [Group Y]
    (p : ℕ) (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X)
    (L₁ L₂ : Subgroup X) (hL₁ : CFSG.IsPComponent p L₁) (hL₂ : CFSG.IsPComponent p L₂)
    (himages : L₁.map f = L₂.map f) : L₁ = L₂ := by
  rw [← pComponent_left_inverse p f hcentral L₁ hL₁,
    ← pComponent_left_inverse p f hcentral L₂ hL₂, himages]

theorem pComponent_bijOn {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) :
    Set.BijOn (Subgroup.map f) {L | CFSG.IsPComponent p L} {M | CFSG.IsPComponent p M} := by
  refine ⟨fun L hL => pComponent_map p f hsurjective hcentral L hL, ?_, ?_⟩
  · intro L₁ hL₁ L₂ hL₂ himages
    exact pComponent_lift_unique p f hcentral L₁ L₂ hL₁ hL₂ himages
  · intro M hM
    exact ⟨derivedPreimage f M, pComponent_derivedPreimage p f hsurjective hcentral M hM,
      pComponent_right_inverse p f hsurjective M hM⟩

@[expose] def pComponentEquiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) :
    {L : Subgroup X // CFSG.IsPComponent p L} ≃ {M : Subgroup Y // CFSG.IsPComponent p M} where
  toFun L := ⟨L.val.map f, pComponent_map p f hsurjective hcentral L.val L.property⟩
  invFun M := ⟨derivedPreimage f M.val,
    pComponent_derivedPreimage p f hsurjective hcentral M.val M.property⟩
  left_inv L := Subtype.ext (pComponent_left_inverse p f hcentral L.val L.property)
  right_inv M := Subtype.ext (pComponent_right_inverse p f hsurjective M.val M.property)

theorem pComponentEquiv_apply {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) (L : {L : Subgroup X // CFSG.IsPComponent p L}) :
    (pComponentEquiv p f hsurjective hcentral L).val = L.val.map f := rfl

theorem pComponentEquiv_symm_apply {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) (M : {M : Subgroup Y // CFSG.IsPComponent p M}) :
    ((pComponentEquiv p f hsurjective hcentral).symm M).val =
      (commutator (M.val.comap f)).map (M.val.comap f).subtype := rfl

theorem central_quotient_p_component_bijection {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (p : ℕ) (hp : p.Prime) (f : X →* Y)
    (hsurjective : Function.Surjective f) (hcentral : f.ker ≤ Subgroup.center X) :
    Set.BijOn (Subgroup.map f) {L | CFSG.IsPComponent p L} {M | CFSG.IsPComponent p M} ∧
      (∀ L : Subgroup X, CFSG.IsPComponent p L →
        CFSG.IsPComponent p (L.map f) ∧
          (commutator ((L.map f).comap f)).map ((L.map f).comap f).subtype = L ∧
          (CFSG.IsQuasisimple L ↔ CFSG.IsQuasisimple (L.map f))) ∧
      (∀ M : Subgroup Y, CFSG.IsPComponent p M →
        CFSG.IsPComponent p ((commutator (M.comap f)).map (M.comap f).subtype) ∧
          ((commutator (M.comap f)).map (M.comap f).subtype).map f = M) := by
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨pComponent_bijOn p f hsurjective hcentral, ?_, ?_⟩
  · intro L hL
    exact ⟨pComponent_map p f hsurjective hcentral L hL,
      pComponent_left_inverse p f hcentral L hL, pComponent_quasisimple_iff f hcentral p L hL⟩
  · intro M hM
    exact ⟨pComponent_derivedPreimage p f hsurjective hcentral M hM,
      pComponent_right_inverse p f hsurjective M hM⟩

end CFSG.ComponentClassification.CatalogueBCentralQuotient
