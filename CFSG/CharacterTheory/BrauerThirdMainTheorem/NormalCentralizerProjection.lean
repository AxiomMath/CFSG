module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalPVanishing
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalCentralAlgebra

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

noncomputable def centralizerProjection {G : Type*} [Group G]
    (subgroup : Subgroup G) (coefficients : G → ℂ) : G → ℂ :=
  (Subgroup.centralizer (subgroup : Set G) : Set G).indicator coefficients

theorem centralizerProjection_central {G : Type*} [Group G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (subgroup : Subgroup G) [subgroup.Normal]
    {coefficients : G → ℂ} (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksIsCentralR m (centralizerProjection subgroup coefficients) := by
  classical
  constructor
  · intro element
    simp only [centralizerProjection, Set.indicator_apply]
    split_ifs
    · exact hcoefficients.1 element
    · exact localRing_zero m hm
  · intro element conjugator
    have hnormalizer : conjugator ∈ Subgroup.normalizer (subgroup : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    simp only [centralizerProjection, Set.indicator_apply]
    change (if conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (subgroup : Set G)
      then coefficients (conjugator * element * conjugator⁻¹) else 0) =
        if element ∈ Subgroup.centralizer (subgroup : Set G) then coefficients element else 0
    rw [centralizer_conj_iff subgroup hnormalizer, hcoefficients.2]

theorem normalPSubgroup_centralizerProjection_congr (prime : ℕ) (hprime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (subgroup : Subgroup G) [subgroup.Normal]
    (hpGroup : IsPGroup prime subgroup) {character coefficients : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksCentralChar character coefficients -
      BlocksCentralChar character (centralizerProjection subgroup coefficients) ∈ BlocksLocalMaxIdeal m := by
  have hprojected := centralizerProjection_central m hm subgroup hcoefficients
  have hcentral : BlocksIsCentralR m (coefficients - centralizerProjection subgroup coefficients) := by
    constructor
    · intro element
      exact localRing_sub m hm (hcoefficients.1 element) (hprojected.1 element)
    · intro element conjugator
      simp only [Pi.sub_apply, hcoefficients.2 element conjugator, hprojected.2 element conjugator]
  have hvanishes : ∀ element ∈ Subgroup.centralizer (subgroup : Set G),
      (coefficients - centralizerProjection subgroup coefficients) element = 0 := by
    intro element helement
    simp only [Pi.sub_apply, centralizerProjection, Set.indicator_of_mem helement, sub_self]
  have hscalar := normalPSubgroup_centralChar_vanishes prime hprime m hm hprimeMem G subgroup hpGroup
    hcharacter hcentral hvanishes
  rw [centralChar_sub] at hscalar
  exact hscalar

theorem centralResidue_common_principal (prime : ℕ) (hprime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (small large : Type) [Group small] [Group large] [Finite small] [Finite large]
    (subgroup : Subgroup large) [subgroup.Normal] (hpGroup : IsPGroup prime subgroup)
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (hrange : Set.range inclusion = (Subgroup.centralizer (subgroup : Set large) : Set large))
    (character : BlocksIrr large)
    (hrestriction : ∀ value : commonCentralAlgebra m hm small large inclusion,
      centralResidue m hm large character (commonCentralInclusion m hm small large inclusion value) =
        centralResidue m hm small ⟨fun _ => 1, trivial_mem_irr small⟩ value.val) :
    character.val ∈ BlocksPrincipalBlock m large := by
  classical
  let : Fintype small := Fintype.ofFinite _
  apply mem_blockOf_of_centralChar_congr m hm large (trivial_mem_irr large) character.property
  intro coefficients hcoefficients
  have hprojected : BlocksIsCentralR m ((Set.range inclusion).indicator coefficients) := by
    rw [hrange]
    exact centralizerProjection_central m hm subgroup hcoefficients
  let value := commonCentralRestriction m hm small large inclusion hinjective coefficients hcoefficients hprojected
  have hequal := hrestriction value
  have hcongr := (localResidue_eq_iff m hm _ _).mp hequal
  change BlocksCentralChar character.val (centralLocalCoefficients m hm large
    (commonCentralInclusion m hm small large inclusion value)) -
      BlocksCentralChar (fun _ => 1) (centralLocalCoefficients m hm small value.val) ∈ BlocksLocalMaxIdeal m at hcongr
  rw [← commonCentralInclusion_augmentation m hm small large inclusion hinjective value] at hcongr
  have hcoeff := commonCentralRestriction_inclusion m hm small large inclusion hinjective coefficients hcoefficients hprojected
  rw [hrange] at hcoeff
  change centralLocalCoefficients m hm large (commonCentralInclusion m hm small large inclusion value) =
    centralizerProjection subgroup coefficients at hcoeff
  rw [hcoeff] at hcongr
  have htrivial := normalPSubgroup_centralizerProjection_congr prime hprime m hm hprimeMem large subgroup hpGroup
    (trivial_mem_irr large) hcoefficients
  have hnegative : BlocksCentralChar (fun _ => 1) (centralizerProjection subgroup coefficients) -
      BlocksCentralChar (fun _ => 1) coefficients ∈ BlocksLocalMaxIdeal m := by
    convert localMaxIdeal_neg m htrivial using 1
    ring
  exact localMaxIdeal_trans m hm
    (normalPSubgroup_centralizerProjection_congr prime hprime m hm hprimeMem large subgroup hpGroup
      character.property hcoefficients) (localMaxIdeal_trans m hm hcongr hnegative)

end CFSG.BrauerThirdMainTheorem.Helpers
