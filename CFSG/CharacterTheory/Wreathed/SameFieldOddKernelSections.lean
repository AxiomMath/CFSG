module

public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelQuotient
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigiditySections

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open CFSG.Wreathed.SquareRootSmallCharacterRigidity

variable {M X : Type} [Group M] [Group X]

theorem map_mem_squareRootSection (α : M →* X) {y g : M}
    (hg : g ∈ squareRootSection y) : α g ∈ squareRootSection (α y) := by
  obtain ⟨h, v, hh, hv, hcentral, hconj⟩ := hg
  have hvX : Odd (orderOf (α v)) :=
    Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr hv).coprime_dvd_right
      (orderOf_map_dvd α v))
  have hcentralX : α v ∈ Subgroup.centralizer ({α y} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hcentral ⊢
    simpa only [map_mul] using congrArg α hcentral
  refine ⟨h, α v, hh, hvX, hcentralX, ?_⟩
  obtain ⟨a, ha⟩ := isConj_iff.mp hconj
  apply isConj_iff.mpr
  refine ⟨α a, ?_⟩
  simpa only [map_mul, map_inv, map_zpow] using congrArg α ha

theorem mem_squareRootSection_quotient_iff [Finite M]
    (O : Subgroup M) [O.Normal] (hO : Odd (Nat.card O))
    {y g : M} {a : ℕ} (hy : orderOf y = 2 ^ a) :
    QuotientGroup.mk' O g ∈ squareRootSection (QuotientGroup.mk' O y) ↔
      g ∈ squareRootSection y := by
  constructor
  · intro hg
    obtain ⟨h, z, hh, hz, hcentral, hconj⟩ := hg
    obtain ⟨b, hb⟩ := isConj_iff.mp hconj
    obtain ⟨b0, hb0⟩ := QuotientGroup.mk'_surjective O b
    have hx : QuotientGroup.mk' O (b0⁻¹ * g * b0) =
        QuotientGroup.mk' O y ^ h * z := by
      rw [map_mul, map_mul, map_inv, hb0, ← hb]
      group
    obtain ⟨c, v, hcv, hv, hvy⟩ :=
      CFSG.Wreathed.exists_conj_eq_zpow_mul_of_mk_eq hO hy hh hz hcentral hx
    refine ⟨h, v, hh, hv, Subgroup.mem_centralizer_singleton_iff.mpr hvy.eq, ?_⟩
    apply isConj_iff.mpr
    refine ⟨b0 * c⁻¹, ?_⟩
    rw [← hcv]
    group
  · exact map_mem_squareRootSection (QuotientGroup.mk' O)

theorem squareRootSection_preimage_quotient [Finite M]
    (O : Subgroup M) [O.Normal] (hO : Odd (Nat.card O))
    {y : M} {a : ℕ} (hy : orderOf y = 2 ^ a) :
    (QuotientGroup.mk' O) ⁻¹' squareRootSection (QuotientGroup.mk' O y) =
      squareRootSection y := by
  ext g
  exact mem_squareRootSection_quotient_iff O hO hy

theorem squareRootSection_coset [Finite M]
    (O : Subgroup M) [O.Normal] (hO : Odd (Nat.card O))
    {y g : M} {a : ℕ} (hy : orderOf y = 2 ^ a)
    (hg : QuotientGroup.mk' O g ∈ squareRootSection (QuotientGroup.mk' O y)) (o : O) :
    g * (o : M) ∈ squareRootSection y := by
  apply (mem_squareRootSection_quotient_iff O hO hy).mp
  simpa only [map_mul, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff (o : M)).mpr o.property, mul_one] using hg

variable {G : Type} [Group G] [Finite G]

theorem original_layer_section_lift
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (g : K) (gL : L) (hgL : (gL : K ⧸ O) = QuotientGroup.mk' O g)
    (hsection : gL ∈ squareRootSection
      (WreathCentralSquare.actualRoot (layerSylow S K hSK O L hindex)
        (layerCoordinates S e K hSK O hO L hindex))) :
    (g : G) ∈ squareRootSection (WreathCentralSquare.actualRoot S e) := by
  have himage := map_mem_squareRootSection L.subtype hsection
  change (gL : K ⧸ O) ∈ squareRootSection
    ((WreathCentralSquare.actualRoot (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex) : L) : K ⧸ O) at himage
  rw [hgL, layerRoot_coe] at himage
  have hlift := (mem_squareRootSection_quotient_iff O hO
    (coveringRoot_order n hn S e K hSK)).mp himage
  have hambient := map_mem_squareRootSection K.subtype hlift
  change (g : G) ∈ squareRootSection
    ((WreathCentralSquare.actualRoot (FullSylowCoveringObstruction.subgroupSylow S K hSK)
      (FullSylowCoveringObstruction.subgroupCoordinates S e K hSK) : K) : G) at hambient
  simpa only [coveringRoot_coe] using hambient

theorem original_layer_section_coset_lift
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (g : K) (gL : L) (hgL : (gL : K ⧸ O) = QuotientGroup.mk' O g)
    (hsection : gL ∈ squareRootSection
      (WreathCentralSquare.actualRoot (layerSylow S K hSK O L hindex)
        (layerCoordinates S e K hSK O hO L hindex))) (o : O) :
    (g : G) * ((o : K) : G) ∈ squareRootSection (WreathCentralSquare.actualRoot S e) := by
  have hcoset : (gL : K ⧸ O) = QuotientGroup.mk' O (g * (o : K)) := by
    simpa only [map_mul, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff (o : K)).mpr o.property, mul_one] using hgL
  have hlift := original_layer_section_lift n hn S e K hSK O hO L hindex
    (g * (o : K)) gL hcoset hsection
  simpa only [Subgroup.coe_mul] using hlift

end CFSG.Wreathed.SameFieldOddKernel
