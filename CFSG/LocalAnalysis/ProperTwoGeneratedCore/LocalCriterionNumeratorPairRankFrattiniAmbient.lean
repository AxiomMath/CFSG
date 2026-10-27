module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairGeneratedHull
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniDimensions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator LocalCriterionGeometry
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

@[expose, reducible]
def normalizerFrattiniBaseAction (P : Subgroup G) :
    MulDistribMulAction (Subgroup.normalizer (P : Set G)) P :=
  Subgroup.conjMulDistribMulActionOfLeNormalizer _ P le_rfl

@[expose] def ambientFrattiniInversion
    (P : Subgroup G) (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G)) : Prop :=
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  ∀ x : P ⧸ frattini P, (⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • x = x⁻¹

@[expose] def ambientFrattiniBounds [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    (W : Subgroup G) (hWP : W ≤ Subgroup.normalizer (P : Set G)) : Prop :=
  let := normalizerFrattiniBaseAction P
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let := frattiniQuotientAction (A := W) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  (∀ w : W, w ≠ 1 →
    let : IsElementaryAbelian p (actorFixedSubgroup (I := P ⧸ frattini P) w) :=
      elementary_subgroup (actorFixedSubgroup (I := P ⧸ frattini P) w)
    IsCyclic (actorFixedSubgroup (I := P ⧸ frattini P) w) ∧
      Nat.card (actorFixedSubgroup (I := P ⧸ frattini P) w) ≤ p ∧
        Module.finrank (ZMod p)
          (Additive (actorFixedSubgroup (I := P ⧸ frattini P) w)) ≤ 1) ∧
    Nat.card (P ⧸ frattini P) ≤ p ^ 3 ∧
      Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) ≤ 3

theorem ambient_fixed_subgroup_map (P : Subgroup G) (w : G)
    (hwP : w ∈ Subgroup.normalizer (P : Set G)) :
    let := normalizerFrattiniBaseAction P
    (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G))).map
      P.subtype = P ⊓ Subgroup.centralizer ({w} : Set G) := by
  let := normalizerFrattiniBaseAction P
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    change (a : G) * w = w * (a : G)
    have hfix : w * (a : G) * w⁻¹ = a := congrArg Subtype.val ha
    have hm := congrArg (fun y : G => y * w) hfix
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm
  · rintro ⟨hxP, hxw⟩
    refine ⟨⟨x, hxP⟩, ?_, rfl⟩
    apply Subtype.ext
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxw
    change w * x * w⁻¹ = x
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem ambient_fixed_commutator_map (P : Subgroup G) (w t : G)
    (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (ht : orderOf t = 2) :
    let := normalizerFrattiniBaseAction P
    (actorCommutatorSubgroup (⟨t, htP⟩ : Subgroup.normalizer (P : Set G))
      (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)))).map
        P.subtype = rightInvolutionCommutatorSubgroup t
          (P ⊓ Subgroup.centralizer ({w} : Set G)) := by
  let := normalizerFrattiniBaseAction P
  let K := actorCommutatorSubgroup (⟨t, htP⟩ : Subgroup.normalizer (P : Set G))
    (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)))
  let C := P ⊓ Subgroup.centralizer ({w} : Set G)
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply (actorCommutatorSubgroup_le _ _ _).2
    intro a ha
    have haw : (a : G) ∈ Subgroup.centralizer ({w} : Set G) := by
      have hmap : (a : G) ∈
          (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G))).map
            P.subtype := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      rw [ambient_fixed_subgroup_map P w hwP] at hmap
      exact hmap.2
    have hright : t⁻¹ * (a : G)⁻¹ * t * a ∈ rightInvolutionCommutatorSubgroup t C :=
      Subgroup.subset_closure ⟨⟨a, a.property, haw⟩, rfl⟩
    have hinv := (rightInvolutionCommutatorSubgroup t C).inv_mem hright
    change (a : G)⁻¹ * (t * (a : G) * t⁻¹) ∈ rightInvolutionCommutatorSubgroup t C
    simpa only [mul_inv_rev, inv_inv, htinv, mul_assoc] using hinv
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, rfl⟩
    let aP : P := ⟨a, a.property.1⟩
    have hafix : aP ∈ actorFixedSubgroup (I := P)
        (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)) := by
      apply Subtype.ext
      change w * (a : G) * w⁻¹ = a
      rw [← Subgroup.mem_centralizer_singleton_iff.mp a.property.2,
        mul_assoc, mul_inv_cancel, mul_one]
    have hgen := actorCommutatorSubgroup_generator_mem
      (⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) hafix
    have himage : ((aP⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • aP) : P) : G)
        ∈ K.map P.subtype := Subgroup.mem_map.mpr ⟨_, hgen, rfl⟩
    have hinv := (K.map P.subtype).inv_mem himage
    change ((a : G)⁻¹ * (t * (a : G) * t⁻¹))⁻¹ ∈ K.map P.subtype at hinv
    change t⁻¹ * (a : G)⁻¹ * t * a ∈ K.map P.subtype
    simpa only [mul_inv_rev, inv_inv, htinv, mul_assoc] using hinv

theorem right_involution_commutator_mono (t : G) {C D : Subgroup G} (hCD : C ≤ D) :
    rightInvolutionCommutatorSubgroup t C ≤ rightInvolutionCommutatorSubgroup t D := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨a, rfl⟩
  exact Subgroup.subset_closure ⟨⟨a, hCD a.property⟩, rfl⟩

theorem ambient_fixed_commutator_cyclic (I P : Subgroup G) (hPI : P ≤ I) (w t : G)
    (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (ht : orderOf t = 2)
    (hcyclic : IsCyclic (rightInvolutionCommutatorSubgroup t
      (I ⊓ Subgroup.centralizer ({w} : Set G)))) :
    let := normalizerFrattiniBaseAction P
    IsCyclic (actorCommutatorSubgroup (⟨t, htP⟩ : Subgroup.normalizer (P : Set G))
      (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)))) := by
  let := normalizerFrattiniBaseAction P
  let K := actorCommutatorSubgroup (⟨t, htP⟩ : Subgroup.normalizer (P : Set G))
    (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)))
  let := hcyclic
  have hkle : K.map P.subtype ≤ rightInvolutionCommutatorSubgroup t
      (I ⊓ Subgroup.centralizer ({w} : Set G)) := by
    rw [ambient_fixed_commutator_map P w t hwP htP ht]
    exact right_involution_commutator_mono t (inf_le_inf hPI le_rfl)
  let : IsCyclic (K.map P.subtype) := Subgroup.isCyclic_of_le hkle
  exact isCyclic_of_injective (P.subtype.subgroupMap K)
    (P.subtype.subgroupMap_injective K P.subtype_injective)

theorem ambient_frattini_four_group_bounds [Finite G] {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (I P : Subgroup G) (hPI : P ≤ I) (hP : IsPGroup p P)
    (W : Subgroup G) [IsKleinFour W] (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (t : G) (ht : orderOf t = 2) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hwt : ∀ w : W, Commute (w : G) t) (hinv : ambientFrattiniInversion P t htP)
    (hcyclic : ∀ w : W, w ≠ 1 →
      IsCyclic (rightInvolutionCommutatorSubgroup t
        (I ⊓ Subgroup.centralizer ({(w : G)} : Set G)))) :
    ambientFrattiniBounds P hP W hWP := by
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let : MulDistribMulAction W (P ⧸ frattini P) :=
    MulDistribMulAction.compHom (P ⧸ frattini P) (Subgroup.inclusion hWP)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  have hlocal (w : W) (hw : w ≠ 1) :
      IsCyclic (actorFixedSubgroup (I := P ⧸ frattini P) w) ∧
        Nat.card (actorFixedSubgroup (I := P ⧸ frattini P) w) ≤ p := by
    let wN : Subgroup.normalizer (P : Set G) := ⟨w, hWP w.property⟩
    let tN : Subgroup.normalizer (P : Set G) := ⟨t, htP⟩
    have hwsq : wN ^ 2 = 1 := by
      apply Subtype.ext
      change (w : G) ^ 2 = 1
      simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
        congrArg Subtype.val (IsKleinFour.mul_self w)
    have hcomm : Commute wN tN := by
      apply Subtype.ext
      exact (hwt w).eq
    have hc := ambient_fixed_commutator_cyclic I P hPI (w : G) t
      (hWP w.property) htP ht (hcyclic w hw)
    have hfixed := frattini_cyclic_fixed_card hP hpodd wN tN hwsq hcomm hinv hc
    exact ⟨hfixed.1, hfixed.2.2⟩
  change _ ∧ _ ∧ _
  refine ⟨?_, ?_⟩
  · intro w hw
    let : IsElementaryAbelian p (actorFixedSubgroup (I := P ⧸ frattini P) w) :=
      elementary_subgroup (actorFixedSubgroup (I := P ⧸ frattini P) w)
    obtain ⟨hc, hcard⟩ := hlocal w hw
    exact ⟨hc, hcard, elementary_finrank_le_of_card_le (n := 1)
      (by simpa only [pow_one] using hcard)⟩
  · exact klein_four_elementary_finrank_bound hpodd (fun w hw => (hlocal w hw).2)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
