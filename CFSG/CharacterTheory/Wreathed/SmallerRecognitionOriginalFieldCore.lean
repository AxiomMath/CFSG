module

public import CFSG.CharacterTheory.Wreathed.SimpleOddIndexQuotient
public import CFSG.CharacterTheory.Wreathed.FullSylowCoveringObstruction
public import CFSG.CharacterTheory.Wreathed.ReducedCentralizerInclusion
public import CFSG.CharacterTheory.Wreathed.FullCentralizerFromProjectiveModel
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.GroupTheory.LocalCores.Fitting

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open scoped Classical
open FullSylowCoveringObstruction SimpleOddIndexQuotient ReducedCentralizerInclusion

variable {G : Type} [Group G]

@[expose] def SmallerWreathedRecognition (G : Type) : Prop :=
  ∀ (J : Type) [Group J] [Finite J] [IsSimpleGroup J],
    (∃ a b : J, a * b ≠ b * a) → Nat.card J < Nat.card G →
    ∀ (a : ℕ), 2 ≤ a → ∀ (T : Sylow 2 J), Nonempty (T ≃* Wreath (2 ^ a)) →
      ∃ r b : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ b ∧
        ((r ^ b % 4 = 1 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL 3 r b) ∨
          (r ^ b % 4 = 3 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSU 3 r b))

theorem coveringInvolution_order (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    orderOf (coveringInvolution n S e K hSK) = 2 := by
  rw [← Subgroup.orderOf_coe, coveringInvolution_coe]
  exact (orderOf_injective _ (wreathModelHom_injective S e) _).trans
    (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem proper_core_quotient_subgroup_card_lt [Finite G] (K : Subgroup G) (hK : K < ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) : Nat.card L < Nat.card G := by
  have hquotient : Nat.card (K ⧸ CFSG.oddCore K) ≤ Nat.card K :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' (CFSG.oddCore K))
      (QuotientGroup.mk'_surjective _)
  have hproper : Nat.card K < Nat.card G := by
    simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt hK
  exact lt_of_le_of_lt ((Subgroup.card_le_card_group L).trans hquotient) hproper

theorem smaller_core_quotient_model [Finite G]
    (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (hproper : K < ⊤)
    (hfusion : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ D : Subgroup K, D.index ≠ 2) :
    let O := CFSG.oddCore K
    let X := K ⧸ O
    let L := involutionClosure X
    IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧ Odd L.index ∧
      Subgroup.centralizer (L : Set X) = ⊥ ∧ Nat.card L < Nat.card G ∧
      ∃ r b : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ b ∧
        ((r ^ b % 4 = 1 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 3 r b) ∨
          (r ^ b % 4 = 3 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSU 3 r b)) := by
  let T := subgroupSylow S K hSK
  let eT := subgroupCoordinates S e K hSK
  obtain ⟨_, _, _, _, hsimple, hnonab, hodd, _, hcentralizer, _, _, _,
    TL, _, _, _, eL, _, _⟩ :=
    one_involution_class_no_index_two_has_simple_odd_index_core_quotient
      n hn T eT hfusion hindex
  let L := involutionClosure (K ⧸ CFSG.oddCore K)
  let : IsSimpleGroup L := hsimple
  have hnoncomm : ∃ a b : L, a * b ≠ b * a := by
    by_contra h
    apply hnonab
    apply isMulCommutative_iff.mpr
    intro a b
    exact not_not.mp (fun hab => h ⟨a, b, hab⟩)
  have hcard : Nat.card L < Nat.card G := proper_core_quotient_subgroup_card_lt K hproper L
  exact ⟨hsimple, hnonab, hodd, hcentralizer, hcard,
    hrec L hnoncomm hcard n hn TL ⟨eL⟩⟩

@[expose] def coveringCentralizerInclusion (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.centralizer {coveringInvolution n S e K hSK} →*
      involutionCentralizer n S e where
  toFun c := ⟨(c.val : G), Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coveringCentralizerInclusion_coe (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (c : Subgroup.centralizer {coveringInvolution n S e K hSK}) :
    (coveringCentralizerInclusion n S e K hSK c : G) = (c.val : G) := rfl

theorem coveringCentralizer_quotient_surjective (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    Function.Surjective ((centralizerOddCoreMap n S e).comp
      (coveringCentralizerInclusion n S e K hSK)) := by
  intro y
  obtain ⟨c, hc⟩ := covering_quotient_restriction_surjective
    (centralizerOddCore n S e) (K.subgroupOf (involutionCentralizer n S e)) hcover y
  let k : K := ⟨(c.val : G), c.property⟩
  have hk : k ∈ Subgroup.centralizer {coveringInvolution n S e K hSK} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.val.property
  exact ⟨⟨k, hk⟩, hc⟩

@[expose] def coveringCentralizerIntersectionEquiv (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.centralizer {coveringInvolution n S e K hSK} ≃*
    K.subgroupOf (involutionCentralizer n S e) where
  toFun c := ⟨coveringCentralizerInclusion n S e K hSK c, c.val.property⟩
  invFun c := ⟨⟨(c.val : G), c.property⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem coveringCentralizer_quotient_ker [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    ((centralizerOddCoreMap n S e).comp
      (coveringCentralizerInclusion n S e K hSK)).ker =
        CFSG.oddCore (Subgroup.centralizer {coveringInvolution n S e K hSK}) := by
  let E := coveringCentralizerIntersectionEquiv n S e K hSK
  have hE : (CFSG.oddCore (Subgroup.centralizer {coveringInvolution n S e K hSK})).map
      E.toMonoidHom = CFSG.oddCore (K.subgroupOf (involutionCentralizer n S e)) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant E
  have hcore := covering_odd_core_eq_kernel_intersection
    (K.subgroupOf (involutionCentralizer n S e)) hcover
  ext c
  change centralizerOddCoreMap n S e
    (coveringCentralizerInclusion n S e K hSK c) = 1 ↔ _
  rw [← Subgroup.mem_map_iff_mem (f := E.toMonoidHom) E.injective, hE, hcore]
  exact QuotientGroup.eq_one_iff (N := centralizerOddCore n S e)
    (coveringCentralizerInclusion n S e K hSK c)

@[expose] def coveringReducedCentralizerEquiv [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    Subgroup.centralizer {coveringInvolution n S e K hSK} ⧸
      CFSG.oddCore (Subgroup.centralizer {coveringInvolution n S e K hSK}) ≃*
        centralizerOddCoreQuotient n S e :=
  (QuotientGroup.quotientMulEquivOfEq
    (coveringCentralizer_quotient_ker n S e K hSK hcover).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (coveringCentralizer_quotient_surjective n S e K hSK hcover))

theorem coveringReducedCentralizerEquiv_mk [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (c : Subgroup.centralizer {coveringInvolution n S e K hSK}) :
    coveringReducedCentralizerEquiv n S e K hSK hcover
      (QuotientGroup.mk' (CFSG.oddCore
        (Subgroup.centralizer {coveringInvolution n S e K hSK})) c) =
      centralizerOddCoreMap n S e (coveringCentralizerInclusion n S e K hSK c) := rfl

@[expose] def simpleReducedCentralizerInclusion [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :=
  (coveringReducedCentralizerEquiv n S e K hSK hcover).toMonoidHom.comp
    (reducedCentralizerInjection (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
      (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK))

theorem simpleReducedCentralizerInclusion_injective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    Function.Injective (simpleReducedCentralizerInclusion n hn S e K hSK hcover L hodd) :=
  (coveringReducedCentralizerEquiv n S e K hSK hcover).injective.comp
    (reducedCentralizerInjection_injective (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
      (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK))

theorem simpleReducedCentralizerInclusion_normal [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    (simpleReducedCentralizerInclusion n hn S e K hSK hcover L hodd).range.Normal := by
  rw [simpleReducedCentralizerInclusion, MonoidHom.range_comp]
  exact Subgroup.Normal.map
    (reducedCentralizerInjection_normal (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
    (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK))
    _ (coveringReducedCentralizerEquiv n S e K hSK hcover).surjective

theorem simpleReducedCentralizerInclusion_odd_index [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    Odd (simpleReducedCentralizerInclusion n hn S e K hSK hcover L hodd).range.index := by
  rw [simpleReducedCentralizerInclusion, MonoidHom.range_comp,
    Subgroup.index_map_of_bijective (coveringReducedCentralizerEquiv n S e K hSK hcover).bijective]
  exact reducedCentralizerInjection_odd_index (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
    (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK)

theorem simpleReducedCentralizerInclusion_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index)
    (c : Subgroup.centralizer {coveringInvolution n S e K hSK})
    (b : Subgroup.centralizer ({(⟨QuotientGroup.mk' (CFSG.oddCore K)
      (coveringInvolution n S e K hSK), quotient_involution_mem (CFSG.oddCore K)
        (actual_oddCore_odd K) L hodd _ (coveringInvolution_order n hn S e K hSK)⟩ : L)} : Set L))
    (hcb : QuotientGroup.mk' (CFSG.oddCore K) (c.val : K) = (b.val : K ⧸ CFSG.oddCore K)) :
    simpleReducedCentralizerInclusion n hn S e K hSK hcover L hodd
      (QuotientGroup.mk' (CFSG.oddCore _) b) =
      centralizerOddCoreMap n S e (coveringCentralizerInclusion n S e K hSK c) := by
  let E := coveringReducedCentralizerEquiv n S e K hSK hcover
  let psi := reducedCentralizerEquiv (CFSG.oddCore K) (actual_oddCore_odd K)
    (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK)
  have h := reducedCentralizerInjection_mk (CFSG.oddCore K) (actual_oddCore_odd K)
    L hodd (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK) b
  have heq : OddNormalQuotientInvolutions.centralizerQuotient (CFSG.oddCore K)
      (coveringInvolution n S e K hSK) c = centralizerInclusion L _ _ b :=
    Subtype.ext hcb
  have hin : reducedCentralizerInjection (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
      (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK)
        (QuotientGroup.mk' (CFSG.oddCore _) b) =
      QuotientGroup.mk' (CFSG.oddCore _) c := by
    apply psi.injective
    exact h.trans (by rw [reducedCentralizerEquiv_mk, heq])
  rw [simpleReducedCentralizerInclusion, MonoidHom.comp_apply, hin]
  exact coveringReducedCentralizerEquiv_mk n S e K hSK hcover c

end CFSG.Wreathed.SmallerRecognitionOriginalField
