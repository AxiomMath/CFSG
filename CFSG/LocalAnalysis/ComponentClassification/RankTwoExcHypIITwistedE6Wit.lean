module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIE6Wit
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem exists_ne_fixed {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : ∃ d : K, σ d ≠ d := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  by_contra hne
  have h : ∀ d : K, σ d = d := fun d => not_not.1 fun hd => hne ⟨d, hd⟩
  have hk := CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK hσ
  have hle := Nat.card_le_card_of_surjective
    (fun c : RingHom.eqLocusField σ (RingHom.id K) => (c : K)) (fun c => ⟨⟨c, h c⟩, rfl⟩)
  rw [hk, hK] at hle
  have h2 : 2 ≤ 2 ^ f := calc
    2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  nlinarith

theorem frob_frob {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (c : K) : σ (σ c) = c := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem e6Alpha_pair_mem_graphFixedRootGroup
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (d : K) :
    pinnedX TwistTag.E6.tag K (e6Alpha false) d *
        pinnedX TwistTag.E6.tag K (e6Alpha true) (σ d) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have hU : ∀ (j : Bool) (c : K),
      pinnedX TwistTag.E6.tag K (e6Alpha j) c ∈ posUnipotent TwistTag.E6.tag K := fun j c =>
    pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
      ⟨isRoot_e6Alpha j, by rw [height_e6Alpha]; exact one_pos⟩ c
  obtain ⟨hρ1, hρ2, -, -⟩ := permLattice_e6Alpha
  refine graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
    ⟨mul_mem (hU false d) (hU true (σ d)), (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _), ?_⟩⟩)
  rw [map_mul, E6GraphRadical.twistHom_pinnedX_of_two h2 σ (isRoot_e6Alpha false),
    E6GraphRadical.twistHom_pinnedX_of_two h2 σ (isRoot_e6Alpha true), hρ1, hρ2, hσσ]
  exact (commute_e6Alpha_pair' d (σ d)).1.eq.symm

theorem negPair_mem_graphFixedRootGroup
    (h2 : (2 : K) = 0) (σ : K →+* K) :
    pinnedX TwistTag.E6.tag K (-e6Alpha false) 1 *
        pinnedX TwistTag.E6.tag K (-e6Alpha true) 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have hU : ∀ j : Bool,
      pinnedX TwistTag.E6.tag K (-e6Alpha j) 1 ∈ negUnipotent TwistTag.E6.tag K := fun j =>
    pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ height β < 0})
      ⟨isRoot_neg_iff.2 (isRoot_e6Alpha j), by rw [height_neg, height_e6Alpha]; norm_num⟩ 1
  obtain ⟨-, -, hρ3, hρ4⟩ := permLattice_e6Alpha
  refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
    ⟨mul_mem (hU false) (hU true), (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _), ?_⟩⟩)
  rw [map_mul,
    E6GraphRadical.twistHom_pinnedX_of_two h2 σ (isRoot_neg_iff.2 (isRoot_e6Alpha false)),
    E6GraphRadical.twistHom_pinnedX_of_two h2 σ (isRoot_neg_iff.2 (isRoot_e6Alpha true)), hρ3,
    hρ4, map_one]
  exact (commute_e6Alpha_pair' (1 : K) 1).2.eq.symm

theorem secondGraphWitness_twistedE6
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hη : ∀ h, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) :
    SecondGraphWitness
      (MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) * η) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (show 1 ≤ 2 * f by omega) (by rw [hK, ← pow_mul, mul_comm])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hk := CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK hσ'
  have : CharP (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  obtain ⟨-, ⟨η₀, hη₀, -, hJC, hfixJ, -⟩, -⟩ := even_E6_twisted_E6_canonical_graph_fixed_subgroup f
    hf (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ'
  have hξ : ∀ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ((MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) * η) g :
        ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
          (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
            (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ := fun g => by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη]
  have hJ : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g →
        g ∈ (twistedFixedGroup TwistTag.E6 (RingHom.eqLocusField σ.toRingHom (RingHom.id K))
          (RingHom.id _)).map (baseChangeGL (algebraMap _ K)) := fun g hg hP =>
    (hfixJ ⟨g, hg⟩).1 (Subtype.ext (by rw [hη₀]; exact hP))
  have hCa : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ adjointGroup TwistTag.E6.tag K :=
    fun g hg => (graphFixedRootGroup_le _ _ _ hg).1
  obtain ⟨d, hd⟩ := exists_ne_fixed hf hK hσ'
  have hd' : d + σ.toRingHom d ≠ 0 := fun h =>
    hd ((eq_neg_of_add_eq_zero_right h).trans (CharTwo.neg_eq d))
  exact secondGraphWitness_of (exceptional_fixed_center_trivial TwistTag.E6 K σ) hξ
    (fun E₁ hne h2' hfix hn =>
      exists_commute_tests_of_baseChange hCa hJC hJ hξ hne h2' hfix hn)
    hd' (e6Alpha_pair_mem_graphFixedRootGroup h2 (frob_frob hK hσ') d)
    (negPair_mem_graphFixedRootGroup h2 σ.toRingHom)

end CFSG.ComponentClassification.RankTwoExcHypII
