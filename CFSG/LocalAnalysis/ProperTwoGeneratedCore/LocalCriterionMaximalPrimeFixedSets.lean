module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def pointFixedSet (H M : Subgroup G) : Set (pointRightCosetSpace H) :=
  {omega | ∀ m ∈ M, pointRightCosetMul H omega m = omega}

theorem mem_pointFixedSet_iff (H M : Subgroup G) (omega : pointRightCosetSpace H) :
    omega ∈ pointFixedSet H M ↔ M ≤ rightCosetStabilizer H omega := by
  constructor
  · intro h m hm
    exact (mem_point_right_stabilizer_iff H omega m).mpr (h m hm)
  · intro h m hm
    exact (mem_point_right_stabilizer_iff H omega m).mp (h hm)

theorem pointFixedSet_antitone {H M Q : Subgroup G} (hMQ : M ≤ Q) :
    pointFixedSet H Q ⊆ pointFixedSet H M := fun _ h m hm => h m (hMQ hm)

theorem normalizer_preserves_pointFixedSet {H M : Subgroup G}
    {n : G} (hn : n ∈ Subgroup.normalizer (M : Set G))
    {omega : pointRightCosetSpace H} (homega : omega ∈ pointFixedSet H M) :
    pointRightCosetMul H omega n ∈ pointFixedSet H M := by
  intro m hm
  have hconj : n * m * n⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hn m).mp hm
  calc
    pointRightCosetMul H (pointRightCosetMul H omega n) m =
        pointRightCosetMul H omega (n * m) := pointRightCosetMul_mul H omega n m
    _ = pointRightCosetMul H (pointRightCosetMul H omega (n * m * n⁻¹)) n := by
      rw [pointRightCosetMul_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = pointRightCosetMul H omega n := by rw [homega _ hconj]

@[expose] def pointFixedSetNormalizerEquiv (H M : Subgroup G)
    (n : Subgroup.normalizer (M : Set G)) : pointFixedSet H M ≃ pointFixedSet H M where
  toFun omega := ⟨pointRightCosetMul H omega.val n.val,
    normalizer_preserves_pointFixedSet n.property omega.property⟩
  invFun omega := ⟨pointRightCosetMul H omega.val n.val⁻¹,
    normalizer_preserves_pointFixedSet n⁻¹.property omega.property⟩
  left_inv omega := by
    apply Subtype.ext
    simp only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]
  right_inv omega := by
    apply Subtype.ext
    simp only [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one]

theorem class_centralizer_has_pointFixedSet_point [Finite G]
    {H M : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (hs : s ∈ involutionPointClass z) (hcentral : M ≤ Subgroup.centralizer ({s} : Set G)) :
    ∃ omega ∈ pointFixedSet H M, pointRightCosetMul H omega s = omega := by
  have huniq := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨omega, hfix, hunique⟩ := huniq s hs
  refine ⟨omega, ?_, hfix⟩
  intro m hm
  have hconj : rightConjugateElem s m = s := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hcentral hm)
    simp only [rightConjugateElem, mul_assoc]
    rw [← hc, inv_mul_cancel_left]
  have hf := point_right_fixed_conjugate hfix m
  rw [hconj] at hf
  exact hunique _ hf

theorem centralizes_of_conjugacyWithin_card_one [Finite G]
    (M : Subgroup G) (s : G) (hcard : Nat.card (conjugacyWithin M s) = 1) :
    M ≤ Subgroup.centralizer ({s} : Set G) := by
  have hidx : (Subgroup.centralizer ({s} : Set G)).relIndex M = 1 := by
    change ((Subgroup.centralizer ({s} : Set G)).subgroupOf M).index = 1
    rw [← conjugacyWithin_card_eq_centralizer_index]
    exact hcard
  have htop : (Subgroup.centralizer ({s} : Set G)).subgroupOf M = ⊤ :=
    Subgroup.index_eq_one.mp hidx
  intro m hm
  have hmem : (⟨m, hm⟩ : M) ∈ (Subgroup.centralizer ({s} : Set G)).subgroupOf M := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

@[expose, instance_reducible] def pointSubgroupInverseRightAction (H M : Subgroup G) :
    MulAction M (pointRightCosetSpace H) where
  smul m omega := pointRightCosetMul H omega (m.val)⁻¹
  one_smul omega := by
    change pointRightCosetMul H omega ((1 : M) : G)⁻¹ = omega
    simp only [Subgroup.coe_one, inv_one, pointRightCosetMul_one]
  mul_smul m n omega := by
    change pointRightCosetMul H omega ((m * n : M) : G)⁻¹ =
      pointRightCosetMul H (pointRightCosetMul H omega (n : G)⁻¹) (m : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, pointRightCosetMul_mul]

theorem pointInverseAction_fixed_iff (H M : Subgroup G) (omega : pointRightCosetSpace H) :
    (letI := pointSubgroupInverseRightAction H M
     omega ∈ MulAction.fixedPoints M (pointRightCosetSpace H)) ↔
      omega ∈ pointFixedSet H M := by
  change (∀ m : M, pointRightCosetMul H omega (m.val)⁻¹ = omega) ↔ _
  constructor
  · intro hf m hm
    simpa only [Subgroup.coe_inv, inv_inv] using hf (⟨m, hm⟩ : M)⁻¹
  · intro hf m
    exact hf m.val⁻¹ (M.inv_mem m.property)

theorem pointFixedSet_card_modEq [Finite G] (p : ℕ) (hp : p.Prime)
    (H M : Subgroup G) (hM : IsPGroup p M) :
    Nat.card (pointRightCosetSpace H) ≡ Nat.card (pointFixedSet H M) [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  let := pointSubgroupInverseRightAction H M
  have hset : MulAction.fixedPoints M (pointRightCosetSpace H) = pointFixedSet H M := by
    ext omega
    exact pointInverseAction_fixed_iff H M omega
  have hc := hM.card_modEq_card_fixedPoints (pointRightCosetSpace H)
  rw [hset] at hc
  exact hc

@[expose, instance_reducible] def pointInvariantSetInverseRightAction (H A : Subgroup G)
    (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta, pointRightCosetMul H omega a ∈ Delta) :
    MulAction A Delta where
  smul a omega := ⟨pointRightCosetMul H omega.val a.val⁻¹,
    hstable _ (A.inv_mem a.property) _ omega.property⟩
  one_smul omega := by
    apply Subtype.ext
    change pointRightCosetMul H omega.val ((1 : A) : G)⁻¹ = omega.val
    simp only [Subgroup.coe_one, inv_one, pointRightCosetMul_one]
  mul_smul a b omega := by
    apply Subtype.ext
    change pointRightCosetMul H omega.val ((a * b : A) : G)⁻¹ =
      pointRightCosetMul H (pointRightCosetMul H omega.val (b : G)⁻¹) (a : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, pointRightCosetMul_mul]

theorem pointFixedSet_restricted_card_modEq [Finite G]
    (p : ℕ) (hp : p.Prime) (H M Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQN : Q ≤ Subgroup.normalizer (M : Set G)) :
    Nat.card (pointFixedSet H M) ≡
      Nat.card (pointFixedSet H M ∩ pointFixedSet H Q : Set (pointRightCosetSpace H)) [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  let := pointInvariantSetInverseRightAction H Q (pointFixedSet H M)
    (fun q hq omega homega => normalizer_preserves_pointFixedSet (hQN hq) homega)
  have hc := hQ.card_modEq_card_fixedPoints (pointFixedSet H M)
  have he : MulAction.fixedPoints Q (pointFixedSet H M) ≃
      (pointFixedSet H M ∩ pointFixedSet H Q : Set (pointRightCosetSpace H)) :=
    { toFun := fun omega => ⟨omega.val.val, omega.val.property, by
        intro q hq
        have hh := MulAction.mem_fixedPoints.mp omega.property (⟨q, hq⟩ : Q)⁻¹
        change (⟨pointRightCosetMul H omega.val.val (((⟨q, hq⟩ : Q)⁻¹ : Q) : G)⁻¹,
          _⟩ : pointFixedSet H M) = omega.val at hh
        simpa only [Subgroup.coe_inv, inv_inv] using congrArg Subtype.val hh⟩
      invFun := fun omega => ⟨⟨omega.val, omega.property.1⟩, by
        intro q
        apply Subtype.ext
        exact omega.property.2 q.val⁻¹ (Q.inv_mem q.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr he] at hc
  exact hc

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
