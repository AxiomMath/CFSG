module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Layer
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.D4G2All
public import CFSG.LieType.Steinberg.G2.Perfect
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]

theorem mem_fixSubgroup_d4Graph_one_iff {x : adjointGroup Tag.D4 K} :
    x ∈ fixSubgroup (d4Graph K 1) ↔
      (x : ModGL Tag.D4 K) ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) := by
  have h : Units.map (entrywiseHom (RingHom.id K)) (x : ModGL Tag.D4 K) = x :=
    Units.ext (entrywise_id _)
  have e : twistHom TwistTag.D4 K (RingHom.id K) (x : ModGL Tag.D4 K) =
      d4P K * (x : ModGL Tag.D4 K) * (d4P K)⁻¹ := by
    change d4P K * Units.map (entrywiseHom (RingHom.id K)) (x : ModGL Tag.D4 K) *
      (d4P K)⁻¹ = _
    rw [h]
  rw [mem_fixSubgroup, Subtype.ext_iff, coe_d4Graph, pow_one]
  refine ⟨fun hx => ⟨x.2, ?_⟩, fun hx => ?_⟩
  · show twistHom TwistTag.D4 K (RingHom.id K) (x : ModGL Tag.D4 K) = (x : ModGL Tag.D4 K)
    rw [e]
    exact hx
  · have h2 : twistHom TwistTag.D4 K (RingHom.id K) (x : ModGL Tag.D4 K) =
        (x : ModGL Tag.D4 K) := hx.2
    rw [e] at h2
    exact h2

@[expose] def fixSubgroupToTwisted :
    ↥(fixSubgroup (d4Graph K 1)) →*
      ↥(twistedFixedGroup TwistTag.D4 K (RingHom.id K)) where
  toFun x := ⟨x.1.1, mem_fixSubgroup_d4Graph_one_iff.1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fixSubgroupToTwisted_bijective :
    Function.Bijective (fixSubgroupToTwisted (K := K)) :=
  ⟨fun a b h => by
      have h' := congrArg Subtype.val h
      apply Subtype.ext
      apply Subtype.ext
      exact h',
    fun g => ⟨⟨⟨g.1, g.2.1⟩, mem_fixSubgroup_d4Graph_one_iff.2 g.2⟩, rfl⟩⟩

variable (K) in
@[expose] noncomputable def fixSubgroupEquivTwisted :
    ↥(fixSubgroup (d4Graph K 1)) ≃* ↥(twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :=
  MulEquiv.ofBijective fixSubgroupToTwisted fixSubgroupToTwisted_bijective

variable (K) in
@[expose] noncomputable def fixSubgroupEquivG2 (hK3 : 3 ≤ Nat.card K) :
    ↥(fixSubgroup (d4Graph K 1)) ≃* ↥(adjointGroup Tag.G2 K) :=
  (fixSubgroupEquivTwisted K).trans
    (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.d4FixedG2EquivAll K
      (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast hK3))

theorem isQuasisimple_fixSubgroup_d4Graph_one (hK3 : 3 ≤ Nat.card K) :
    CFSG.IsQuasisimple ↥(fixSubgroup (d4Graph K 1)) :=
  CFSG.IsQuasisimple.of_mulEquiv (fixSubgroupEquivG2 K hK3)
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3)

theorem two_eq_zero_of_card_eq_two (h2 : Nat.card K = 2) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact h2
  have hr : ringChar K = 2 := (FiniteField.even_card_iff_char_two (F := K)).2 (by rw [hc])
  have : CharP K 2 := ringChar.of_eq hr
  exact_mod_cast CharP.cast_eq_zero K 2

theorem conj_pow_two_eq_iff {M : Type*} [Group M] (P X : M) (hP : P ^ 3 = 1) :
    P ^ 2 * X * (P ^ 2)⁻¹ = X ↔ P ^ 1 * X * (P ^ 1)⁻¹ = X := by
  have h2 : (P ^ 2)⁻¹ = P := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hP)
  have h1 : P⁻¹ = P ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hP)
  rw [h2, pow_one, h1]
  constructor
  · intro h
    calc P * X * P ^ 2 = P * (P ^ 2 * X * P) * P ^ 2 := by rw [h]
      _ = P ^ 3 * X * P ^ 3 := by group
      _ = X := by rw [hP]; group
  · intro h
    calc P ^ 2 * X * P = P ^ 2 * (P * X * P ^ 2) * P := by rw [h]
      _ = P ^ 3 * X * P ^ 3 := by group
      _ = X := by rw [hP]; group

theorem fixSubgroup_d4Graph_two : fixSubgroup (d4Graph K 2) = fixSubgroup (d4Graph K 1) := by
  have hP3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  ext x
  rw [mem_fixSubgroup, mem_fixSubgroup, Subtype.ext_iff, Subtype.ext_iff, coe_d4Graph,
    coe_d4Graph]
  exact conj_pow_two_eq_iff _ _ hP3

section G2

variable {S : Type*} [Group S] {k : Type} [Field k] [Finite k]

theorem perfectInLayer_of_mulEquiv_g2_of_three_le (β : MulAut S) (hk : 3 ≤ Nat.card k)
    (e : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 k)) : PerfectInLayer β :=
  perfectInLayer_of_isQuasisimple_fixSubgroup _
    (CFSG.IsQuasisimple.of_mulEquiv e
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k hk))

theorem perfectInLayer_of_mulEquiv_g2_of_card_two (β : MulAut S)
    (h2 : Nat.card k = 2) (e : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 k)) :
    PerfectInLayer β := by
  classical
  have hDc : (commutator ↥(adjointGroup Tag.G2 k)).map (adjointGroup Tag.G2 k).subtype =
      ⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ := by
    rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hsimpleA : IsSimpleGroup ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ := by
    have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k h2
    rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM).2
    all_goals exact absurd h0 (by norm_num)
  have hmap : (commutator ↥(fixSubgroup β)).map e.toMonoidHom =
      commutator ↥(adjointGroup Tag.G2 k) := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    rfl
  let e1 : ↥(commutator ↥(fixSubgroup β)) ≃* ↥(commutator ↥(adjointGroup Tag.G2 k)) :=
    ((commutator ↥(fixSubgroup β)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  let e2 : ↥(commutator ↥(adjointGroup Tag.G2 k)) ≃*
      ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ :=
    ((commutator ↥(adjointGroup Tag.G2 k)).equivMapOfInjective (adjointGroup Tag.G2 k).subtype
      (adjointGroup Tag.G2 k).subtype_injective).trans (MulEquiv.subgroupCongr hDc)
  exact perfectInLayer_of_isSimpleGroup_commutator β (e1.trans e2).isSimpleGroup

theorem perfectInLayer_of_mulEquiv_g2 (β : MulAut S)
    (e : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.G2 k)) : PerfectInLayer β := by
  by_cases h : 3 ≤ Nat.card k
  · exact perfectInLayer_of_mulEquiv_g2_of_three_le β h e
  · have h2 : Nat.card k = 2 := by
      have := Finite.one_lt_card (α := k)
      omega
    exact perfectInLayer_of_mulEquiv_g2_of_card_two β h2 e

end G2

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
