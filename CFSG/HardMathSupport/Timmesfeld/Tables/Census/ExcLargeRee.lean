module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.TauCetiBridge
  CFSG.TauCetiBridge.ReeF4 TauCeti CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

theorem three_dvd_two_pow_odd_add_one (a : ℕ) : 3 ∣ 2 ^ (2 * a + 1) + 1 := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega

theorem threeTwoWitness_reeGamma
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ThreeTwoWitness (F4.reeGamma K a) := by
  have : Finite (ModGL F4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨hF0, -⟩ := largeReeParabolicFacts a K ha hK
  obtain ⟨-, -, -, -, -, hr0, -⟩ := largeRee_named_covers a K hK
  have hP₀Γ : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hQΓ : F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ≤ F4.reeGamma K a :=
    inf_le_right
  have h3 : 3 ∣ Nat.card ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf
      (F4.reeGamma K a)) := by
    have h1 := three_dvd_two_pow_odd_add_one a
    rw [← hK, ← hr0] at h1
    exact h1.trans (by rw [Subgroup.relIndex]; exact Subgroup.index_dvd_card _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxP := Subgroup.mem_subgroupOf.1 x.2
  have hnorm := Subgroup.mem_normalizer_iff.1 (hF0.normalizes hxP)
  refine ThreeTwoWitness.mk'
    (P := (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a))
    ?_ ?_ (x := ((x : ↥(F4.reeGamma K a)))) ?_ ?_
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := hF0.nonabelian
    have h1 : ∀ w ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩, w = 1 := by
      intro w hw
      have : (⟨w, hQΓ hw⟩ : ↥(F4.reeGamma K a)) ∈ (F4.reeFixedOrbitComplementUnipotent K a
          ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) := Subgroup.mem_subgroupOf.2 hw
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    exact huv (by rw [h1 u hu, h1 v hv])
  · exact IsPGroup.of_injective hF0.pGroup (Subgroup.subgroupOfEquivOfLe hQΓ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQΓ).injective
  · rw [Subgroup.orderOf_coe]
    exact hx
  · refine mem_normalizer_of_conj_le fun y hy => ?_
    exact Subgroup.mem_subgroupOf.2 ((hnorm y.1).1 (Subgroup.mem_subgroupOf.1 hy))

theorem threeTwoWitness_largeRee_model
    {X : Type} [Group X] {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f) : ThreeTwoWitness X := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  exact ThreeTwoWitness.of_mulEquiv e.symm (threeTwoWitness_reeGamma ha (by rw [hK, hfa]))

theorem reeTitsModel_reeF4_of_equiv
    {X : Type} [Group X] {m : ℕ} {hv : (LieTypeIndex.reeF4 m).Valid}
    (hadm : StatedLieAdmissible .twistedF4 0 2 (2 * m + 1))
    (e : X ≃* (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) :
    ReeTitsModel X .twistedF4 2 (2 * m + 1) := by
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  exact ⟨hadm, m, rfl, (ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
    ⟨(e.trans e₁).trans (nativeModelEquiv m).symm⟩⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
