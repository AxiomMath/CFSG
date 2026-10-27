module

public import CFSG.LocalAnalysis.LargeEvenClassification.MaximalAbelian
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoAction

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem selfCentralizing_conj_subgroup_generator_bound {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (SubgroupOfAmbient : Subgroup Ambient) {normalBound actionBound : ℕ}
    (hnormalBound : pGeneratorRank prime Normal ≤ normalBound)
    (hactionBound : pGeneratorRank prime
      ((MulAut.conjNormal (H := Normal)).comp SubgroupOfAmbient.subtype).range ≤ actionBound) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧
        generators.card ≤ normalBound + actionBound := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let action := (MulAut.conjNormal (H := Normal)).comp SubgroupOfAmbient.subtype
  let quotient := action.rangeRestrict
  have hkernel : quotient.ker = Normal.comap SubgroupOfAmbient.subtype := by
    rw [MonoidHom.ker_rangeRestrict]
    change ((MulAut.conjNormal (H := Normal)).ker).comap SubgroupOfAmbient.subtype = _
    rw [conjNormal_ker_eq_centralizer Normal, hselfCentralizing]
  let embedding : quotient.ker →* Normal := {
    toFun := fun element => ⟨element.val.val, by
      exact hkernel.le element.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinjective : Function.Injective embedding := by
    intro first second heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun normalElement : Normal => (normalElement : Ambient)) heq
  let : CommGroup quotient.ker := { (inferInstance : Group quotient.ker) with
    mul_comm := fun first second => hinjective (by rw [map_mul, map_mul, mul_comm]) }
  have hkernelRank := (commutative_pGeneratorRank_embedding_le hprime
    (hpgroup.to_subgroup Normal) embedding hinjective).trans hnormalBound
  have hsource := hpgroup.to_subgroup SubgroupOfAmbient
  have hkernelGroup := hsource.to_subgroup quotient.ker
  have himageGroup := hsource.of_surjective quotient action.rangeRestrict_surjective
  obtain ⟨kernelGenerators, hkernelGenerates, hkernelCard⟩ :=
    pGeneratorRank_generators hprime hkernelGroup
  obtain ⟨imageGenerators, himageGenerates, himageCard⟩ :=
    pGeneratorRank_generators hprime himageGroup
  exact extension_generator_bound quotient action.rangeRestrict_surjective
    ⟨kernelGenerators, hkernelGenerates, hkernelCard.trans_le hkernelRank⟩
    ⟨imageGenerators, himageGenerates, himageCard.trans_le hactionBound⟩

theorem cyclic_maximal_abelian_normal_three_generators {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] [IsCyclic Normal]
    (hmaximal : ∀ Larger : Subgroup Ambient,
      Larger.Normal → IsMulCommutative Larger → Normal ≤ Larger → Larger ≤ Normal)
    (SubgroupOfAmbient : Subgroup Ambient) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧ generators.card ≤ 3 := by
  have hcommutative : IsMulCommutative Normal := inferInstance
  have hselfCentralizing := maximal_abelian_normal_selfCentralizing Nat.prime_two hpgroup
    Normal hcommutative hmaximal
  exact selfCentralizing_conj_subgroup_generator_bound Nat.prime_two hpgroup Normal hcommutative
    hselfCentralizing SubgroupOfAmbient
    (cyclic_pGeneratorRank_le_one Nat.prime_two (hpgroup.to_subgroup Normal))
    (cyclic_two_aut_subgroup_generator_rank (hpgroup.to_subgroup Normal)
      ((MulAut.conjNormal (H := Normal)).comp SubgroupOfAmbient.subtype).range)

end CFSG.LargeEvenClassification.Helpers
