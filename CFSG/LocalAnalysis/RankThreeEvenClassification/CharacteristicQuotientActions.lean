module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem characteristic_map_equiv_eq {G : Type u} [Group G]
    (subgroup : Subgroup G) [subgroup.Characteristic] (equivalence : MulAut G) :
    subgroup.map (equivalence : G →* G) = subgroup :=
  Subgroup.characteristic_iff_map_eq.mp (inferInstance : subgroup.Characteristic) equivalence

@[expose] noncomputable def characteristicQuotientAction {G : Type u} [Group G]
    (subgroup : Subgroup G) [subgroup.Characteristic] : MulAut G →* MulAut (G ⧸ subgroup) where
  toFun equivalence := QuotientGroup.congr subgroup subgroup equivalence
    (characteristic_map_equiv_eq subgroup equivalence)
  map_one' := by
    ext member
    obtain ⟨member, rfl⟩ := QuotientGroup.mk'_surjective subgroup member
    rw [QuotientGroup.congr_mk', MulAut.one_apply]
    rfl
  map_mul' first second := by
    ext member
    obtain ⟨member, rfl⟩ := QuotientGroup.mk'_surjective subgroup member
    change (QuotientGroup.congr subgroup subgroup (first * second)
      (characteristic_map_equiv_eq subgroup (first * second))) (QuotientGroup.mk' subgroup member) =
      (QuotientGroup.congr subgroup subgroup first (characteristic_map_equiv_eq subgroup first))
        ((QuotientGroup.congr subgroup subgroup second (characteristic_map_equiv_eq subgroup second))
          (QuotientGroup.mk' subgroup member))
    rw [QuotientGroup.congr_mk', QuotientGroup.congr_mk', QuotientGroup.congr_mk', MulAut.mul_apply]

theorem characteristicQuotientAction_apply {G : Type u} [Group G]
    (subgroup : Subgroup G) [subgroup.Characteristic] (equivalence : MulAut G) (member : G) :
    characteristicQuotientAction subgroup equivalence (QuotientGroup.mk' subgroup member) =
      QuotientGroup.mk' subgroup (equivalence member) := by
  exact QuotientGroup.congr_mk' subgroup subgroup equivalence
    (characteristic_map_equiv_eq subgroup equivalence) member

theorem characteristicQuotientAction_mem_kernel_iff {G : Type u} [Group G]
    (subgroup : Subgroup G) [subgroup.Characteristic] (equivalence : MulAut G) :
    equivalence ∈ (characteristicQuotientAction subgroup).ker ↔
      ∀ member : G, QuotientGroup.mk' subgroup (equivalence member) = QuotientGroup.mk' subgroup member := by
  constructor
  · intro hmember member
    rw [← characteristicQuotientAction_apply]
    have heq := MonoidHom.mem_ker.mp hmember
    rw [heq]
    rfl
  · intro hequal
    apply MonoidHom.mem_ker.mpr
    ext member
    obtain ⟨member, rfl⟩ := QuotientGroup.mk'_surjective subgroup member
    rw [characteristicQuotientAction_apply, hequal]
    rfl

theorem quadratic_characteristic_quotient_action {G : Type u} [Group G]
    (subgroup : Subgroup G) [subgroup.Characteristic] (equivalence : MulAut G)
    (hquadratic : QuadraticAutomorphism equivalence) :
    QuadraticAutomorphism (characteristicQuotientAction subgroup equivalence) := by
  intro member
  obtain ⟨member, rfl⟩ := QuotientGroup.mk'_surjective subgroup member
  rw [characteristicQuotientAction_apply, ← map_inv, ← map_mul,
    characteristicQuotientAction_apply, hquadratic]

end CFSG.RankThreeEvenClassification.Helpers
