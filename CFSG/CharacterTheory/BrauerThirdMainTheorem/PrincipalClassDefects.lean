module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockDefects
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.DefectMaximality
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Projection

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem centralChar_trivial_classCard {G : Type*} [Group G] [Finite G]
    (conjugacyClass : ConjClasses G) :
    BlocksCentralChar (fun _ : G => 1) (classCoefficients conjugacyClass) =
      (Nat.card {element : G // ConjClasses.mk element = conjugacyClass} : ℂ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [centralChar_trivial, finsum_eq_sum_of_fintype]
  have hcount := Finset.sum_boole (R := ℂ)
    (fun element : G => ConjClasses.mk element = conjugacyClass) Finset.univ
  apply Eq.trans (b := ∑ element : G,
    if ConjClasses.mk element = conjugacyClass then (1 : ℂ) else 0)
  · apply Finset.sum_congr rfl
    intro element _
    unfold classCoefficients
    by_cases hclass : ConjClasses.mk element = conjugacyClass <;> simp only [hclass, ↓reduceIte]
  · rw [hcount]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem principal_class_nonzero_defect_sylow {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (conjugacyClass : ConjClasses G)
    (hnonzero : BlocksCentralChar (fun _ : G => 1) (classCoefficients conjugacyClass) ∉
      BlocksLocalMaxIdeal m) {defect : Subgroup G}
    (hdefect : classDefect prime conjugacyClass defect) :
    ∃ sylow : Sylow prime G, (sylow : Subgroup G) = defect := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let sylow : Sylow prime G := Classical.choice inferInstance
  let points := {element : G // ConjClasses.mk element = conjugacyClass}
  let : MulAction (sylow : Subgroup G) points := {
    smul member point := ⟨member.val * point.val * member.val⁻¹,
      (ConjClasses.mk_eq_mk_iff_isConj.mpr
        (isConj_iff.mpr ⟨member.val, rfl⟩).symm).trans point.property⟩
    one_smul point := Subtype.ext (by
      change (1 : G) * point.val * (1 : G)⁻¹ = point.val
      group)
    mul_smul first second point := Subtype.ext (by
      change (first.val * second.val) * point.val * (first.val * second.val)⁻¹ =
        first.val * (second.val * point.val * second.val⁻¹) * first.val⁻¹
      group)
  }
  have hcard : ¬ prime ∣ Nat.card points := by
    intro hdivides
    rw [centralChar_trivial_classCard] at hnonzero
    exact hnonzero (localMaxIdeal_natCast_of_dvd m hm prime hprimeMem hdivides)
  obtain ⟨point, hpoint⟩ := pGroup_exists_fixed_of_not_dvd_card prime hprime sylow.isPGroup' points hcard
  have hcentralizes : (sylow : Subgroup G) ≤ Subgroup.centralizer {point.val} := by
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    have hfixed := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hpoint ⟨member, hmember⟩)
    change member * point.val * member⁻¹ = point.val at hfixed
    exact ((mul_inv_eq_iff_eq_mul).mp hfixed).symm
  have hsubconjugate := pGroup_centralizes_subconjugate_classDefect prime hprime
    point.property sylow.isPGroup' hcentralizes hdefect
  obtain ⟨extension, hextension⟩ := (classDefect_isPGroup prime hdefect).exists_le_sylow
  have hcardSylow := Nat.card_congr (sylow.equiv extension).toEquiv
  have hequal : defect = (extension : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hextension
      (hcardSylow ▸ subgroupSubconjugate_card_le hsubconjugate)
  exact ⟨extension, hequal.symm⟩

theorem sylow_classDefect_in_subgroup {G : Type*} [Group G]
    (prime : ℕ) (sylow : Sylow prime G) (overgroup : Subgroup G)
    (hinclusion : (sylow : Subgroup G) ≤ overgroup) (element : overgroup)
    (hcentralizes : (sylow : Subgroup G) ≤ Subgroup.centralizer {element.val}) :
    classDefect prime (ConjClasses.mk element) ((sylow : Subgroup G).subgroupOf overgroup) := by
  have hpLocal : IsPGroup prime ((sylow : Subgroup G).subgroupOf overgroup) :=
    sylow.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hinclusion).symm
  have hcentralizesLocal : (sylow : Subgroup G).subgroupOf overgroup ≤ Subgroup.centralizer {element} := by
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    have htestEqual : test = element := Set.mem_singleton_iff.mp htest
    subst test
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentralizes hmember) element.val (Set.mem_singleton element.val)
  apply classDefect_of_maximal_centralizing prime element _ hpLocal hcentralizesLocal
  intro other hpOther hother _
  have hmapped : other.map overgroup.subtype = (sylow : Subgroup G) :=
    sylow.is_maximal' (hpOther.map overgroup.subtype) (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hinclusion]
      exact Subgroup.map_mono hother)
  apply Subgroup.map_injective overgroup.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hinclusion]
  exact hmapped

end CFSG.BrauerThirdMainTheorem.Helpers
