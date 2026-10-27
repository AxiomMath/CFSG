module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3Pump
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_quot_pPrimeCore_dvd {Y : Type*} [Group Y] [Finite Y] (T : Subgroup Y) :
    Nat.card (↥T ⧸ pPrimeCore 2 ↥T) ∣ Nat.card (Y ⧸ pPrimeCore 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥T →* Y ⧸ pPrimeCore 2 Y := (QuotientGroup.mk' (pPrimeCore 2 Y)).comp T.subtype
  have hk : φ.ker = (pPrimeCore 2 Y).comap T.subtype := by
    ext x
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hker : φ.ker ≤ pPrimeCore 2 ↥T := by
    rw [hk]
    exact le_sSup ⟨inferInstance, Nat.Coprime.coprime_dvd_right
      (card_comap_dvd_of_injective _ _ T.subtype_injective) pPrimeCore_coprime_card⟩
  calc Nat.card (↥T ⧸ pPrimeCore 2 ↥T) = (pPrimeCore 2 ↥T).index := (index_eq_card _).symm
    _ ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
    _ = Nat.card φ.range := by
        rw [index_eq_card]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    _ ∣ Nat.card (Y ⧸ pPrimeCore 2 Y) := Subgroup.card_subgroup_dvd_card _

theorem chevOddPump_sub (hleaf : ChevOddPumpLeaf)
    {X : Type} [Group X] [Finite X] (hKX : SectionRank.IsKGroupCat X) (β : MulAut X)
    (hβ : ∀ x, β (β x) = x) {X₁ : Subgroup X} (hX₁ : IsPComponent 2 X₁)
    (hinv : X₁.map β.toMonoidHom = X₁) {T : Subgroup X} (hTF : T ≤ fixedSubgroup β)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))) (hTX : T ≤ X₁) {r q : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (h11 : 11 ≤ q)
    (hTY : HarrisLit.IsSimpleChevalleyOver r (↥T ⧸ Open.fusionZStar ↥T))
    (hTY2 : ¬ GH74.GLS.InChev2 (↥T ⧸ Open.fusionZStar ↥T))
    (hk : q * (q ^ 2 - 1) ∣ Nat.card (↥T ⧸ pPrimeCore 2 ↥T)) :
    HarrisLit.IsSimpleChevalleyOver r (↥X₁ ⧸ Open.fusionZStar ↥X₁) ∧
      ¬ GH74.GLS.InChev2 (↥X₁ ⧸ Open.fusionZStar ↥X₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect X₁ := CatalogueBHeldSmallCore.pComponent_perfect 2 X₁ hX₁
  have hX₁q : IsQuasisimple (↥X₁ ⧸ pPrimeCore 2 ↥X₁) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 X₁).mp hX₁).2.2
  have : IsSimpleGroup ((↥X₁ ⧸ pPrimeCore 2 ↥X₁) ⧸ center (↥X₁ ⧸ pPrimeCore 2 ↥X₁)) :=
    hX₁q.2.1
  have hcat : Blueprint.Catalog ((↥X₁ ⧸ pPrimeCore 2 ↥X₁) ⧸ center (↥X₁ ⧸ pPrimeCore 2 ↥X₁)) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hKX X₁
      ((QuotientGroup.mk' (center (↥X₁ ⧸ pPrimeCore 2 ↥X₁))).comp
        (QuotientGroup.mk' (pPrimeCore 2 ↥X₁)))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  let β₁ : MulAut ↥X₁ := (β.subgroupMap X₁).trans (MulEquiv.subgroupCongr hinv)
  have hβ₁ : ∀ y : ↥X₁, ((β₁ y : ↥X₁) : X) = β y := fun y => rfl
  have hβ₁β₁ : ∀ y, β₁ (β₁ y) = y := fun y => Subtype.ext (by rw [hβ₁, hβ₁]; exact hβ y)
  have hfix : fixedSubgroup β₁ = (fixedSubgroup β).subgroupOf X₁ := by
    ext y
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf,
      LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, ← hβ₁]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set T₁ := T.subgroupOf X₁ with hT₁
  have hT₁F : T₁ ≤ fixedSubgroup β₁ := by
    rw [hfix]
    intro y hy
    exact hTF hy
  have hT₁p : IsPComponent 2 (T₁.subgroupOf (fixedSubgroup β₁)) := by
    rw [hfix, OddStandard.Solomon75.isPComponent_subgroupOf_subgroupOf_iff hTF hTX]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hTF hTX) inf_le_left hT
  let eT : ↥T₁ ≃* ↥T := subgroupOfEquivOfLe hTX
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' eT
  obtain ⟨hT₁Y, hT₁Y2⟩ := chev_of_mulEquiv hTY hTY2 eZ.symm
  have hk₁ : q * (q ^ 2 - 1) ∣ Nat.card (↥T₁ ⧸ pPrimeCore 2 ↥T₁) := by
    rw [UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eT]
    exact hk
  exact chevOddPump_aut hleaf hX₁q hcat β₁ hβ₁β₁ hT₁F hT₁p hr hr2 h11 hT₁Y hT₁Y2 hk₁

end CFSG.ComponentClassification.GS82PumpInputs
