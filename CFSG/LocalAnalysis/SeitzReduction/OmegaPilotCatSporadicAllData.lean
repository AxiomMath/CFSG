module

public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.FischerOddCore.Fi24Block
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuter
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6Sporadic
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.RankThree.PartOne.SPOR.OuterB

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple exists_conj_or_not_mem_range)

theorem card_quotient_center_dvd_card_of_fixed {S : Type} [Group S] [Finite S] {σ : MulAut S}
    (D : Subgroup (fixedSubgroup σ)) : Nat.card (D ⧸ center D) ∣ Nat.card S := by
  have h1 : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
    card_map_of_injective (fixedSubgroup σ).subtype_injective
  exact (card_quotient_dvd_card _).trans (h1 ▸ card_subgroup_dvd_card _)

theorem orderOf_eq_two_of_conj {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {u : S} (hσ : orderOf (MulAut.conj u) = 2) :
    orderOf u = 2 := by
  have := hS
  rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) u]
  exact hσ

theorem exists_component_centralizer_of_conj {S : Type} [Group S] (u : S)
    {D : Subgroup (fixedSubgroup (MulAut.conj u))} (hD : IsComponent D) :
    ∃ B : Subgroup (centralizer ({u} : Set S)), IsComponent B ∧
      Nat.card (B ⧸ center B) = Nat.card (D ⧸ center D) := by
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)
  exact ⟨D.map φ.toMonoidHom, isComponent_map_mulEquiv φ hD,
    (TwistedE6Pilot.card_quotient_center_eq_of_mulEquiv
      (D.equivMapOfInjective φ.toMonoidHom φ.injective)).symm⟩

theorem exists_component_fixSub {S : Type} [Group S] (σ : MulAut S)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    ∃ B : Subgroup (Sporadic.Schreier.fixSub σ), IsComponent B ∧
      Nat.card (B ⧸ center B) = Nat.card (D ⧸ center D) := by
  have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
    ext x
    exact Iff.rfl
  let φ := MulEquiv.subgroupCongr hfix
  exact ⟨D.map φ.toMonoidHom, isComponent_map_mulEquiv φ hD,
    (TwistedE6Pilot.card_quotient_center_eq_of_mulEquiv
      (D.equivMapOfInjective φ.toMonoidHom φ.injective)).symm⟩

theorem eq_forty_one_of_two_part {N r X : ℕ} (hr : Odd r) (hX : X = 2 ^ N * r)
    (h41 : 2 ^ 41 ∣ X) (h42 : ¬ 2 ^ 42 ∣ X) : N = 41 := by
  subst hX
  have h1 := F4Pilot.le_of_two_pow_dvd_two_pow_mul_odd hr h41
  have h2 : N < 42 := by
    by_contra h
    exact h42 ((pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _))
  omega

theorem monster_two_part_card_quotient_center (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    2 ^ 41 ∣ Nat.card (D ⧸ center D) ∧ ¬ 2 ^ 42 ∣ Nat.card (D ⧸ center D) := by
  obtain ⟨u, rfl⟩ := hMinn S hS ⟨e⟩ σ
  obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
  rw [← hcard]
  exact hMcomp S hS ⟨e⟩ u (orderOf_eq_two_of_conj hS hna hσ) B hB

section Baby


theorem baby_card_quotient_center {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .B) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 76532479683774853939200 ∨
      Nat.card (D ⧸ center D) = 3311126603366400 := by
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_B σ
  obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
  obtain ⟨-, hty, -⟩ :=
    Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen
      (T := S) ⟨e⟩ u (orderOf_eq_two_of_conj hS hna hσ) B hB
  rw [← hcard]
  rcases hty with hθ | hθ
  · obtain ⟨θ⟩ := hθ
    exact .inl ((Nat.card_congr θ.toEquiv).trans LieType.Chevalley.C2E6Std.card_stdGroup)
  · obtain ⟨θ⟩ := hθ
    refine .inr ((Nat.card_congr θ.toEquiv).trans ?_)
    have h := Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := ZMod 2)
    rw [Nat.card_zmod] at h
    exact h.trans (by norm_num [Open.ordF4])

end Baby

section Fi23

open CFSG.Sporadic.FischerOddCore (fi23_mulAut_eq_conj
  CTI_Fi23_involution_local_components_simple_quotient_divisible_by_eleven)


theorem fi23_eleven_dvd_card_quotient_center {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Fi23) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) : 11 ∣ Nat.card (D ⧸ center D) := by
  obtain ⟨u, rfl⟩ := ComponentClassification.BMCase.inner_of_equiv e fi23_mulAut_eq_conj σ
  obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
  rw [← hcard]
  exact CTI_Fi23_involution_local_components_simple_quotient_divisible_by_eleven e u
    (orderOf_eq_two_of_conj hS hna hσ) B hB

end Fi23

section Fi24

open CFSG.Sporadic.FischerOddCore (fi24primeOuterComponentsInput_holds
  CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)


theorem fi24_card_quotient_center {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi24Prime)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 64561751654400 ∨
      Nat.card (D ⧸ center D) = 4089470473293004800 ∨
        Nat.card (D ⧸ center D) = 9196830720 := by
  rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
    rw [← hcard]
    exact .inl (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e u
      (orderOf_eq_two_of_conj hS hna hσ) B hB).1
  · obtain ⟨B, hB, hcard⟩ := exists_component_fixSub σ hD
    have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    rw [← hcard]
    exact .inr (fi24primeOuterComponentsInput_holds S ⟨e⟩ σ hσ2 hout B hB)

end Fi24

section J4


theorem false_of_j4_component {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .J4) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) : False := by
  obtain ⟨u, rfl⟩ := ComponentClassification.RestrictedStd.Spor.mem_inner_of_J4 e σ hσ
  obtain ⟨B, hB, -⟩ := exists_component_centralizer_of_conj u hD
  exact ComponentClassification.RestrictedStd.Spor.j4NoComponentsInput S ⟨e⟩ u
    (orderOf_eq_two_of_conj hS hna hσ) B hB

end J4

end CFSG.SeitzReduction.OmegaPilot
