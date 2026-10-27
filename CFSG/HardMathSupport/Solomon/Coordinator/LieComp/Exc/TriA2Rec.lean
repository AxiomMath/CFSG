module

public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsFine
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem exists_hom_ker_eq_of_perfect_index_le_four {C : Type} [Group C] {Q : Subgroup C}
    (hQ : Group.IsPerfect Q) (hidx : Q.index ≤ 4) (hfin : Q.index ≠ 0) :
    ∃ π : C →* Equiv.Perm (C ⧸ Q), π.ker = Q := by
  classical
  haveI : Finite (C ⧸ Q) := Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_eq_card]; exact hfin)
  have hcard : Nat.card (C ⧸ Q) ≤ 4 := by rw [← Subgroup.index_eq_card]; exact hidx
  have hsolv : Group.IsSolvable (Equiv.Perm (C ⧸ Q)) := Equiv.Perm.isSolvable hcard
  let π : C →* Equiv.Perm (C ⧸ Q) := MulAction.toPermHom C (C ⧸ Q)
  have hker_le : π.ker ≤ Q := by
    intro c hc
    have h1 : π c (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
      rw [MonoidHom.mem_ker.1 hc]; rfl
    have h2 : (QuotientGroup.mk (c * 1) : C ⧸ Q) = QuotientGroup.mk 1 := h1
    rw [mul_one, QuotientGroup.eq, mul_one] at h2
    exact Q.inv_mem_iff.1 h2
  have hle_ker : Q ≤ π.ker := by
    intro x hx
    have hf : (π.comp Q.subtype).range = ⊥ := by
      by_contra hne
      haveI : Nontrivial ↥(π.comp Q.subtype).range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      haveI : Group.IsSolvable ↥(π.comp Q.subtype).range :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
      haveI : Group.IsPerfect ↥(π.comp Q.subtype).range := Group.IsPerfect.range _
      exact Group.IsPerfect.not_isSolvable (↥(π.comp Q.subtype).range) inferInstance
    have hmem : (π.comp Q.subtype) ⟨x, hx⟩ ∈ (π.comp Q.subtype).range := ⟨_, rfl⟩
    rw [hf] at hmem
    exact hmem
  exact ⟨π, le_antisymm hker_le hle_ker⟩

theorem normal_and_solvable_of_perfect_index_le_four {C : Type} [Group C] {Q : Subgroup C}
    (hQ : Group.IsPerfect Q) (hidx : Q.index ≤ 4) (hfin : Q.index ≠ 0) :
    ∃ _ : Q.Normal, Group.IsSolvable (C ⧸ Q) := by
  classical
  haveI : Finite (C ⧸ Q) := Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_eq_card]; exact hfin)
  have hcard : Nat.card (C ⧸ Q) ≤ 4 := by rw [← Subgroup.index_eq_card]; exact hidx
  have hsolv : Group.IsSolvable (Equiv.Perm (C ⧸ Q)) := Equiv.Perm.isSolvable hcard
  obtain ⟨π, hπ⟩ := exists_hom_ker_eq_of_perfect_index_le_four hQ hidx hfin
  have hN : Q.Normal := hπ ▸ π.normal_ker
  refine ⟨hN, ?_⟩
  have e : (C ⧸ Q) ≃* π.range := (QuotientGroup.quotientMulEquivOfEq hπ.symm).trans
    (QuotientGroup.quotientKerEquivRange π)
  haveI : Group.IsSolvable ↥π.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem componentFactor_sl_of_surjective {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : ringChar F = p) {Q : Type} [Group Q] [Finite Q] (ρ : SL(3, F) →* Q)
    (hρ : Function.Surjective ρ) (hk : ρ.ker ≤ Subgroup.center SL(3, F)) :
    ComponentFactor p Q := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  subst hp
  have hFD : LieFactorData (ringChar F) SL(3, F) :=
    slFactorFacts_holds F 3 (by norm_num) (fun h => absurd h (by norm_num))
  refine ⟨⟨SL(3, F), inferInstance, inferInstance, hFD, ρ, hρ, hk⟩, ⟨fun a => ?_⟩⟩
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hFD.perfect ρ hρ hk
  obtain ⟨h3, -⟩ := slAltSixFacts_holds F 3 (by norm_num) ⟨e.trans a⟩
  omega

theorem compsWith_of_sl3_hom {P : (X : Type) → [Group X] → Prop}
    {F : Type} [Field F] [Finite F]
    (hPquot : ∀ {Q : Type} [Group Q] [Finite Q] (ρ : SL(3, F) →* Q),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center SL(3, F) → P Q)
    {C : Type} [Group C] [Finite C] (ρ : SL(3, F) →* C) (hρ : ∃ g, ρ g ≠ 1)
    (hcard : Nat.card C = Nat.card SL(3, F)) : CompsWith P C := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hquasi' : CFSG.IsQuasisimple SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hquasi : CFSG.Open.IsQuasisimple SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hquasi'
  have hker : ρ.ker ≤ Subgroup.center SL(3, F) := by
    obtain ⟨g, hg⟩ := hρ
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi ρ.ker with
      h | h
    · exact h
    · exact absurd (h ▸ Subgroup.mem_top g : g ∈ ρ.ker) hg
  have hkercard : Nat.card ρ.ker ≤ 3 :=
    (Subgroup.card_le_of_le hker).trans CFSG.DesarguesianPlanes.card_center_SL3_le
  have hrange : Nat.card ρ.range * Nat.card ρ.ker = Nat.card (SL(3, F)) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.index_eq_card, Subgroup.index_mul_card]
  have hidx : ρ.range.index * Nat.card ρ.range = Nat.card C := ρ.range.index_mul_card
  have hpos : 0 < Nat.card ρ.range := Nat.card_pos
  have h1 : ρ.range.index * Nat.card ρ.range ≤ 3 * Nat.card ρ.range := by
    rw [hidx, hcard, ← hrange]
    nlinarith
  have hidx3 : ρ.range.index ≤ 3 := Nat.le_of_mul_le_mul_right h1 hpos
  have hidx0 : ρ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  haveI : Group.IsPerfect SL(3, F) := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  obtain ⟨hN, hsolv⟩ := normal_and_solvable_of_perfect_index_le_four inferInstance
    (by omega) hidx0
  have hkR : ρ.rangeRestrict.ker ≤ Subgroup.center SL(3, F) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hPJ : P ↥ρ.range := hPquot ρ.rangeRestrict ρ.rangeRestrict_surjective hkR
  exact compsWith_of_normal_quasisimple ρ.range
    (CFSG.LocalCores.isQuasisimple_of_surjective (P := SL(3, F)) hquasi' ρ.rangeRestrict
      ρ.rangeRestrict_surjective hkR) hsolv hPJ

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
