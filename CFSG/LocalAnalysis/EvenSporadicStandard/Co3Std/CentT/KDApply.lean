module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ConjAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Sp62
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDCat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerCore

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

private theorem zpowers_sq_eq_one_or {x : X} (hx : x * x = 1) {c : X}
    (hc : c ∈ zpowers x) : c = 1 ∨ c = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 2 * m := ⟨k / 2, by omega⟩
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem exists_mul_of_mem_sup_of_le_centralizer {T C : Subgroup X}
    (hC : C ≤ centralizer (T : Set X)) {x : X} (hx : x ∈ T ⊔ C) :
    ∃ t ∈ T, ∃ c ∈ C, x = t * c := by
  have hTC : T ≤ normalizer (C : Set X) := fun t ht =>
    centralizer_le_normalizer _ ((Subgroup.le_centralizer_iff.mp hC) ht)
  have hx' : x ∈ ((T ⊔ C : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T C hTC] at hx'
  obtain ⟨t, ht, c, hc, rfl⟩ := hx'
  exact ⟨t, ht, c, hc, rfl⟩

private theorem E_le_centralizer_zpowers (h : CentConfig X a b E Fus) :
    E ≤ centralizer (zpowers a : Set X) := by
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_iff.mpr fun e he => h.a_comm he

private theorem commutator_mem_sup (h : CentConfig X a b E Fus) {c₁ c₂ : X}
    (hc₁ : c₁ ∈ zpowers a ⊔ E) (hc₂ : c₂ ∈ zpowers a ⊔ E) : ⁅c₁, c₂⁆ ∈ E := by
  obtain ⟨h₁, hh₁, e₁, he₁, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (E_le_centralizer_zpowers h) hc₁
  obtain ⟨h₂, hh₂, e₂, he₂, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (E_le_centralizer_zpowers h) hc₂
  have hconj : ∀ x ∈ E, a * x * a⁻¹ = x := by
    intro x hx
    rw [← h.a_comm hx]
    group
  have he12 : ⁅e₁, e₂⁆ ∈ E :=
    Subgroup.commutator_le_of_le (le_refl E) (le_refl E)
      (Subgroup.commutator_mem_commutator he₁ he₂)
  have hea : ⁅e₁, a⁆ = 1 := Commute.commutator_eq (h.a_comm he₁)
  have hae : ⁅a, e₂⁆ = 1 := Commute.commutator_eq (h.a_comm he₂).symm
  rcases zpowers_sq_eq_one_or h.a_sq hh₁ with hh1 | hh1 <;>
    rcases zpowers_sq_eq_one_or h.a_sq hh₂ with hh2 | hh2
  · rw [hh1, hh2, one_mul, one_mul]
    exact he12
  · rw [hh1, hh2, one_mul, commutatorElement_mul_right_eq_mul_conj, hea, one_mul]
    rw [hconj _ he12]
    exact he12
  · rw [hh1, hh2, one_mul, commutatorElement_mul_left_eq_conj_mul, hae, mul_one]
    rw [hconj _ he12]
    exact he12
  · rw [hh1, hh2, commutatorElement_mul_left_eq_conj_mul]
    have hx : ⁅e₁, a * e₂⁆ ∈ E := by
      rw [commutatorElement_mul_right_eq_mul_conj, hea, one_mul]
      rw [hconj _ he12]
      exact he12
    have hax : ⁅a, a * e₂⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact Commute.mul_right (Commute.refl a) (h.a_comm he₂).symm
    rw [hax, mul_one, hconj _ hx]
    exact hx

theorem isPGroup_center_component (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : IsPGroup 2 (center ↥L) := by
  have htop : CFSG.Open.standardComponentOddCore ↥(⊤ : Subgroup X) = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant
      (Subgroup.topEquiv (G := X)).symm
    have h2 : CFSG.Open.componentClassificationOddCore X = ⊥ := h.oddCore
    rw [h2, Subgroup.map_bot] at h1
    exact h1.symm
  have hX : CFSG.pPrimeCore 2 ↥(⊤ : Subgroup X) = ⊥ :=
    CFSG.EvenSporadicStandard.Induction.Balance.pPrimeCore_eq_bot_of_standardComponentOddCore_eq_bot
      htop
  have hsub : (L.subgroupOf (⊤ : Subgroup X)).IsSubnormal := hL.2.1.subgroupOf
  have hLcore : CFSG.pPrimeCore 2 ↥L = ⊥ :=
    CFSG.EvenSporadicStandard.Induction.Balance.pPrimeCore_eq_bot_of_isSubnormal
      le_top hsub hX
  exact CFSG.EvenSporadicStandard.Induction.Balance.isPGroup_center_of_pPrimeCore_eq_bot hLcore

theorem catalog_center_quotient (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : Catalog (↥L ⧸ center ↥L) := by
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := hL.2.2.2
  exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective h.kgroupCat L
    (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective _)

theorem kd_facts (hKD : KDCo3Cat) (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (haL : a ∈ normalizer (L : Set X)) (hEL : E ≤ L) (hne : E ≠ L) :
    (LieModel (↥L ⧸ center ↥L) .POmegaPlus 4 2 1 ∨ LieModel (↥L ⧸ center ↥L) .PSU 6 2 1 ∨
        NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Fi22) ∧
      ∀ g : ↥L, conjAut L a haL ≠ MulAut.conj g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hζ : orderOf (conjAut L a haL) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact conjAut_mul_self L haL h.a_sq
    · intro hζ1
      have hLC : L ≤ centralizer ({a} : Set X) := by
        intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hfix : conjAut L a haL ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [hζ1]; rfl
        have hco := congrArg (fun x : ↥L => (x : X)) hfix
        rw [coe_conjAut] at hco
        calc l * a = (a * l * a⁻¹) * a := by rw [hco]
          _ = a * l := by group
      have hsub : L ≤ zpowers a ⊔ E := hLC.trans (le_of_eq h.cent_a)
      have hCL : ⁅L, L⁆ ≤ E :=
        Subgroup.commutator_le.mpr fun l₁ hl₁ l₂ hl₂ =>
          commutator_mem_sup h (hsub hl₁) (hsub hl₂)
      haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.2.2.1
      have hLleE : L ≤ E := (Subgroup.commutator_eq_self (H := L)).ge.trans hCL
      exact hne (le_antisymm hEL hLleE)
  have hD1 : E.subgroupOf L ≤ fixedSubgroup (conjAut L a haL) := by
    intro d hd
    have hdE : (d : X) ∈ E := Subgroup.mem_subgroupOf.mp hd
    change conjAut L a haL d = d
    apply Subtype.ext
    rw [coe_conjAut, ← h.a_comm hdE]
    group
  have hD2 : (E.subgroupOf L).relIndex (fixedSubgroup (conjAut L a haL)) ≤ 2 := by
    set C : Subgroup X := centralizer ({a} : Set X) with hC
    have hF : fixedSubgroup (conjAut L a haL) = C.subgroupOf L := by
      ext l
      change conjAut L a haL l = l ↔ (l : X) ∈ C
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hl
        have hco := congrArg (fun x : ↥L => (x : X)) hl
        rw [coe_conjAut] at hco
        calc (l : X) * a = (a * (l : X) * a⁻¹) * a := by rw [hco]
          _ = a * (l : X) := by group
      · intro hl
        apply Subtype.ext
        rw [coe_conjAut, ← hl]
        group
    have hrel : (E.subgroupOf L).relIndex (fixedSubgroup (conjAut L a haL)) =
        E.relIndex (C ⊓ L) := by
      rw [hF]
      have h := Subgroup.relIndex_subgroupOf (H := E) (K := C ⊓ L) (L := L) inf_le_right
      rw [Subgroup.inf_subgroupOf_right] at h
      exact h
    have hC2 : E.relIndex C ≤ 2 := by
      have hdvd : E.relIndex C ∣ 2 := by
        rw [Subgroup.relIndex_dvd_two_iff']
        refine ⟨a, ?_, fun b hb => ?_⟩
        · rw [hC, Subgroup.mem_centralizer_singleton_iff]
        · rw [hC] at hb
          rw [h.cent_a] at hb
          obtain ⟨h₁, hh₁, e₁, he₁, hbeq⟩ :=
            exists_mul_of_mem_sup_of_le_centralizer (E_le_centralizer_zpowers h) hb
          rcases zpowers_sq_eq_one_or h.a_sq hh₁ with hh1 | hh1
          · right
            rw [hbeq, hh1, one_mul]
            exact he₁
          · left
            rw [hbeq, hh1]
            rw [← mul_assoc, h.a_sq, one_mul]
            exact he₁
      exact Nat.le_of_dvd (by norm_num) hdvd
    have hpos : E.relIndex C ≠ 0 := (E.subgroupOf C).index_ne_zero_of_finite
    rw [hrel]
    exact (Subgroup.relIndex_le_of_le_right inf_le_left hpos).trans hC2
  have hD3 : IsTwoSp62 ↥(E.subgroupOf L) :=
    IsTwoSp62.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEL).symm h.E_two
  have hD4 : ∀ d : ↥(E.subgroupOf L), d ∈ center ↥(E.subgroupOf L) →
      (d : ↥L) ∈ center ↥L := by
    intro d hd
    have hdE : (d : X) ∈ E := Subgroup.mem_subgroupOf.mp d.2
    have hcomm : ∀ x ∈ E, x * (d : X) = (d : X) * x := by
      intro x hx
      have hmem := Subgroup.mem_center_iff.mp hd (⟨⟨x, hEL hx⟩, hx⟩ : ↥(E.subgroupOf L))
      have h' := congrArg (fun y : ↥(E.subgroupOf L) => ((y : ↥L) : X)) hmem
      simpa using h'
    have hdX : (d : X) ∈ center X := by
      rcases h.center_E hdE hcomm with h1 | hb
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hb]; exact h.b_central
    refine Subgroup.mem_center_iff.mpr fun l => ?_
    exact Subtype.ext (Subgroup.mem_center_iff.mp hdX (l : X))
  exact hKD ↥L hL.2.2 (catalog_center_quotient h hL) (isPGroup_center_component h hL)
    (conjAut L a haL) hζ (E.subgroupOf L) hD1 hD2 hD3 hD4

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
