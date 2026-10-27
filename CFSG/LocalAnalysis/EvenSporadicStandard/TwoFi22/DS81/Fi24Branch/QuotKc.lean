module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.LayerBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotCores
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemma210

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C] {c : CInv C} {R : Subgroup C}

@[expose] def CatSections (C : Type) [Group C] : Prop :=
  ∀ (A : Subgroup C) (S : Type) [Group S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ φ : ↥A →* S, Function.Surjective φ → CFSG.Blueprint.Catalog S

structure UniqueComp (c : CInv C) (R : Subgroup C) (L1 : Subgroup c.Qt) : Prop where
  comp : CFSG.IsComponent L1
  layer : CFSG.layer c.Qt = L1
  R_le : c.bar R ≤ L1

variable {L1 : Subgroup c.Qt}

theorem L1_normal (h : UniqueComp c R L1) : L1.Normal := by
  rw [← h.layer]
  exact layer_normal_Fi24 c.Qt

theorem component_eq (hC : CCore c) (h : UniqueComp c R L1) {K' : Subgroup c.Qt}
    (hK' : CFSG.IsComponent K') : K' = L1 := by
  rcases CFSG.LocalCores.distinct_components_commute hK' h.comp with heq | hcomm
  · exact heq
  · exfalso
    have hK'le : K' ≤ centralizer (L1 : Set c.Qt) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hbot : centralizer (L1 : Set c.Qt) = ⊥ := by
      rw [← h.layer]
      exact centralizer_layer_eq_bot (pPrimeCore_Qt_eq_bot hC) (pCore_Qt_eq_bot hC)
    rw [hbot] at hK'le
    haveI : Nontrivial ↥K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
    exact (Subgroup.nontrivial_iff_ne_bot K').mp inferInstance (le_bot_iff.mp hK'le)

theorem L1_center_eq_bot (hC : CCore c) (h : UniqueComp c R L1) : center ↥L1 = ⊥ := by
  exact center_component_eq_bot (pPrimeCore_Qt_eq_bot hC) (pCore_Qt_eq_bot hC) h.comp

theorem L1_perfect (h : UniqueComp c R L1) : ⁅L1, L1⁆ = L1 := by
  rw [← h.layer]
  exact CFSG.LocalCores.layer_perfect

theorem L1_simple (hC : CCore c) (h : UniqueComp c R L1) : IsSimpleGroup ↥L1 := by
  have hcenter : center ↥L1 = ⊥ := L1_center_eq_bot hC h
  haveI : IsSimpleGroup (↥L1 ⧸ center ↥L1) := h.comp.1.2.1
  let e : (↥L1 ⧸ center ↥L1) ≃* ↥L1 :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem L1_nonabelian (hC : CCore c) (h : UniqueComp c R L1) : ∃ a b : ↥L1, a * b ≠ b * a := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  haveI : IsMulCommutative ↥L1 := IsMulCommutative.of_comm fun a b => hcon a b
  haveI : Nontrivial ↥L1 := CFSG.LocalCores.isQuasisimple_nontrivial h.comp.1
  haveI : Group.IsPerfect ↥L1 := Subgroup.isPerfect_iff.mpr (L1_perfect h)
  exact Group.IsPerfect.not_isMulCommutative (↥L1) inferInstance

theorem catalog_L1 (hC : CCore c) (hcat : CatSections C) (h : UniqueComp c R L1) :
    CFSG.Blueprint.Catalog ↥L1 := by
  haveI : IsSimpleGroup ↥L1 := L1_simple hC h
  exact hcat (L1.comap c.qmap) ↥L1 (L1_nonabelian hC h)
    (c.qmap.subgroupComap L1) (MonoidHom.subgroupComap_surjective c.qmap L1 c.qmap_surjective)

theorem perfect_le_L1 (hC : CCore c) (hcat : CatSections C) (hSch : CatalogOuterSolvable)
    (h : UniqueComp c R L1) {P : Subgroup c.Qt} (hP : ⁅P, P⁆ = P) : P ≤ L1 := by
  have hcen : ∀ x ∈ CFSG.pCore 2 c.Qt, ∀ y : c.Qt, x * y = y * x := by
    intro x hx y
    rw [pCore_Qt_eq_bot hC] at hx
    rw [Subgroup.mem_bot.mp hx, one_mul, mul_one]
  have hOut : ∀ i : CFSG.ComponentClassification.SemisimpleComponentStructure.ComponentIndex c.Qt,
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥i.val) := by
    intro i
    have hi : CFSG.IsComponent i.val := (CFSG.isComponent_iff_open i.val).mpr i.property
    have hLi : i.val = L1 := component_eq hC h hi
    rw [hLi]
    haveI : IsSimpleGroup ↥L1 := L1_simple hC h
    exact hSch ↥L1 (L1_nonabelian hC h) (catalog_L1 hC hcat h)
  have hn : ∀ (i : CFSG.ComponentClassification.SemisimpleComponentStructure.ComponentIndex c.Qt),
      ∀ k ∈ P, ∀ m ∈ i.val, k * m * k⁻¹ ∈ i.val := by
    intro i k _ m hm
    have hi : CFSG.IsComponent i.val := (CFSG.isComponent_iff_open i.val).mpr i.property
    have hLi : i.val = L1 := component_eq hC h hi
    have hnormal : L1.Normal := L1_normal h
    rw [hLi] at hm ⊢
    exact hnormal.conj_mem m hm k
  have hle := CFSG.EvenSporadicStandard.TwoB.Layer54.le_layer_of_perfect_normalizes
    (H := c.Qt) hP (pPrimeCore_Qt_eq_bot hC) hcen hOut hn
  rw [← CFSG.layer_eq_componentClassification c.Qt, h.layer] at hle
  exact hle

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
