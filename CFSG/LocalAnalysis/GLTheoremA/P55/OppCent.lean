module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem oPPrimeP_le_centModSubgroup {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : oPPrimeP p X ≤ centModSubgroup p L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ⁅CFSG.LocalAnalysis.GLTheoremB.barX p X L,
      CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)⁆ = ⊥ := by
    rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
        (CFSG.LocalAnalysis.GLTheoremB.barX p X L) (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X))
        hL.2.2.1 with hle | hc
    · exfalso
      have hpg : IsPGroup p ↥(CFSG.LocalAnalysis.GLTheoremB.barX p X L) :=
        IsPGroup.to_le CFSG.pCore_isPGroup hle
      have hnil : Group.IsNilpotent ↥(CFSG.LocalAnalysis.GLTheoremB.barX p X L) :=
        IsPGroup.isNilpotent hpg
      haveI : Group.IsPerfect ↥(CFSG.LocalAnalysis.GLTheoremB.barX p X L) :=
        Group.isPerfect_def.2 hL.2.2.1.2.2.1
      haveI : Nontrivial ↥(CFSG.LocalAnalysis.GLTheoremB.barX p X L) :=
        isQuasisimple_nontrivial hL.2.2.1.2.2
      exact Group.IsPerfect.not_isNilpotent _ hnil
    · exact hc
  intro q hq
  unfold oPPrimeP at hq
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
  show (x : G) ∈ centModSubgroup p L
  have hA : ∀ l ∈ L, ⁅l, (x : G)⁆ ∈ GLAPPrimeCoreOf p X := by
    intro l hl
    have hlX : l ∈ X := hL.1 hl
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨l, hlX⟩ : ↥X) ∈
        CFSG.LocalAnalysis.GLTheoremB.barX p X L :=
      Subgroup.mem_map.2 ⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) x ∈
        CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := hx
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    rw [hcomm, Subgroup.mem_bot] at h3
    have h4 : ((⁅(⟨l, hlX⟩ : ↥X), x⁆ : ↥X) : ↥X ⧸ GLAPPrimeCore p ↥X) = 1 := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement]
      exact h3
    have h5 : ⁅(⟨l, hlX⟩ : ↥X), x⁆ ∈ GLAPPrimeCore p ↥X :=
      (QuotientGroup.eq_one_iff _).1 h4
    refine Subgroup.mem_map.2 ⟨⁅(⟨l, hlX⟩ : ↥X), x⁆, h5, ?_⟩
    simp only [map_commutatorElement]
    rfl
  have hgX : (x : G)⁻¹ ∈ X := Subgroup.inv_mem _ x.2
  have hXeq : GLBConj (x : G)⁻¹ X = X :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hgX)
  have hK : GLAPComponent p X (GLBConj (x : G)⁻¹ L) := by
    have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL (x : G)⁻¹
    rwa [hXeq] at h
  have hLK : L ≤ GLBConj (x : G)⁻¹ L ⊔ GLAPPrimeCoreOf p X := by
    intro l hl
    have hk : (x : G) * l * (x : G)⁻¹ ∈ GLBConj (x : G)⁻¹ L := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hl
    have key : l = ⁅l, (x : G)⁆ * ((x : G) * l * (x : G)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hA l hl)) (Subgroup.mem_sup_left hk)
  have hLconj : L ≤ GLBConj (x : G)⁻¹ L :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup hp hL
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp X)
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPPrimeCoreOf_le_normalizer hK) hLK
  have hcard : Nat.card (GLBConj (x : G)⁻¹ L) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj (x : G)⁻¹⁻¹).injective
  have heq : L = GLBConj (x : G)⁻¹ L := Subgroup.eq_of_le_of_card_ge hLconj hcard.le
  have hxN : (x : G) ∈ Subgroup.normalizer (L : Set G) := by
    have hg : (x : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 heq.symm
    simpa using Subgroup.inv_mem _ hg
  rw [mem_centModSubgroup]
  refine ⟨hxN, fun l hl => ?_⟩
  have hlx : ⁅l, (x : G)⁆ ∈ L := by
    have e : ⁅l, (x : G)⁆ = l * ((x : G) * l⁻¹ * (x : G)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ hl
      ((Subgroup.mem_normalizer_iff.1 hxN l⁻¹).1 (Subgroup.inv_mem _ hl))
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
  exact Subgroup.mem_inf.2 ⟨hlx, hA l hl⟩

end CFSG.LocalAnalysis.GLTheoremA.P55
