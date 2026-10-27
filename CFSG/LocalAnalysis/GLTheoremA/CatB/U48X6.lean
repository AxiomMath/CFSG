module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsU

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def U48RootResidual (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L A E T : Subgroup G), GLAPComponent 3 X L → catalogIs ↥L S9.isU4eight →
    A ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 3 A → E ≤ A → E ≤ L → Nat.card E = 3 ^ 2 →
    T ≤ L → IsPGroup 2 T → ¬ T ≤ GLAPPrimeCoreOf 3 L → A ≤ Subgroup.normalizer (T : Set G) →
    ∃ R : Subgroup G, Nat.card R = 8 ∧ R ≤ L ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ r ∈ R, r ≠ 1 → r ^ 2 = 1 ∧ IsCentralIn 2 r L

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem u48CentInvAt_of_root (G : Type) [Group G] [Finite G] (h : U48RootResidual G) :
    U48CentInvAt G := by
  intro X L A E T hL hcat hAN hA hEA hEL hEc hTL hT2 hTO hAT
  obtain ⟨R, hR8, hRL, hAR, hRinv⟩ := h X L A E T hL hcat hAN hA hEA hEL hEc hTL hT2 hTO hAT
  have hnorm : ∀ a : ↥A, ∀ r : G, r ∈ R ↔ (a : G) * r * (a : G)⁻¹ ∈ R := fun a r =>
    Subgroup.mem_normalizer_iff.1 (hAR a.2) r
  let S : Type := {r : G // r ∈ R ∧ r ≠ 1}
  have hSfin : Finite S := inferInstance
  have hS7 : Nat.card S = 7 := by
    have e1 : Nat.card ↥R = Nat.card {x : ↥R // x ≠ 1} + 1 := by
      classical
      rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥R))]
    have e2 : Nat.card S = Nat.card {x : ↥R // x ≠ 1} := by
      refine Nat.card_congr
        { toFun := fun r => ⟨⟨r.1, r.2.1⟩, fun h => r.2.2 (congrArg Subtype.val h)⟩
          invFun := fun x => ⟨x.1.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
          left_inv := fun r => rfl
          right_inv := fun x => rfl }
    have e3 : Nat.card ↥R = 8 := hR8
    omega
  let ρ : ↥A →* Equiv.Perm S :=
    { toFun := fun a =>
        Equiv.subtypeEquiv (MulAut.conj (a : G)).toEquiv (fun r => by
          change r ∈ R ∧ r ≠ 1 ↔ (a : G) * r * (a : G)⁻¹ ∈ R ∧ (a : G) * r * (a : G)⁻¹ ≠ 1
          rw [← hnorm a r]
          simp)
      map_one' := by
        ext r
        simp
      map_mul' := by
        intro a b
        ext r
        simp [mul_assoc] }
  letI : MulAction ↥A S := MulAction.compHom S ρ
  have hA3 : IsPGroup 3 ↥A := isPGroup_of_isElemAbelian hA
  have hmod := hA3.card_modEq_card_fixedPoints S
  rw [hS7] at hmod
  have hne : (MulAction.fixedPoints ↥A S).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmod
    norm_num [Nat.ModEq] at hmod
  obtain ⟨r0, hr0⟩ := hne
  have hfix : ∀ a : ↥A, a • r0 = r0 := fun a => hr0 a
  refine ⟨r0.1, (hRinv r0.1 r0.2.1 r0.2.2).1, r0.2.2, (hRinv r0.1 r0.2.1 r0.2.2).2, ?_⟩
  intro a ha
  have h1 : ((⟨a, ha⟩ : ↥A) • r0 : S).1 = r0.1 := congrArg Subtype.val (hfix ⟨a, ha⟩)
  have h2 : (a : G) * r0.1 * (a : G)⁻¹ = r0.1 := h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.1 h2

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X6
