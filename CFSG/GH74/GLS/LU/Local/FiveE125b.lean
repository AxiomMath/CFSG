module

public import CFSG.GH74.GLS.LU.Local.FiveE125
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

open scoped MatrixGroups Matrix

namespace CFSG.GH74.GLS.LU.Local.Five

theorem card_sl3_five : Nat.card SL(3, ZMod 5) = 372000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_SL_field 3, ZMod.card, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num

theorem normalizer_quot_sl3_of_card {G : Type} [Group G] [Finite G] (E : Subgroup G) (x : Fin 3 → G)
    (hxE : Subgroup.closure (Set.range x) = E) (hcomm : ∀ i j, x i * x j = x j * x i)
    (hord : ∀ i, x i ^ 5 = 1) (hcard : Nat.card E = 125)
    (hC : ∀ m ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, m * e = e * m) → m ∈ E)
    (R : Fin 3 → Subgroup G) (hRN : ∀ i, R i ≤ Subgroup.normalizer (E : Set G))
    (hRx : ∀ i, ∀ r ∈ R i, r * x i * r⁻¹ = x i)
    (hRc : ∀ i, ∀ r ∈ R i, ∀ j, ∃ c : ℕ, r * x j * r⁻¹ = x j * (x i) ^ c)
    (hRcard : ∀ i, Nat.card ↥(R i ⊔ E) = 5 ^ 5)
    (hbound : Nat.card ↥(Subgroup.normalizer (E : Set G)) ≤ 125 * 372000) :
    ∃ phi : ↥(Subgroup.normalizer (E : Set G)) →* SL(3, ZMod 5),
      Function.Surjective phi ∧ ∀ m, phi m = 1 ↔ (m : G) ∈ E := by
  have hF : E125.Frame E x := ⟨hxE, hcomm, hord, hcard⟩
  have htr : ∀ (i j : Fin 3) (hij : i ≠ j) (a : ZMod 5),
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) ∈
        (E125.rho hF).range := by
    intro i j hij a
    obtain ⟨k, hik, hjk, hcov⟩ := E125.exists_third i j hij
    exact E125.transvection_mem_range hF hC hij hik hjk hcov (hRN i) (hRx i) (hRc i) (hRcard i) a
  have hSL : ∀ s : SL(3, ZMod 5), Matrix.SpecialLinearGroup.toGL s ∈ (E125.rho hF).range :=
    fun s => sl3_five_le_of_transvections htr s
  have hker : (E125.rho hF).ker = E.subgroupOf (Subgroup.normalizer (E : Set G)) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact E125.rho_eq_one_iff hF hC m
  have hkercard : Nat.card ↥(E125.rho hF).ker = 125 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe E.le_normalizer).toEquiv, hcard]
  have hrange : Nat.card ↥(E125.rho hF).range * 125 =
      Nat.card ↥(Subgroup.normalizer (E : Set G)) := by
    have h1 := Subgroup.index_ker (E125.rho hF)
    have h2 := Subgroup.index_mul_card (E125.rho hF).ker
    rw [h1, hkercard] at h2
    exact h2
  have hTcard : Nat.card ↥(Matrix.SpecialLinearGroup.toGL :
      SL(3, ZMod 5) →* GL (Fin 3) (ZMod 5)).range = 372000 := by
    rw [← card_sl3_five]
    exact (Nat.card_congr
      (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv).symm
  have hTle : (Matrix.SpecialLinearGroup.toGL : SL(3, ZMod 5) →* GL (Fin 3) (ZMod 5)).range ≤
      (E125.rho hF).range := by
    rintro _ ⟨s, rfl⟩
    exact hSL s
  have hTeq := Subgroup.eq_of_le_of_card_ge hTle (by rw [hTcard]; omega)
  have hdet : ∀ m, Matrix.GeneralLinearGroup.det (E125.rho hF m) = 1 := by
    intro m
    have hm : E125.rho hF m ∈ (Matrix.SpecialLinearGroup.toGL :
        SL(3, ZMod 5) →* GL (Fin 3) (ZMod 5)).range := by
      rw [hTeq]; exact ⟨m, rfl⟩
    obtain ⟨s, hs⟩ := hm
    rw [← hs]
    exact Units.ext (by simp)
  obtain ⟨phi, hphi⟩ := exists_lift_to_sl3 (E125.rho hF) hdet
  refine ⟨phi, fun s => ?_, fun m => ?_⟩
  · obtain ⟨m, hm⟩ := hSL s
    exact ⟨m, Matrix.SpecialLinearGroup.toGL_injective (by rw [hphi, hm])⟩
  · rw [← E125.rho_eq_one_iff hF hC m, ← hphi m, ← map_one Matrix.SpecialLinearGroup.toGL]
    exact Matrix.SpecialLinearGroup.toGL_injective.eq_iff.symm

end CFSG.GH74.GLS.LU.Local.Five
