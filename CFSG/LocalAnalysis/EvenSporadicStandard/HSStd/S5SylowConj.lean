module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Aut
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

theorem exists_conj_of_one_sylow {W : Type*} [Group W] [Finite W] (Q : Subgroup W) [Q.Normal]
    (S₀ : Subgroup W) (hS₀ : IsPGroup 2 S₀) (hS₀i : ¬ 2 ∣ S₀.index) (z₀ : W) (hz₀Q : z₀ ∈ Q)
    (hz₀1 : z₀ ≠ 1) (hz₀c : ∀ x ∈ S₀ ⊓ Q, z₀ * x = x * z₀)
    (Sw : Subgroup W) (hSw : IsPGroup 2 Sw) (hSwi : ¬ 2 ∣ Sw.index) (zw : W)
    (hzw2 : orderOf zw = 2)
    (hcent : centralizer ((Sw ⊓ Q : Subgroup W) : Set W) ⊓ Q = zpowers zw) :
    ∃ g : W, (∀ y : W, y ∈ Sw ↔ g⁻¹ * y * g ∈ S₀) ∧ g * z₀ * g⁻¹ = zw := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Sylow 2 W := hS₀.toSylow hS₀i
  let P₁ : Sylow 2 W := hSw.toSylow hSwi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W P₀ P₁
  have hmem : ∀ y : W, y ∈ Sw ↔ g⁻¹ * y * g ∈ S₀ := by
    intro y
    have h1 : y ∈ (P₁ : Subgroup W) ↔ y ∈ Sw := (hSw.mem_toSylow hSwi).symm.symm
    rw [← h1, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h2 : ∀ x : W, x ∈ (P₀ : Subgroup W) ↔ x ∈ S₀ := fun x => hS₀.mem_toSylow hS₀i
    rw [h2]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc]
  have hQc : ∀ y : W, g⁻¹ * y * g ∈ Q ↔ y ∈ Q := by
    intro y
    constructor
    · intro h
      have := (inferInstance : Q.Normal).conj_mem _ h g
      simpa [mul_assoc] using this
    · intro h
      simpa using (inferInstance : Q.Normal).conj_mem _ h g⁻¹
  refine ⟨g, hmem, ?_⟩
  have hz'Q : g * z₀ * g⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem _ hz₀Q g
  have hz'c : g * z₀ * g⁻¹ ∈ centralizer ((Sw ⊓ Q : Subgroup W) : Set W) := by
    refine mem_centralizer_iff.2 fun y hy => ?_
    have hyS : y ∈ Sw := hy.1
    have hyQ : y ∈ Q := hy.2
    have h3 := hz₀c (g⁻¹ * y * g) ⟨(hmem y).1 hyS, (hQc y).2 hyQ⟩
    calc y * (g * z₀ * g⁻¹) = g * ((g⁻¹ * y * g) * z₀) * g⁻¹ := by group
      _ = g * (z₀ * (g⁻¹ * y * g)) * g⁻¹ := by rw [← h3]
      _ = g * z₀ * g⁻¹ * y := by group
  have hmemz : g * z₀ * g⁻¹ ∈ centralizer ((Sw ⊓ Q : Subgroup W) : Set W) ⊓ Q := ⟨hz'c, hz'Q⟩
  rw [hcent] at hmemz
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmemz
  have hzz : zw * zw = 1 := by
    rw [← pow_two, ← hzw2]
    exact pow_orderOf_eq_one zw
  rcases zpow_eq_one_or_self hzz k with h | h
  · exfalso
    apply hz₀1
    have h1 : g * z₀ * g⁻¹ = 1 := by rw [← hk, h]
    calc z₀ = g⁻¹ * (g * z₀ * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [← hk, h]

theorem hcount_of_one_sylow {W : Type*} [Group W] [Finite W] (Q : Subgroup W) [Q.Normal]
    (S₀ : Subgroup W) (hS₀ : IsPGroup 2 S₀) (hS₀i : ¬ 2 ∣ S₀.index) (z₀ : W) (hz₀Q : z₀ ∈ Q)
    (hz₀1 : z₀ ≠ 1) (hz₀c : ∀ x ∈ S₀ ⊓ Q, z₀ * x = x * z₀)
    (hne : Nat.card {y : S₀ // y.1 ∉ Q ∧ y.1 * y.1 = 1} ≠
      Nat.card {y : S₀ // y.1 ∉ Q ∧ y.1 * y.1 = z₀}) :
    ∀ Sw : Subgroup W, IsPGroup 2 Sw → ¬ 2 ∣ Sw.index → ∀ zw ∈ Q, orderOf zw = 2 →
      centralizer ((Sw ⊓ Q : Subgroup W) : Set W) ⊓ Q = zpowers zw →
      Nat.card {y : Sw // y.1 ∉ Q ∧ y.1 * y.1 = 1} ≠
        Nat.card {y : Sw // y.1 ∉ Q ∧ y.1 * y.1 = zw} := by
  intro Sw hSw hSwi zw _ hzw2 hcent
  obtain ⟨g, hmem, hz'⟩ := exists_conj_of_one_sylow Q S₀ hS₀ hS₀i z₀ hz₀Q hz₀1 hz₀c Sw hSw hSwi zw
    hzw2 hcent
  have hQc : ∀ y : W, g⁻¹ * y * g ∈ Q ↔ y ∈ Q := by
    intro y
    constructor
    · intro h
      have := (inferInstance : Q.Normal).conj_mem _ h g
      simpa [mul_assoc] using this
    · intro h
      simpa using (inferInstance : Q.Normal).conj_mem _ h g⁻¹
  have hconj : ∀ a : W, Nat.card {y : Sw // y.1 ∉ Q ∧ y.1 * y.1 = a} =
      Nat.card {x : S₀ // x.1 ∉ Q ∧ x.1 * x.1 = g⁻¹ * a * g} := by
    intro a
    let e : Sw ≃ S₀ :=
      { toFun := fun y => ⟨g⁻¹ * y.1 * g, (hmem _).1 y.2⟩
        invFun := fun x => ⟨g * x.1 * g⁻¹, (hmem _).2 (by simp [mul_assoc])⟩
        left_inv := fun y => by ext; simp [mul_assoc]
        right_inv := fun x => by ext; simp [mul_assoc] }
    refine Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)
    show (y.1 ∉ Q ∧ y.1 * y.1 = a) ↔ (g⁻¹ * y.1 * g ∉ Q ∧ (g⁻¹ * y.1 * g) * (g⁻¹ * y.1 * g) =
      g⁻¹ * a * g)
    have hsq : (g⁻¹ * y.1 * g) * (g⁻¹ * y.1 * g) = g⁻¹ * (y.1 * y.1) * g := by group
    rw [hsq]
    refine and_congr (not_congr (hQc _).symm) ?_
    constructor
    · intro h
      rw [h]
    · intro h
      have := mul_left_cancel (mul_right_cancel h)
      exact this
  have e1 := hconj 1
  have e2 := hconj zw
  have hz0 : g⁻¹ * zw * g = z₀ := by rw [← hz']; group
  rw [show g⁻¹ * (1 : W) * g = 1 by group] at e1
  rw [hz0] at e2
  rw [e1, e2]
  exact hne

end CFSG.EvenSporadicStandard.HSStd
