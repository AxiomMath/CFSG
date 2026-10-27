module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeGraph
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic
import CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeAux.Twisted
import CFSG.HardMathSupport.Dickson.DefCharOuter.EntrywiseFixed
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeAux

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


section Types

variable {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
include hf hK

theorem perfectInLayer_of_fieldType (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1) (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) :
    PerfectInLayer α := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ :=
    exists_frobenius_of_cube Nat.prime_three hf K hK σ hσ3 hσ1
  rw [d4Graph_zero, mul_one] at hαeq
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hconj : ∀ (β : MulAut (adjointGroup Tag.D4 K)) (g' : adjointGroup Tag.D4 K)
      (a' : Fin Tag.D4.rank → Kˣ), β = MulAut.conj g' * exactNormalAut Tag.D4 K a' T 0 →
      β ^ 3 = 1 → PerfectInLayer β := by
    intro β g' a' hβ hβ3
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g' a' β hβ hβ3
    have h2 := LieSemisimple.perfectInLayer_conj ψ⁻¹ _
      (perfectInLayer_entrywiseAdjointAut Tag.D4 hK2 T)
    rwa [← hψ, show ψ⁻¹ * (ψ * β * ψ⁻¹) * ψ⁻¹⁻¹ = β by group] at h2
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    exact hconj α g a hαeq hα3
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hαeq] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    have hα22 : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα3, one_mul]
    exact perfectInLayer_of_fixSubgroup_eq (fixedSubgroup_pow_eq hα22)
      (hconj (α ^ 2) g' a' hα2 hα23)

theorem perfectInLayer_of_graphFieldType (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3)
    (hε0 : ε ≠ 0) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    PerfectInLayer α := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three Nat.prime_three hf K hK σ hord
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hε' : ε = 1 ∨ ε = 2 := by omega
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ :=
      exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T hT α hα3 g a ε hαeq
    have h := LieSemisimple.perfectInLayer_conj ψ⁻¹ _
      (perfectInLayer_twistedEntrywiseAut_D4 hK2 T (ε : ℤ) (by rcases hε' with rfl | rfl <;> simp))
    rwa [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at h
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) α hα3 g a ε hαeq
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    have hP := perfectInLayer_twistedEntrywiseAut_D4 hK2 T (3 - (ε : ℤ))
      (by rcases hε' with rfl | rfl <;> simp)
    rw [← hshift, ← hψ] at hP
    have h := LieSemisimple.perfectInLayer_conj ψ⁻¹ _ hP
    rw [show ψ⁻¹ * (ψ * α⁻¹ * ψ⁻¹) * ψ⁻¹⁻¹ = α⁻¹ by group] at h
    exact perfectInLayer_of_fixSubgroup_eq (fixedSubgroup_inv_eq α).symm h

end Types

theorem perfectInLayer_or_core_adjointD4_three (h1 : D4ThreeGraphOuter) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] [CharP K 3] (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.D4 K)) :
    PerfectInLayer α ∨ CFSG.Open.GLAPPrimeCoreOf 3 (fixSubgroup α) = ⊥ := by
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ := outer_cube_normal_form_cases α hα3 hα
  rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
  · subst hε0
    exact .inl (perfectInLayer_of_fieldType hf hK α hα3 g a σ hσ3 hσ1 hαeq)
  · exact .inl (perfectInLayer_of_graphFieldType hf hK α hα3 g a σ ε hε hε0 hσ3 hσ1 hαeq)
  · subst hσ1
    exact h1 K g a ε (Nat.pos_of_ne_zero hε0) hε α hαeq hα3

end CFSG.HardMathSupport.Dickson.DefCharOuter.D4ThreeAux
