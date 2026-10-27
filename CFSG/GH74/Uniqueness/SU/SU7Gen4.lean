module

public import CFSG.GH74.Uniqueness.SU.SU7Gen
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup

theorem exists_normalizer_conj {X : Type*} [Group X] [Finite X] {R O : Subgroup X} [O.Normal]
    (hRp : IsPGroup 2 R) (hOodd : Odd (Nat.card O))
    (hKn : ∀ h : X, ∀ r ∈ R, h * r * h⁻¹ ∈ R ⊔ O) (g : X) :
    ∃ n ∈ normalizer (R : Set X), ∃ r₁ ∈ R, ∀ r ∈ R, g * r * g⁻¹ ∈ R →
      n * r * n⁻¹ = r₁ * (g * r * g⁻¹) * r₁⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Rg : Subgroup X := R.map (MulAut.conj g).toMonoidHom with hRg
  have hRgN : Rg ≤ R ⊔ O := by
    rintro _ ⟨r, hr, rfl⟩
    exact hKn g r hr
  have hRgp : IsPGroup 2 Rg := hRp.map _
  have hidx : ¬ 2 ∣ R.relIndex (R ⊔ O) := by
    rw [Gen.relIndex_sup_odd O hRp hOodd]
    have := Nat.odd_iff.1 hOodd
    omega
  obtain ⟨c, hc, hcR⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 2) hRgN hRgp
    le_sup_left hRp hidx
  have hnN : c⁻¹ * g ∈ normalizer (R : Set X) := by
    apply Gen.mem_normalizer_of_conj_le
    intro r hr
    have := hcR (g * r * g⁻¹) ⟨r, hr, by simp [MulAut.conj_apply]⟩
    have e : c⁻¹ * g * r * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * r * g⁻¹) * c := by group
    rw [e]; exact this
  obtain ⟨r', hr', o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hc
  refine ⟨(r' * o)⁻¹ * g, hnN, r'⁻¹, R.inv_mem hr', fun r hr he => ?_⟩
  set e := g * r * g⁻¹ with he_def
  have hnr : (r' * o)⁻¹ * g * r * ((r' * o)⁻¹ * g)⁻¹ ∈ R := (mem_normalizer_iff.1 hnN r).1 hr
  have e1 : (r' * o)⁻¹ * g * r * ((r' * o)⁻¹ * g)⁻¹ = o⁻¹ * (r'⁻¹ * e * r') * o := by
    rw [he_def]; group
  have he₁ : r'⁻¹ * e * r' ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hr') he) hr'
  rw [e1] at hnr ⊢
  set e₁ := r'⁻¹ * e * r' with he₁_def
  have h1 : e₁⁻¹ * (o⁻¹ * e₁ * o) ∈ R := R.mul_mem (R.inv_mem he₁) hnr
  have h2 : e₁⁻¹ * (o⁻¹ * e₁ * o) ∈ O := by
    have : e₁⁻¹ * (o⁻¹ * e₁ * o) = (e₁⁻¹ * o⁻¹ * e₁) * o := by group
    rw [this]
    exact O.mul_mem (by
      have := (inferInstance : O.Normal).conj_mem o⁻¹ (O.inv_mem ho) e₁⁻¹
      simpa [mul_assoc] using this) ho
  have h3 : e₁⁻¹ * (o⁻¹ * e₁ * o) ∈ R ⊓ O := ⟨h1, h2⟩
  rw [Gen.inf_eq_bot_of_isPGroup hRp hOodd, Subgroup.mem_bot] at h3
  have h4 : o⁻¹ * e₁ * o = e₁ := (inv_mul_eq_one.1 h3).symm
  rw [h4, he₁_def]
  group

end CFSG.GH74.Uniqueness.SU.SU7.Gen
