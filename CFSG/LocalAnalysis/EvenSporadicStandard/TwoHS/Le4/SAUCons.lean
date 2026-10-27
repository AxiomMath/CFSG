module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

namespace SAU

variable {G : Type*} [Group G]

structure ConsHyp (T E E₁ : Subgroup G) (y' f : G) : Prop where
  E_le : E ≤ T
  E₁_le : E₁ ≤ E
  T_norm_E : ∀ z ∈ T, ∀ e ∈ E, z * e * z⁻¹ ∈ E
  T_norm_E₁ : ∀ z ∈ T, ∀ e ∈ E₁, z * e * z⁻¹ ∈ E₁
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  y_mem : y' ∈ T
  y_inv : ∀ e ∈ E, y' * e * y'⁻¹ = e⁻¹
  cls : ∀ z ∈ T, ∃ ε ∈ E, ε * ε = 1 ∧ z * y' * z⁻¹ = y' * ε
  sqrt : ∀ ε ∈ E, ε * ε = 1 → ∃ e ∈ E, e * e = ε
  inv_mem_E₁ : ∀ e ∈ E, e * e = 1 → e ∈ E₁
  f_mem : f ∈ E
  f_not : f ∉ E₁
  f_sq : f * f ∈ E₁
  cases : ∀ e ∈ E, e ∈ E₁ ∨ f⁻¹ * e ∈ E₁

variable {T E E₁ : Subgroup G} {y' f : G}

namespace ConsHyp

variable (hc : ConsHyp T E E₁ y' f)
include hc

theorem y_inv' {e : G} (he : e ∈ E) : y'⁻¹ * e * y' = e⁻¹ := by
  have hb : y'⁻¹ * e * y' ∈ E := by
    have := hc.T_norm_E y'⁻¹ (T.inv_mem hc.y_mem) e he
    simpa using this
  have h1 := hc.y_inv _ hb
  have h2 : y' * (y'⁻¹ * e * y') * y'⁻¹ = e := by group
  rw [h2] at h1
  have h3 : e⁻¹ = y'⁻¹ * e * y' := by simpa using congrArg (·⁻¹) h1
  exact h3.symm

theorem decomp {z : G} (hz : z ∈ T) :
    ∃ e ∈ E, ∃ c ∈ T, c * y' = y' * c ∧ z = e * c := by
  obtain ⟨ε, hεE, hεε, hzy⟩ := hc.cls z hz
  obtain ⟨e, heE, hee⟩ := hc.sqrt ε hεE hεε
  have heT : e ∈ T := hc.E_le heE
  refine ⟨e, heE, e⁻¹ * z, T.mul_mem (T.inv_mem heT) hz, ?_, by group⟩
  have h4 : (e * e) * (e * e) = 1 := by rw [hee]; exact hεε
  have h5 : e * ε = e⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hee]
    calc e * (e * e) * e = (e * e) * (e * e) := by group
      _ = 1 := h4
  have h6 : e⁻¹ * y' = y' * e := by
    have := hc.y_inv' (E.inv_mem heE)
    calc e⁻¹ * y' = y' * (y'⁻¹ * e⁻¹ * y') := by group
      _ = y' * e⁻¹⁻¹ := by rw [this]
      _ = y' * e := by rw [inv_inv]
  calc e⁻¹ * z * y' = e⁻¹ * (z * y' * z⁻¹) * z := by group
    _ = e⁻¹ * (y' * ε) * z := by rw [hzy]
    _ = (e⁻¹ * y') * ε * z := by group
    _ = (y' * e) * ε * z := by rw [h6]
    _ = y' * (e * ε) * z := by group
    _ = y' * (e⁻¹ * z) := by rw [h5]; group

theorem inter_le {e : G} (he : e ∈ E) (hcy : e * y' = y' * e) : e ∈ E₁ := by
  apply hc.inv_mem_E₁ e he
  have h1 := hc.y_inv e he
  have h2 : y' * e * y'⁻¹ = e := by
    calc y' * e * y'⁻¹ = e * y' * y'⁻¹ := by rw [← hcy]
      _ = e := by group
  rw [h2] at h1
  exact (congrArg (e * ·) h1).trans (mul_inv_cancel e)

def Usub : Subgroup G where
  carrier := {z | ∃ e ∈ E₁, ∃ c ∈ T, c * y' = y' * c ∧ z = e * c}
  one_mem' := ⟨1, E₁.one_mem, 1, T.one_mem, by group, by group⟩
  mul_mem' := by
    rintro _ _ ⟨e, he, c, hcT, hcy, rfl⟩ ⟨e', he', c', hc'T, hc'y, rfl⟩
    refine ⟨e * (c * e' * c⁻¹), E₁.mul_mem he (hc.T_norm_E₁ c hcT e' he'), c * c',
      T.mul_mem hcT hc'T, ?_, by group⟩
    calc c * c' * y' = c * (c' * y') := by rw [mul_assoc]
      _ = c * (y' * c') := by rw [hc'y]
      _ = (c * y') * c' := by rw [mul_assoc]
      _ = (y' * c) * c' := by rw [hcy]
      _ = y' * (c * c') := by rw [mul_assoc]
  inv_mem' := by
    rintro _ ⟨e, he, c, hcT, hcy, rfl⟩
    refine ⟨c⁻¹ * e⁻¹ * c, ?_, c⁻¹, T.inv_mem hcT, ?_, by group⟩
    · have := hc.T_norm_E₁ c⁻¹ (T.inv_mem hcT) e⁻¹ (E₁.inv_mem he)
      simpa using this
    · have h1 : c⁻¹ * y' = y' * c⁻¹ := by
        calc c⁻¹ * y' = c⁻¹ * (y' * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * y') * c⁻¹ := by rw [hcy]
          _ = y' * c⁻¹ := by group
      exact h1

theorem Usub_le : hc.Usub ≤ T := by
  rintro _ ⟨e, he, c, hcT, -, rfl⟩
  exact T.mul_mem (hc.E_le (hc.E₁_le he)) hcT

theorem E₁_le_Usub : E₁ ≤ hc.Usub := fun e he =>
  ⟨e, he, 1, T.one_mem, by group, by group⟩

theorem mem_Usub_iff {e c : G} (he : e ∈ E) (hcT : c ∈ T) (hcy : c * y' = y' * c) :
    e * c ∈ hc.Usub ↔ e ∈ E₁ := by
  constructor
  · rintro ⟨e', he', c', hc'T, hc'y, h⟩
    have h1 : e'⁻¹ * e = c' * c⁻¹ := by
      have : e' * c' = e * c := h.symm
      calc e'⁻¹ * e = e'⁻¹ * (e * c) * c⁻¹ := by group
        _ = e'⁻¹ * (e' * c') * c⁻¹ := by rw [this]
        _ = c' * c⁻¹ := by group
    have hE : e'⁻¹ * e ∈ E := E.mul_mem (E.inv_mem (hc.E₁_le he')) he
    have hcomm : (e'⁻¹ * e) * y' = y' * (e'⁻¹ * e) := by
      rw [h1]
      have hcy' : c⁻¹ * y' = y' * c⁻¹ := by
        calc c⁻¹ * y' = c⁻¹ * (y' * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * y') * c⁻¹ := by rw [hcy]
          _ = y' * c⁻¹ := by group
      calc c' * c⁻¹ * y' = c' * (c⁻¹ * y') := by rw [mul_assoc]
        _ = c' * (y' * c⁻¹) := by rw [hcy']
        _ = (c' * y') * c⁻¹ := by rw [mul_assoc]
        _ = (y' * c') * c⁻¹ := by rw [hc'y]
        _ = y' * (c' * c⁻¹) := by rw [mul_assoc]
    have hE1 : e'⁻¹ * e ∈ E₁ := inter_le hc hE hcomm
    have : e = e' * (e'⁻¹ * e) := by group
    rw [this]
    exact E₁.mul_mem he' hE1
  · intro he1
    exact ⟨e, he1, c, hcT, hcy, rfl⟩

theorem f_not_mem_Usub : f ∉ hc.Usub := by
  intro hf
  have : f * 1 ∈ hc.Usub := by simpa using hf
  exact hc.f_not ((hc.mem_Usub_iff hc.f_mem T.one_mem (by group)).1 this)

theorem relIndex_Usub : hc.Usub.relIndex T = 2 := by
  rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.index_eq_two_iff]
  refine ⟨⟨f, hc.E_le hc.f_mem⟩, fun b => ?_⟩
  obtain ⟨e, heE, c, hcT, hcy, hb⟩ := hc.decomp b.2
  have hbU : (b : G) ∈ hc.Usub ↔ e ∈ E₁ := by rw [hb]; exact hc.mem_Usub_iff heE hcT hcy
  have hf' : c * f * c⁻¹ ∈ E := hc.T_norm_E c hcT f hc.f_mem
  have hf'not : c * f * c⁻¹ ∉ E₁ := by
    intro h1
    apply hc.f_not
    have := hc.T_norm_E₁ c⁻¹ (T.inv_mem hcT) _ h1
    have e2 : c⁻¹ * (c * f * c⁻¹) * c⁻¹⁻¹ = f := by group
    rwa [e2] at this
  have hbf : (b : G) * f = (e * (c * f * c⁻¹)) * c := by rw [hb]; group
  have hef : e * (c * f * c⁻¹) ∈ E := E.mul_mem heE hf'
  have hbfU : (b : G) * f ∈ hc.Usub ↔ e * (c * f * c⁻¹) ∈ E₁ := by
    rw [hbf]; exact hc.mem_Usub_iff hef hcT hcy
  show Xor ((b : G) * f ∈ hc.Usub) ((b : G) ∈ hc.Usub)
  rw [hbfU, hbU]
  by_cases he1 : e ∈ E₁
  · refine Or.inr ⟨he1, ?_⟩
    intro h1
    apply hf'not
    have := E₁.mul_mem (E₁.inv_mem he1) h1
    simpa using this
  · refine Or.inl ⟨?_, he1⟩
    rcases hc.cases e heE with h1 | h1
    · exact absurd h1 he1
    · rcases hc.cases _ hf' with h2 | h2
      · exact absurd h2 hf'not
      · have hab : (f⁻¹ * e) * f = f * (f⁻¹ * e) :=
          hc.E_comm _ (E.mul_mem (E.inv_mem hc.f_mem) heE) _ hc.f_mem
        have e1 : e * (c * f * c⁻¹) =
            (f * f) * ((f⁻¹ * e) * (f⁻¹ * (c * f * c⁻¹))) := by
          calc e * (c * f * c⁻¹) = (f * (f⁻¹ * e)) * (f * (f⁻¹ * (c * f * c⁻¹))) := by group
            _ = f * ((f⁻¹ * e) * f) * (f⁻¹ * (c * f * c⁻¹)) := by group
            _ = f * (f * (f⁻¹ * e)) * (f⁻¹ * (c * f * c⁻¹)) := by rw [hab]
            _ = (f * f) * ((f⁻¹ * e) * (f⁻¹ * (c * f * c⁻¹))) := by group
        rw [e1]
        exact E₁.mul_mem hc.f_sq (E₁.mul_mem h1 h2)

end ConsHyp

end SAU

end CFSG.EvenSporadicStandard.TwoHS
