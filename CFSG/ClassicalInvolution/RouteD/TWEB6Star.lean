module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)

section Star

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem star_twin (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {c l₁ l₂ l₃ : Subgroup (V ≃ₗ[K] V)} {ic i₁ i₂ i₃ : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (h₁ : IsFundamental Q l₁ i₁) (h₂ : IsFundamental Q l₂ i₂) (h₃ : IsFundamental Q l₃ i₃)
    (a₁ : ModelAdj (scalars K V) c l₁) (a₂ : ModelAdj (scalars K V) c l₂)
    (a₃ : ModelAdj (scalars K V) c l₃) (k12 : Commutes l₁ l₂) (k13 : Commutes l₁ l₃)
    (k23 : Commutes l₂ l₃) : i₂ = i₁ ∨ i₃ = i₁ ∨ i₃ = i₂ := by
  obtain ⟨cm₁, N₁, C₁⟩ := adj_data hodd hdim hc h₁ a₁
  obtain ⟨cm₂, N₂, C₂⟩ := adj_data hodd hdim hc h₂ a₂
  obtain ⟨cm₃, N₃, C₃⟩ := adj_data hodd hdim hc h₃ a₃
  have pd₁ := (lemma_6_10 hodd hc h₁ cm₁ N₁ C₁).1
  have pd₂ := (lemma_6_10 hodd hc h₂ cm₂ N₂ C₂).1
  have pd₃ := (lemma_6_10 hodd hc h₃ cm₃ N₃ C₃).1
  rcases orth_or_twin hodd h₁ h₂ k12 with o12 | t12
  swap
  · exact Or.inl t12
  rcases orth_or_twin hodd h₁ h₃ k13 with o13 | t13
  swap
  · exact Or.inr (Or.inl t13)
  rcases orth_or_twin hodd h₂ h₃ k23 with o23 | t23
  swap
  · exact Or.inr (Or.inr t23)
  exfalso
  refine not_three_orth_planes (Q := Q) (W := negSpace ic)
    (P₁ := negSpace ic ⊓ negSpace i₁) (P₂ := negSpace ic ⊓ negSpace i₂)
    (P₃ := negSpace ic ⊓ negSpace i₃) (finrank_negSpace hodd hc) inf_le_left inf_le_left
    inf_le_left pd₁.finrank_U₂ pd₂.finrank_U₂ pd₃.finrank_U₂ pd₁.nondeg₂ pd₃.nondeg₂ ?_ ?_ ?_
  · exact fun x hx y hy => o12 x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => o13 x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => o23 x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2

theorem star_twin_of_distinguish (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {c l₁ l₂ l₃ S : Subgroup (V ≃ₗ[K] V)} {ic i₁ i₂ i₃ iS : V ≃ₗ[K] V}
    (hc : IsFundamental Q c ic) (h₁ : IsFundamental Q l₁ i₁) (h₂ : IsFundamental Q l₂ i₂)
    (h₃ : IsFundamental Q l₃ i₃) (hS : IsFundamental Q S iS)
    (a₁ : ModelAdj (scalars K V) c l₁) (a₂ : ModelAdj (scalars K V) c l₂)
    (a₃ : ModelAdj (scalars K V) c l₃) (k12 : Commutes l₁ l₂) (k13 : Commutes l₁ l₃)
    (k23 : Commutes l₂ l₃) (hS1 : S ≠ l₁) (hS2 : S ≠ l₂) (hS3 : S ≠ l₃)
    (hI₁ : ModelInvComm (scalars K V) S l₁) (hI₂ : ModelInvComm (scalars K V) S l₂)
    (hI₃ : ModelInvComm (scalars K V) S l₃) (c1 : Commutes S l₁) (n2 : ¬ Commutes S l₂)
    (n3 : ¬ Commutes S l₃) : i₂ ≠ i₁ ∧ i₃ ≠ i₁ ∧ i₃ = i₂ := by
  have hl12 : l₁ ≠ l₂ := fun h => n2 (h ▸ c1)
  have hl13 : l₁ ≠ l₃ := fun h => n3 (h ▸ c1)
  have hS' : S ∈ fundSet Q := ⟨iS, hS⟩
  have e2 : i₂ ≠ i₁ := fun h => by
    have hind := indist_of_eq hodd hdim h₁ h₂ hl12 h
    exact n2 ((hind.2 S hS' hS1 hS2 hI₁ hI₂).mp c1)
  have e3 : i₃ ≠ i₁ := fun h => by
    have hind := indist_of_eq hodd hdim h₁ h₃ hl13 h
    exact n3 ((hind.2 S hS' hS1 hS3 hI₁ hI₃).mp c1)
  rcases star_twin hodd hdim hc h₁ h₂ h₃ a₁ a₂ a₃ k12 k13 k23 with h | h | h
  · exact absurd h e2
  · exact absurd h e3
  · exact ⟨e2, e3, h⟩

end Star

section Dim

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem le_of_two_distinct {U E N₁ N₂ : Submodule K V} (hU : Module.finrank K U ≤ 5)
    (h₁ : N₁ ≤ U ⊓ E) (h₂ : N₂ ≤ U ⊓ E) (hd₁ : Module.finrank K N₁ = 4)
    (hd₂ : Module.finrank K N₂ = 4) (hne : N₁ ≠ N₂) : U ≤ E := by
  by_contra hUE
  have hlt : U ⊓ E < U := lt_of_le_of_ne inf_le_left fun h => hUE (h ▸ inf_le_right)
  have h4 : Module.finrank K ↥(U ⊓ E) < 5 := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have e1 : N₁ = U ⊓ E :=
    Submodule.eq_of_le_of_finrank_le h₁ (by have := Submodule.finrank_mono h₁; omega)
  have e2 : N₂ = U ⊓ E :=
    Submodule.eq_of_le_of_finrank_le h₂ (by have := Submodule.finrank_mono h₂; omega)
  exact hne (e1.trans e2.symm)

end Dim

end CFSG.ClassicalInvolution.RouteD.TWE.B6
