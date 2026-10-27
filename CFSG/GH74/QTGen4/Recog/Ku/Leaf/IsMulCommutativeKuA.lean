module

public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.CardKuA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem leafIsMulCommutativeKuA : LeafIsMulCommutativeKuA := by
  intro G _ _ T M H P z h
  obtain ⟨u₀, hu₀A, hu₀P⟩ := h.exists_mem_kuA_not_mem_P
  have hu₀Q : u₀ ∈ pCoreOf 2 H := (Subgroup.mem_inf.mp hu₀A).1
  have hWu : ∀ w ∈ kuW P H, w * u₀ = u₀ * w := fun w hw =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu₀A).2 w hw
  obtain ⟨u, -, hcos⟩ := h.exists_u_coset
  have hcoset : ∀ b ∈ pCoreOf 2 H, b ∉ P → ∀ c ∈ pCoreOf 2 H, c ∉ P → b * c⁻¹ ∈ P := by
    intro b hb hbP c hc hcP
    have e : b * c⁻¹ = (b * u) * (c * u)⁻¹ := by group
    rw [e]
    exact P.mul_mem ((hcos b hb).mpr hbP) (P.inv_mem ((hcos c hc).mpr hcP))
  have hdec : ∀ b ∈ kuA P H, b ∈ kuW P H ∨ ∃ w ∈ kuW P H, b = w * u₀ := by
    intro b hbA
    by_cases hbP : b ∈ P
    · left
      have hb : b ∈ kuA P H ⊓ P := ⟨hbA, hbP⟩
      rwa [h.kuA_inf_P] at hb
    · right
      have hbQ : b ∈ pCoreOf 2 H := (Subgroup.mem_inf.mp hbA).1
      have hmP : b * u₀⁻¹ ∈ P := hcoset b hbQ hbP u₀ hu₀Q hu₀P
      have hmA : b * u₀⁻¹ ∈ kuA P H := Subgroup.mul_mem _ hbA (Subgroup.inv_mem _ hu₀A)
      have hm : b * u₀⁻¹ ∈ kuA P H ⊓ P := ⟨hmA, hmP⟩
      rw [h.kuA_inf_P] at hm
      exact ⟨b * u₀⁻¹, hm, by group⟩
  have hu₀comm : ∀ b ∈ kuA P H, u₀ * b = b * u₀ := by
    intro b hbA
    rcases hdec b hbA with hb | ⟨w, hw, rfl⟩
    · exact (hWu b hb).symm
    · calc u₀ * (w * u₀) = (u₀ * w) * u₀ := (mul_assoc _ _ _).symm
        _ = (w * u₀) * u₀ := by rw [← hWu w hw]
  have hWcomm : ∀ w ∈ kuW P H, ∀ b ∈ kuA P H, w * b = b * w := by
    intro w hw b hbA
    rcases hdec b hbA with hb | ⟨w', hw', rfl⟩
    · exact h.kuW_comm_mem hw hb
    · calc w * (w' * u₀) = (w * w') * u₀ := (mul_assoc _ _ _).symm
        _ = (w' * w) * u₀ := by rw [h.kuW_comm_mem hw hw']
        _ = w' * (w * u₀) := mul_assoc _ _ _
        _ = w' * (u₀ * w) := by rw [hWu w hw]
        _ = (w' * u₀) * w := (mul_assoc _ _ _).symm
  have hcomm : ∀ a ∈ kuA P H, ∀ b ∈ kuA P H, a * b = b * a := by
    intro a ha b hb
    rcases hdec a ha with haW | ⟨w, hw, rfl⟩
    · exact hWcomm a haW b hb
    · calc w * u₀ * b = w * (u₀ * b) := mul_assoc _ _ _
        _ = w * (b * u₀) := by rw [hu₀comm b hb]
        _ = (w * b) * u₀ := (mul_assoc _ _ _).symm
        _ = (b * w) * u₀ := by rw [hWcomm w hw b hb]
        _ = b * (w * u₀) := mul_assoc _ _ _
  exact ⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩

end CFSG.GH74.QTGen4.Ku
