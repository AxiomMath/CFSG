module

public import CFSG.ClassicalInvolution.Phan.Phan3B3TwistData
public import CFSG.ClassicalInvolution.Phan.Phan3AModel
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable

theorem twist_trivial (h : ∀ p ∈ b3BadPairs, Subsingleton (PG 6 (b3TwistRels p.1 p.2)))
    {k₁ k₂ : Fin 24} (hk : (k₁, k₂) ∈ b3BadPairs)
    {Y : Type} [Group Y] (y : Fin 6 → Y) (hy : ∀ r ∈ b3TwistRels k₁ k₂, wordVal y r = 1)
    (i : Fin 6) : y i = 1 := by
  let f : PG 6 (b3TwistRels k₁ k₂) →* Y := PresentedGroup.toGroup (f := y) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact hy w hw)
  have hsub : Subsingleton (PG 6 (b3TwistRels k₁ k₂)) := h (k₁, k₂) hk
  have h2 : (PresentedGroup.of i : PG 6 (b3TwistRels k₁ k₂)) = 1 := Subsingleton.elim _ _
  calc y i = f (PresentedGroup.of i) := (PresentedGroup.toGroup.of _).symm
    _ = 1 := by rw [h2, map_one]

end CFSG.ClassicalInvolution.Phan.Q3G
