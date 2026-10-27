module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem commRank_conj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g t : G) :
    commRank ρ (g * t * g⁻¹) = commRank ρ t := by
  unfold commRank
  have h1 : ∀ x, ρ g (ρ g⁻¹ x) = x := fun x => by
    have := congrArg (fun f => f x) (map_mul ρ g g⁻¹); simpa using this.symm
  have h2 : ∀ x, ρ g⁻¹ (ρ g x) = x := fun x => by
    have := congrArg (fun f => f x) (map_mul ρ g⁻¹ g); simpa using this.symm
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinear (ρ g) (ρ g⁻¹)
    (by ext x; exact h1 x) (by ext x; exact h2 x)
  have hc : ρ (g * t * g⁻¹) - 1 = (ρ g) ∘ₗ (ρ t - 1) ∘ₗ (ρ g⁻¹) := by
    ext x
    have := congrArg (fun f => f x) (map_mul ρ (g * t) g⁻¹)
    have h3 := congrArg (fun f => f (ρ g⁻¹ x)) (map_mul ρ g t)
    simp only [Module.End.mul_apply] at this h3
    simp [this, h3, h1]
  have h : LinearMap.range (ρ (g * t * g⁻¹) - 1) =
      (LinearMap.range (ρ t - 1)).map (e : V →ₗ[ZMod 2] V) := by
    rw [hc, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (by
      rw [LinearMap.range_eq_top]; intro x; exact ⟨ρ g x, h2 x⟩)]
    rfl
  rw [h]
  exact LinearEquiv.finrank_map_eq e _

end Section5

end CFSG.LocalAnalysis.RankThreeUC
