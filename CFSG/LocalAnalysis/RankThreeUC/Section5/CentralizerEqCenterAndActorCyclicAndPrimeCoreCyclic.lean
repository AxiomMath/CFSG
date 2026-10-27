module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActorCyclicity

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem centralizer_eq_center_and_actor_cyclic_and_primeCore_cyclic {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    (∀ b ∈ B, b ≠ 1 → P ⊓ Subgroup.centralizer ({b} : Set G) = centerP P) ∧
    IsCyclic ↥B ∧
    (p ∉ piOf B → ∀ b ∈ B, b ≠ 1 → ∀ g ∈ P, b * g * b⁻¹ * g⁻¹ ∈ centerP P → g ∈ centerP P) :=
  ⟨centralizer_nonidentity_actor_eq_center h, actor_isCyclic h, actor_isSemiregular_on_central_quotient h⟩

end Section5
end CFSG.LocalAnalysis.RankThreeUC
