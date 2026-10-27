module

public import CFSG.ClassicalInvolution.Asc77.AscP1Transfer

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open Subgroup CFSG.ClassicalInvolution.Asc77

variable {G : Type*} [Group G] {A : Type*} [CommGroup A]

theorem hom_eq_one_of_isSimpleGroup [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x)
    (f : G →* A) : f = 1 := by
  have := f.normal_ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    apply f.ker_eq_bot_iff.mp h
    rw [map_mul, map_mul, mul_comm]
  · ext x
    have : x ∈ f.ker := by rw [h]; exact Subgroup.mem_top x
    simpa using this

theorem exists_fusion_of_isSimpleGroup [Finite G] [IsSimpleGroup G]
    (hnc : ∃ x y : G, x * y ≠ y * x) {H : Subgroup G} (hodd : Odd H.index) (ϕ : ↥H →* A)
    {a : G} (ha : a ∈ H) (ha2 : IsPGroup 2 (zpowers a)) (hϕ : ϕ ⟨a, ha⟩ ≠ 1) :
    ∃ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H),
      ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ ≠ ϕ ⟨a, ha⟩ ^ n := by
  by_contra hcon
  push Not at hcon
  have h1 := transfer_apply_ne_one ϕ a ha ha2 hϕ hodd hcon
  apply h1
  rw [hom_eq_one_of_isSimpleGroup hnc (MonoidHom.transfer ϕ)]
  rfl

end CFSG.ClassicalInvolution.Asc77.T3CII
