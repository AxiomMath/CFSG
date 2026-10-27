module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

theorem gh23_hom_of_gens {G H : Type*} [Group G] [Group H] [Finite G] (gens : Set G)
    (hgen : Subgroup.closure gens = ⊤) (φ ψ : G → H) (h1 : φ 1 = 1)
    (hφ : ∀ x, ∀ g ∈ gens, φ (x * g) = φ x * ψ g) : ∀ x y, φ (x * y) = φ x * φ y := by
  have hψ : ∀ g ∈ gens, ψ g = φ g := by
    intro g hg
    have h := hφ 1 g hg
    rw [one_mul, h1, one_mul] at h
    exact h.symm
  have hmem : ∀ y : G, y ∈ Submonoid.closure gens := by
    intro y
    rw [← Subgroup.closure_toSubmonoid_of_finite, hgen]
    exact Subgroup.mem_top y
  have key : ∀ m ∈ Submonoid.closure gens, ∀ x, φ (x * m) = φ x * φ m := by
    intro m hm
    induction hm using Submonoid.closure_induction_right with
    | one => intro x; rw [mul_one, h1, mul_one]
    | mul_right m hm g hg ih =>
        intro x
        have hmg : φ (m * g) = φ m * φ g := by rw [hφ m g hg, hψ g hg]
        calc φ (x * (m * g)) = φ ((x * m) * g) := by rw [mul_assoc]
          _ = φ (x * m) * ψ g := hφ (x * m) g hg
          _ = (φ x * φ m) * ψ g := by rw [ih x]
          _ = (φ x * φ m) * φ g := by rw [hψ g hg]
          _ = φ x * (φ m * φ g) := by rw [mul_assoc]
          _ = φ x * φ (m * g) := by rw [hmg]
  intro x y
  exact key y (hmem y) x

theorem gh23_mulEquiv_of_gens {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (gens : Set G) (hgen : Subgroup.closure gens = ⊤) (φ ψ : G → H) (h1 : φ 1 = 1)
    (hφ : ∀ x, ∀ g ∈ gens, φ (x * g) = φ x * ψ g) (hinj : Function.Injective φ)
    (hcard : Nat.card H ≤ Nat.card G) : Nonempty (G ≃* H) := by
  let f : G →* H := MonoidHom.mk' φ (gh23_hom_of_gens gens hgen φ ψ h1 hφ)
  have hfinj : Function.Injective f := fun a b h => hinj h
  have hbij : Function.Bijective f := hfinj.bijective_of_nat_card_le hcard
  exact ⟨MulEquiv.ofBijective f hbij⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
