module

public import CFSG.Goldschmidt75.Closure

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

noncomputable def sylowOfInf (P : Sylow p G) (L : Subgroup G)
    (h : Nat.card ↥((P : Subgroup G) ⊓ L) = p ^ (Nat.card L).factorization p) : Sylow p L :=
  Sylow.ofCard (((P : Subgroup G) ⊓ L).subgroupOf L)
    ((Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).trans h)

theorem mem_sylowOfInf {P : Sylow p G} {L : Subgroup G}
    {h : Nat.card ↥((P : Subgroup G) ⊓ L) = p ^ (Nat.card L).factorization p} {x : L} :
    x ∈ (sylowOfInf P L h : Subgroup L) ↔ (x : G) ∈ (P : Subgroup G) := by
  change (x : G) ∈ (P : Subgroup G) ⊓ L ↔ _
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩

omit [Finite G] [Fact p.Prime] in
theorem card_inf_normalizer {P : Sylow p G} {S₀ : Subgroup G} (h : FullyNormalized p P S₀) :
    Nat.card ↥((P : Subgroup G) ⊓ normalizer (S₀ : Set G)) =
      p ^ (Nat.card (normalizer (S₀ : Set G))).factorization p := h

theorem stronglyClosed_inf_subgroupOf (P : Sylow p G) {S : Subgroup G}
    (hS : fusionStronglyClosed (S : Set G) P) (L : Subgroup G)
    (h : Nat.card ↥((P : Subgroup G) ⊓ L) = p ^ (Nat.card L).factorization p) :
    fusionStronglyClosed (((S ⊓ L).subgroupOf L : Subgroup L) : Set L)
      (sylowOfInf P L h : Subgroup L) := by
  intro a ha l hl
  rw [mem_sylowOfInf] at hl
  have hl' : (l : G)⁻¹ * a * l ∈ (P : Subgroup G) := by simpa using hl
  have h1 : (l : G)⁻¹ * a * l ∈ S := hS _ ha.1 _ hl'
  exact ⟨by simpa using h1, (l⁻¹ * a * l).2⟩

theorem inf_subgroupOf_le_sylowOfInf (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (L : Subgroup G)
    (h : Nat.card ↥((P : Subgroup G) ⊓ L) = p ^ (Nat.card L).factorization p) :
    (S ⊓ L).subgroupOf L ≤ (sylowOfInf P L h : Subgroup L) := fun _ hx =>
  mem_sylowOfInf.2 (hSP hx.1)

theorem card_inf_of_le (P : Sylow p G) {L : Subgroup G} (hPL : (P : Subgroup G) ≤ L) :
    Nat.card ↥((P : Subgroup G) ⊓ L) = p ^ (Nat.card L).factorization p := by
  rw [inf_eq_left.mpr hPL]
  have := Sylow.card_eq_multiplicity (P.subtype hPL)
  rw [← this]
  exact (Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv).symm.trans rfl

end CFSG.Goldschmidt75
