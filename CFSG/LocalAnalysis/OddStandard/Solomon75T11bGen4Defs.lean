module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreShape

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def SylowGen4 (n : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ S : Sylow 2 K,
    ∀ H : Subgroup K, H ≤ (S : Subgroup K) →
      ∃ s : Finset K, s.card ≤ 4 ∧ Subgroup.closure (s : Set K) = H

theorem exists_gen_of_injective {A B : Type} [Group A] [Group B] [DecidableEq A] (f : A →* B)
    (hf : Function.Injective f) (H : Subgroup A) (s : Finset B) (hs : s.card ≤ 4)
    (hcl : Subgroup.closure (s : Set B) = H.map f) :
    ∃ t : Finset A, t.card ≤ 4 ∧ Subgroup.closure (t : Set A) = H := by
  classical
  have hmem : ∀ b ∈ s, ∃ a ∈ H, f a = b := fun b hb => by
    have : b ∈ H.map f := hcl ▸ Subgroup.subset_closure hb
    exact this
  choose! g hgH hgf using hmem
  have himg : f '' ((s.image g : Finset A) : Set A) = (s : Set B) := by
    ext x
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      rw [hgf b hb]
      exact hb
    · intro hx
      exact ⟨g x, ⟨x, hx, rfl⟩, hgf x hx⟩
  refine ⟨s.image g, (Finset.card_image_le).trans hs, ?_⟩
  apply Subgroup.map_injective hf
  rw [MonoidHom.map_closure, himg, hcl]

theorem gen4_of_hasSylowTwoTypeAhat {G : Type} [Group G] [Finite G] {n : ℕ} (hG4 : SylowGen4 n)
    (h : HasSylowTwoTypeAhat G n) :
    ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P := by
  classical
  intro P hP
  obtain ⟨X, _, hX, P', Q, ⟨e⟩⟩ := h
  have := CoreAux.finite_of_doubleCover hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P'', hPP''⟩ := hP.exists_le_sylow
  have e2 : ↥(P'' : Subgroup G) ≃* ↥(Q : Subgroup X) := (Sylow.equiv P'' P').trans e
  let φ : ↥(P'' : Subgroup G) →* X := (Q : Subgroup X).subtype.comp e2.toMonoidHom
  have hφ : Function.Injective φ := fun a b hab => e2.injective (Subtype.ext hab)
  let H' : Subgroup ↥(P'' : Subgroup G) := P.subgroupOf (P'' : Subgroup G)
  have hHQ : H'.map φ ≤ (Q : Subgroup X) := by
    rintro _ ⟨a, -, rfl⟩
    exact (e2 a).2
  obtain ⟨s, hs, hcl⟩ := hG4 X hX Q (H'.map φ) hHQ
  obtain ⟨t, ht, htcl⟩ := exists_gen_of_injective φ hφ H' s hs hcl
  refine ⟨t.image (P'' : Subgroup G).subtype, (Finset.card_image_le).trans ht, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, htcl]
  exact Subgroup.map_subgroupOf_eq_of_le hPP''

end CFSG.OddStandard.Solomon75
