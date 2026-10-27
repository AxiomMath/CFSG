module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Subgroup CFSG.Quasithin

variable {G : Type*} [Group G]

theorem exists_normalizer_conj_of_isWeaklyClosedIn [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {A : Subgroup G} (hAT : A ≤ T) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hwc : IsWeaklyClosedIn A T) {x y : G} (hx : x ∈ A) (hy : y ∈ A) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (A : Set G), n * x * n⁻¹ = y := by
  have hcent : ∀ c ∈ A, c ∈ centralizer (A : Set G) := fun c hc =>
    mem_centralizer_iff.mpr fun a ha => hA a ha c hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  obtain ⟨n, hn, hn'⟩ := burnside_fusion_lemma_centralizer T hAT hwc (hcent x hx) (hcent y hy)
    (g := c⁻¹) (by rw [inv_inv]; exact hc)
  exact ⟨n⁻¹, inv_mem hn, by rw [inv_inv]; exact hn'⟩

theorem eq_of_isConj_of_isWeaklyClosedIn [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {A : Subgroup G} (hAT : A ≤ T) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hwc : IsWeaklyClosedIn A T) {z e : G} (hz : z ∈ A)
    (hN : ∀ n ∈ normalizer (A : Set G), n * z * n⁻¹ = z) (he : e ∈ A) (hze : IsConj z e) :
    e = z := by
  obtain ⟨n, hn, rfl⟩ := exists_normalizer_conj_of_isWeaklyClosedIn T hAT hA hwc hz he hze
  exact hN n hn

theorem isWeaklyClosedIn_of_forall_eq_or_eq {A A' P : Subgroup G} (Φ : Subgroup G → Prop)
    (hΦ : ∀ g, Φ (conjSubgroup A g)) (hP : ∀ B ≤ P, Φ B → B = A ∨ B = A')
    (hA' : ∀ g, conjSubgroup A g ≠ A') : IsWeaklyClosedIn A P := by
  intro g hg
  rcases hP _ hg (hΦ g) with h | h
  · exact h
  · exact absurd h (hA' g)

theorem sq_eq_one_of_mem_conjSubgroup {A : Subgroup G} (hA : ∀ a ∈ A, a ^ 2 = 1) (g : G) :
    ∀ b ∈ conjSubgroup A g, b ^ 2 = 1 := by
  intro b hb
  rw [mem_conjSubgroup_iff] at hb
  have h := hA _ hb
  rw [conj_pow] at h
  have h' := congrArg (fun x => g⁻¹ * x * g) h
  simpa [mul_assoc] using h'

theorem card_conjSubgroup_eq (A : Subgroup G) (g : G) :
    Nat.card (conjSubgroup A g) = Nat.card A :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isWeaklyClosedIn_of_elementary_eq_or_eq {A A' P : Subgroup G}
    (hA : ∀ a ∈ A, a ^ 2 = 1)
    (hP : ∀ B : Subgroup G, B ≤ P → (∀ b ∈ B, b ^ 2 = 1) → Nat.card B = Nat.card A →
      B = A ∨ B = A')
    (hA' : ∀ g, conjSubgroup A g ≠ A') : IsWeaklyClosedIn A P :=
  isWeaklyClosedIn_of_forall_eq_or_eq (fun B => (∀ b ∈ B, b ^ 2 = 1) ∧ Nat.card B = Nat.card A)
    (fun g => ⟨sq_eq_one_of_mem_conjSubgroup hA g, card_conjSubgroup_eq A g⟩)
    (fun B hB h => hP B hB h.1 h.2) hA'

theorem isWeaklyClosedIn_of_elementary_unique {A P : Subgroup G} (hA : ∀ a ∈ A, a ^ 2 = 1)
    (hP : ∀ B : Subgroup G, B ≤ P → (∀ b ∈ B, b ^ 2 = 1) → Nat.card B = Nat.card A → B = A) :
    IsWeaklyClosedIn A P := fun g hg =>
  hP _ hg (sq_eq_one_of_mem_conjSubgroup hA g) (card_conjSubgroup_eq A g)

end CFSG.EvenSmallLie.OmegaEight
