module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GF2Type.Smith1979.Case2

variable {α : Type*}

theorem card_fixed_modEq [Finite α] (f : α → α) {p : ℕ} [hp : Fact p.Prime]
    (hf : f^[p] = id) :
    Nat.card α ≡ (Function.fixedPoints f).ncard [MOD p] := by
  classical
  have := Fintype.ofFinite α
  have hE : (show Function.End α from f) ^ (p ^ 1) = 1 := by
    rw [pow_one]
    exact hf
  have h := Equiv.Perm.card_fixedPoints_modEq hE
  rw [Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  convert h using 2

theorem unique_fixed_of_seven [Finite α] (hα : Nat.card α = 8) (f : α → α)
    (hf : f^[7] = id) {x₀ : α} (hx₀ : f x₀ = x₀) (hne : ∃ x, f x ≠ x) :
    ∀ x, f x = x → x = x₀ := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro x hx
  by_contra hxx
  have hmod := card_fixed_modEq f hf
  have hone : 1 < (Function.fixedPoints f).ncard := by
    rw [Set.one_lt_ncard_iff]
    exact ⟨x₀, x, hx₀, hx, fun h => hxx h.symm⟩
  have hle : (Function.fixedPoints f).ncard ≤ 8 := by
    rw [← hα, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have hc : (Function.fixedPoints f).ncard = 8 := by
    rw [hα] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨z, hz⟩ := hne
  have hfull : Function.fixedPoints f = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (le_of_eq ?_) Set.finite_univ
    rw [Set.ncard_univ, hα, hc]
  have hzmem : z ∈ Function.fixedPoints f := by rw [hfull]; exact Set.mem_univ z
  exact hz (Function.mem_fixedPoints_iff.mp hzmem)

theorem orbit_of_seven [Finite α] (hα : Nat.card α = 8) (f : α → α)
    (hf : f^[7] = id) {x₀ : α} (hx₀ : f x₀ = x₀)
    (huniq : ∀ x, f x = x → x = x₀) {x₁ : α} (hx₁ : x₁ ≠ x₀) {w : α} (hw : w ≠ x₀) :
    ∃ k : ℕ, f^[k] x₁ = w := by
  classical
  have hper7 : ∀ x, f^[7] x = x := fun x => congrFun hf x
  have hinj : Function.Injective f :=
    Function.LeftInverse.injective (g := f^[6]) (fun x => by
      rw [← Function.iterate_succ_apply]
      exact hper7 x)
  have hdist : ∀ a b : ℕ, a < b → b < 7 → f^[a] x₁ ≠ f^[b] x₁ := by
    intro a b hab hb heq
    have h1 : f^[b] x₁ = f^[a] (f^[b - a] x₁) := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le hab.le]
    rw [h1] at heq
    have h2 : f^[b - a] x₁ = x₁ := (hinj.iterate a) heq.symm
    have hp : Function.IsPeriodicPt f (Nat.gcd 7 (b - a)) x₁ :=
      Function.IsPeriodicPt.gcd (hper7 x₁ : Function.IsPeriodicPt f 7 x₁) h2
    have hd : Nat.gcd 7 (b - a) = 1 := by
      have hd1 : 0 < b - a := by omega
      have hd2 : b - a < 7 := by omega
      have key : ∀ d < 7, 0 < d → Nat.gcd 7 d = 1 := by decide
      exact key _ hd2 hd1
    rw [hd] at hp
    have hfix : f x₁ = x₁ := hp
    exact hx₁ (huniq x₁ hfix)
  have hinjOn : ∀ a ∈ Finset.range 7, ∀ b ∈ Finset.range 7,
      f^[a] x₁ = f^[b] x₁ → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_range] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hdist a b h hb hab
    · exact hdist b a h ha hab.symm
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite α
  let s : Finset α := Finset.image (fun k => f^[k] x₁) (Finset.range 7)
  have hs_card : s.card = 7 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact hinjOn a ha b hb hab
  have hx₀_ne : ∀ k < 7, f^[k] x₁ ≠ x₀ := by
    intro k hk heq
    have h1 : f^[7 - k] (f^[k] x₁) = x₁ := by
      rw [← Function.iterate_add_apply, show 7 - k + k = 7 by omega]
      exact hper7 x₁
    rw [heq, Function.iterate_fixed hx₀] at h1
    exact hx₁ h1.symm
  have hsub : s ⊆ (Finset.univ.erase x₀).erase w := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_range] at hk
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨hcon k, hx₀_ne k hk, Finset.mem_univ _⟩
  have hw_mem : w ∈ Finset.univ.erase x₀ := Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩
  have hcard : ((Finset.univ.erase x₀).erase w).card = 6 := by
    rw [Finset.card_erase_of_mem hw_mem, Finset.card_erase_of_mem (Finset.mem_univ x₀),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hα]
  have := Finset.card_le_card hsub
  omega

theorem exists_fixed_ne_of_three [Finite α] (hα : Nat.card α = 8) (f : α → α)
    (hf : f^[3] = id) {x₀ : α} (hx₀ : f x₀ = x₀) :
    ∃ x, f x = x ∧ x ≠ x₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h
  push Not at h
  have hmod := card_fixed_modEq f hf
  have hsub : Function.fixedPoints f = {x₀} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_singleton_iff.mpr (h x (Function.mem_fixedPoints_iff.mp hx))
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Function.mem_fixedPoints_iff.mpr hx₀
  rw [hsub, Set.ncard_singleton, hα] at hmod
  unfold Nat.ModEq at hmod
  omega

end CFSG.GF2Type.Smith1979.Case2
