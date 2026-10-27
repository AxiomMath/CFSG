module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem false_of_alt_normalizes {N : ℕ} (Z : Subgroup (Perm (Fin N))) (hZ : IsPGroup 2 Z)
    (Δ : Finset (Fin N)) (hΔ : 5 ≤ Δ.card) {p : Perm (Fin N)} (hp : p ∈ Z) (hp1 : p ≠ 1)
    (hpA : p ∈ alternatingGroup (Fin N)) (hpfix : ∀ i, i ∉ Δ → p i = i)
    (hN : ∀ h ∈ alternatingGroup (Fin N), (∀ i, i ∉ Δ → h i = i) →
      h ∈ Subgroup.normalizer (Z : Set (Perm (Fin N)))) : False := by
  classical
  let φ : Perm {i // i ∈ Δ} →* Perm (Fin N) := Perm.ofSubtype
  have hφinj : Function.Injective φ := Perm.ofSubtype_injective
  have hφfix : ∀ (a : Perm {i // i ∈ Δ}) (i : Fin N), i ∉ Δ → φ a i = i := by
    intro a i hi
    exact Perm.ofSubtype_apply_of_not_mem a hi
  have hφalt : ∀ a : ↥(alternatingGroup {i // i ∈ Δ}), φ a ∈ alternatingGroup (Fin N) := by
    intro a
    rw [mem_alternatingGroup, show φ a = Perm.ofSubtype (a : Perm {i // i ∈ Δ}) from rfl,
      Perm.sign_ofSubtype]
    exact mem_alternatingGroup.1 a.2
  let ψ : ↥(alternatingGroup {i // i ∈ Δ}) →* Perm (Fin N) :=
    φ.comp (alternatingGroup {i // i ∈ Δ}).subtype
  let N0 : Subgroup ↥(alternatingGroup {i // i ∈ Δ}) := Z.comap ψ
  have hN0 : N0.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : ψ g ∈ Subgroup.normalizer (Z : Set (Perm (Fin N))) :=
      hN _ (hφalt g) (fun i hi => hφfix _ i hi)
    have h1 := (Subgroup.mem_normalizer_iff.1 hg (ψ x)).1 hx
    show ψ (g * x * g⁻¹) ∈ Z
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hcard : 5 ≤ Nat.card {i // i ∈ Δ} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hΔ
  have hsimple : IsSimpleGroup ↥(alternatingGroup {i // i ∈ Δ}) :=
    alternatingGroup.isSimpleGroup hcard
  rcases hN0.eq_bot_or_eq_top with hbot | htop
  ·
    have hpmem : ∀ x, p x ≠ x → x ∈ Δ := fun x hx => by
      by_contra h
      exact hx (hpfix x h)
    have hpΔ : ∀ x, (fun i : Fin N => i ∈ Δ) (p x) ↔ (fun i : Fin N => i ∈ Δ) x := by
      intro x
      by_cases hx : x ∈ Δ
      · simp only [hx, iff_true]
        by_contra hpx
        exact hpx (by
          have := hpfix (p x) hpx
          have h2 : p (p x) = p x := this
          have h3 := p.injective h2
          rw [h3]; exact hx)
      · simp only [hx, iff_false]
        intro hpx
        have := hpfix x hx
        rw [this] at hpx
        exact hx hpx
    let q : Perm {i // i ∈ Δ} := p.subtypePerm hpΔ
    have hqφ : φ q = p := Perm.ofSubtype_subtypePerm hpΔ hpmem
    have hqA : q ∈ alternatingGroup {i // i ∈ Δ} := by
      rw [mem_alternatingGroup]
      have h1 : sign (φ q) = sign q := Perm.sign_ofSubtype q
      rw [← h1, hqφ]
      exact mem_alternatingGroup.1 hpA
    have hqN0 : (⟨q, hqA⟩ : ↥(alternatingGroup {i // i ∈ Δ})) ∈ N0 := by
      show ψ ⟨q, hqA⟩ ∈ Z
      show φ q ∈ Z
      rw [hqφ]; exact hp
    rw [hbot, Subgroup.mem_bot] at hqN0
    apply hp1
    rw [← hqφ]
    have : q = 1 := congrArg Subtype.val hqN0
    rw [this, map_one]
  ·
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ : ∃ x ∈ Δ, ∃ y ∈ Δ, ∃ z ∈ Δ, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
      have h3 : 2 < Δ.card := by omega
      obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 h3
      exact ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
    let c : Perm (Fin N) := swap x y * swap x z
    have hc3 : c.IsThreeCycle := isThreeCycle_swap_mul_swap_same hxy hxz hyz
    have hcΔ : ∀ i, i ∉ Δ → c i = i := by
      intro i hi
      have hix : i ≠ x := fun h => hi (h ▸ hx)
      have hiy : i ≠ y := fun h => hi (h ▸ hy)
      have hiz : i ≠ z := fun h => hi (h ▸ hz)
      simp [c, Perm.mul_apply, swap_apply_of_ne_of_ne hix hiz, swap_apply_of_ne_of_ne hix hiy]
    have hcmem : ∀ i, c i ≠ i → i ∈ Δ := fun i hi => by
      by_contra h
      exact hi (hcΔ i h)
    have hcpres : ∀ i, (fun i : Fin N => i ∈ Δ) (c i) ↔ (fun i : Fin N => i ∈ Δ) i := by
      intro i
      by_cases hi : i ∈ Δ
      · simp only [hi, iff_true]
        by_contra hci
        have h2 := hcΔ _ hci
        have h3 := c.injective (h2.trans rfl : c (c i) = c i)
        exact hci (by rw [h3]; exact hi)
      · simp only [hi, iff_false]
        intro hci
        rw [hcΔ i hi] at hci
        exact hi hci
    let q : Perm {i // i ∈ Δ} := c.subtypePerm hcpres
    have hqφ : φ q = c := Perm.ofSubtype_subtypePerm hcpres hcmem
    have hqA : q ∈ alternatingGroup {i // i ∈ Δ} := by
      rw [mem_alternatingGroup]
      have h1 : sign (φ q) = sign q := Perm.sign_ofSubtype q
      rw [← h1, hqφ]
      exact hc3.sign
    have hcZ : c ∈ Z := by
      have : (⟨q, hqA⟩ : ↥(alternatingGroup {i // i ∈ Δ})) ∈ N0 := by rw [htop]; trivial
      have h2 : ψ ⟨q, hqA⟩ ∈ Z := this
      exact hqφ ▸ h2
    obtain ⟨k, hk⟩ := hZ ⟨c, hcZ⟩
    have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← hc3.orderOf]; exact orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
    omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
