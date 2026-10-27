module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup

section KerTwo

variable {G B : Type*} [Group G] [Group B]

@[expose] def KerTwo (u : G) (π : ↥(centralizer ({u} : Set G)) →* B) : Prop :=
  ∀ g h : ↥(centralizer ({u} : Set G)), π g = π h → (h : G) = g ∨ (h : G) = u * g

variable {u : G} {π : ↥(centralizer ({u} : Set G)) →* B}

theorem KerTwo.eq_one_or_eq (hπ : KerTwo u π) {g : ↥(centralizer ({u} : Set G))} (h : π g = 1) :
    (g : G) = 1 ∨ (g : G) = u := by
  have := hπ 1 g (by rw [h, map_one])
  simpa using this

theorem KerTwo.orderOf_eq_prime (hπ : KerTwo u π) (hu : u * u = 1) (hu1 : u ≠ 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {g : G} (hg : g ∈ centralizer ({u} : Set G))
    (hgo : orderOf g = p) : orderOf (π ⟨g, hg⟩) = p := by
  have hg' : orderOf (⟨g, hg⟩ : ↥(centralizer ({u} : Set G))) = p := by
    rw [Subgroup.orderOf_mk, hgo]
  have hpow : (π ⟨g, hg⟩) ^ p = 1 := by
    rw [← map_pow, ← hg', pow_orderOf_eq_one, map_one]
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow) with h | h
  · exfalso
    have h1 : π ⟨g, hg⟩ = 1 := orderOf_eq_one_iff.1 h
    rcases hπ.eq_one_or_eq h1 with h2 | h2
    · have h2' : g = 1 := h2
      rw [h2', orderOf_one] at hgo
      exact hp.one_lt.ne hgo
    · have h2' : g = u := h2
      have hu2 : orderOf u = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact _root_.orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
      rw [h2', hu2] at hgo
      exact hp2 hgo.symm
  · exact h

theorem KerTwo.orderOf_eq_two (hπ : KerTwo u π) {w : G} (hw : w ∈ centralizer ({u} : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwu : w ≠ u) : orderOf (π ⟨w, hw⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine _root_.orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← map_mul]
    have : (⟨w, hw⟩ : ↥(centralizer ({u} : Set G))) * ⟨w, hw⟩ = 1 := Subtype.ext hw2
    rw [this, map_one]
  · intro h
    rcases hπ.eq_one_or_eq h with h2 | h2
    · exact hw1 h2
    · exact hwu h2

variable [Finite G] [Finite B]

theorem KerTwo.card_ker_le (hu1 : u ≠ 1) (hπ : KerTwo u π) {K : Subgroup G}
    (hK : K ≤ centralizer ({u} : Set G)) :
    Nat.card (π.comp (Subgroup.inclusion hK)).ker ≤ 2 := by
  classical
  have hinj : Function.Injective
      (fun g : (π.comp (Subgroup.inclusion hK)).ker => decide ((g.1.1 : G) = u)) := by
    intro g h hgh
    have hg1 : π ⟨g.1.1, hK g.1.2⟩ = 1 := g.2
    have hh1 : π ⟨h.1.1, hK h.1.2⟩ = 1 := h.2
    have hg : (g.1.1 : G) = 1 ∨ (g.1.1 : G) = u := hπ.eq_one_or_eq hg1
    have hh : (h.1.1 : G) = 1 ∨ (h.1.1 : G) = u := hπ.eq_one_or_eq hh1
    have hgh' : ((g.1.1 : G) = u) ↔ ((h.1.1 : G) = u) := by simpa using hgh
    apply Subtype.ext
    apply Subtype.ext
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · rw [hg, hh]
    · exfalso
      have h1 : (g.1.1 : G) = u := hgh'.2 hh
      exact hu1 (by rw [← h1, hg])
    · exfalso
      have h1 : (h.1.1 : G) = u := hgh'.1 hg
      exact hu1 (by rw [← h1, hh])
    · rw [hg, hh]
  calc Nat.card (π.comp (Subgroup.inclusion hK)).ker ≤ Nat.card Bool :=
        Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem KerTwo.card_le (hu1 : u ≠ 1) (hπ : KerTwo u π) {K : Subgroup G}
    (hK : K ≤ centralizer ({u} : Set G)) {C : Subgroup B}
    (hKC : ∀ k (hk : k ∈ K), π ⟨k, hK hk⟩ ∈ C) : Nat.card K ≤ 2 * Nat.card C := by
  set f := π.comp (Subgroup.inclusion hK) with hf
  have hrange : f.range ≤ C := by
    rintro _ ⟨k, rfl⟩
    exact hKC k.1 k.2
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.ker ≤ 2 := hπ.card_ker_le hu1 hK
  have h3 : Nat.card f.range ≤ Nat.card C := Subgroup.card_le_of_le hrange
  calc Nat.card K = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ 2 * Nat.card C := Nat.mul_le_mul h2 h3

theorem KerTwo.dvd_of_dvd (hu1 : u ≠ 1) (hπ : KerTwo u π) {K : Subgroup G}
    (hK : K ≤ centralizer ({u} : Set G)) {C : Subgroup B}
    (hKC : ∀ k (hk : k ∈ K), π ⟨k, hK hk⟩ ∈ C) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card K) : p ∣ Nat.card C := by
  set f := π.comp (Subgroup.inclusion hK) with hf
  have hrange : f.range ≤ C := by
    rintro _ ⟨k, rfl⟩
    exact hKC k.1 k.2
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.ker ≤ 2 := hπ.card_ker_le hu1 hK
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hndvd : ¬ p ∣ Nat.card f.ker := fun h => by
    have := Nat.le_of_dvd hpos h
    omega
  rw [← h1] at hdvd
  have hr : p ∣ Nat.card f.range := (hp.dvd_mul.1 hdvd).resolve_left hndvd
  exact hr.trans (Subgroup.card_dvd_of_le hrange)

theorem KerTwo.ncard_le_two_mul (hπ : KerTwo u π) {N : Set G}
    (hN : ∀ n ∈ N, n ∈ centralizer ({u} : Set G)) {F : Set B} (hF : F.Finite)
    (hmap : ∀ n (hn : n ∈ N), π ⟨n, hN n hn⟩ ∈ F) : N.ncard ≤ 2 * F.ncard := by
  classical
  let f : G → B := fun n => if h : n ∈ centralizer ({u} : Set G) then π ⟨n, h⟩ else 1
  have hf : ∀ n (hn : n ∈ N), f n = π ⟨n, hN n hn⟩ := fun n hn => by
    simp only [f, dif_pos (hN n hn)]
  have hNfin : N.Finite := Set.toFinite N
  have hmaps : ∀ a ∈ hNfin.toFinset, f a ∈ hF.toFinset := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha ⊢
    rw [hf a ha]
    exact hmap a ha
  have key := Finset.card_le_mul_card_image_of_maps_to hmaps 2 (by
    intro b hb
    by_cases hemp : (hNfin.toFinset.filter fun a => f a = b) = ∅
    · rw [hemp]; simp
    · obtain ⟨a₀, ha₀⟩ := Finset.nonempty_iff_ne_empty.2 hemp
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at ha₀
      calc (hNfin.toFinset.filter fun a => f a = b).card ≤ ({a₀, u * a₀} : Finset G).card := by
            apply Finset.card_le_card
            intro a ha
            rw [Finset.mem_filter, Set.Finite.mem_toFinset] at ha
            have h1 := hf a ha.1
            have h2 := hf a₀ ha₀.1
            have h3 : π ⟨a₀, hN a₀ ha₀.1⟩ = π ⟨a, hN a ha.1⟩ := by rw [← h1, ← h2, ha.2, ha₀.2]
            rcases hπ _ _ h3 with h | h
            · have h' : a = a₀ := h
              simp [h']
            · have h' : a = u * a₀ := h
              simp [h']
        _ ≤ 2 := Finset.card_le_two)
  rw [Set.ncard_eq_toFinset_card N hNfin, Set.ncard_eq_toFinset_card F hF]
  exact key

end KerTwo

end CFSG.HardMathSupport.Dickson.Sec6.I1431
