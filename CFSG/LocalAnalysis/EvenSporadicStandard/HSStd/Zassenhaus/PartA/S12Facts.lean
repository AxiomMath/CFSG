module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12Frame
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

set_option linter.unusedSectionVars false

section CardNine

variable {G : Type*} [Group G]

theorem eq_of_card_nine {X H : Subgroup G} (hX : Nat.card X = 9) (hH : H ≤ X) {y z : G}
    (hy : y ∈ H) (hyo : orderOf y = 3) (hz : z ∈ H) (hzy : z ∉ zpowers y) : H = X := by
  have hXf : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hHf : Finite H := Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
  have h1 : Nat.card H ∣ 9 := hX ▸ Subgroup.card_dvd_of_le hH
  have h3 : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, hyo]
  have h2 : 3 ∣ Nat.card H := h3 ▸ Subgroup.card_dvd_of_le (zpowers_le.2 hy)
  have h5 : Nat.card H = 3 ∨ Nat.card H = 9 := by
    have : Nat.card H ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨h1, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h] at h2; omega
    · exact Or.inl h
    · exact Or.inr h
  rcases h5 with h | h
  · exfalso
    have : zpowers y = H := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hy) (by rw [h3, h])
    exact hzy (this ▸ hz)
  · exact Subgroup.eq_of_le_of_card_ge hH (by rw [hX, h])

theorem eq_zpowers_of_card_nine {X H : Subgroup G} (hX : Nat.card X = 9) (hH : H ≤ X) {y b : G}
    (hy : y ∈ H) (hyo : orderOf y = 3) (hb : b ∈ X) (hbH : b ∉ H) : H = zpowers y := by
  have hXf : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hHf : Finite H := Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
  have h1 : Nat.card H ∣ 9 := hX ▸ Subgroup.card_dvd_of_le hH
  have h3 : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, hyo]
  have h2 : 3 ∣ Nat.card H := h3 ▸ Subgroup.card_dvd_of_le (zpowers_le.2 hy)
  have h5 : Nat.card H = 3 ∨ Nat.card H = 9 := by
    have : Nat.card H ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨h1, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h] at h2; omega
    · exact Or.inl h
    · exact Or.inr h
  rcases h5 with h | h
  · exact (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hy) (by rw [h3, h])).symm
  · exfalso
    have : H = X := Subgroup.eq_of_le_of_card_ge hH (by rw [hX, h])
    exact hbH (this ▸ hb)

end CardNine

section Frame

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

theorem PA11.frame : A6Frame a.L₁ a.X a.x where
  perf := by
    obtain ⟨-, -, -, hp, -⟩ := a.L₁_comp
    exact hp
  x_mem := a.X_three a.x (Subgroup.mem_inf.2 ⟨a.x_mem, mem_Cen.2 rfl⟩) a.x_ord
  X_le := a.X_le
  X_card := a.X_card
  X_Z := by
    intro g hg hgX hz
    have h1 := a.Z_le (Subgroup.mem_map.2 ⟨⟨g, hg⟩, hz, rfl⟩)
    have h2 : orderOf g ∣ Nat.card a.X := Subgroup.orderOf_dvd_natCard a.X hgX
    have h3 : orderOf g ∣ orderOf a.ub := orderOf_dvd_of_mem_zpowers h1
    rw [a.X_card] at h2
    rw [a.ub_ord] at h3
    have h4 : orderOf g ∣ Nat.gcd 9 2 := Nat.dvd_gcd h2 h3
    have h5 : orderOf g = 1 := by simpa using h4
    exact orderOf_eq_one_iff.1 h5
  x_ord := a.x_ord
  quot := a.L₁_A6

theorem PA11.not_central (h : ∀ g ∈ a.L₁, g * a.x = a.x * g) : False := by
  have hz : (⟨a.x, a.x_mem⟩ : ↥a.L₁) ∈ center ↥a.L₁ := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (h g g.2)
  have h1 := a.frame.X_Z a.x a.x_mem a.frame.x_mem hz
  have h2 := a.x_ord
  rw [h1, orderOf_one] at h2
  omega

theorem PA11.x_ne_xt : a.x ≠ t * a.x * t⁻¹ := by
  intro h
  apply a.not_central
  intro g hg
  have := (a.L₁_comm g hg a.x a.x_mem).eq
  rw [← h] at this
  exact this

theorem PA11.x_not_mem_conj : a.x ∉ conjSub t a.L₁ := by
  intro h
  obtain ⟨l, hl, hlx⟩ := mem_conjSub.1 h
  apply a.not_central
  intro g hg
  have := (a.L₁_comm g hg l hl).eq
  rw [hlx] at this
  exact this

theorem PA11.X_inf_Xt {g : G} (hg : g ∈ a.X) (hgt : g ∈ conjSub t a.X) : g = 1 := by
  have hgL : g ∈ a.L₁ := a.frame.X_mem_N hg
  obtain ⟨b, hb, rfl⟩ := mem_conjSub.1 hgt
  have hbL : b ∈ a.L₁ := a.frame.X_mem_N hb
  have hz : (⟨t * b * t⁻¹, hgL⟩ : ↥a.L₁) ∈ center ↥a.L₁ := by
    rw [mem_center_iff]
    intro h
    exact Subtype.ext (a.L₁_comm h h.2 b hbL).eq
  exact a.frame.X_Z _ hgL hg hz

end Frame

section Normalizer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA11 L t E z)

include hb in
theorem PA11.mem_normalizer_L₁ {p : G} (hp : p ∈ Cen a.ub) (hpx : p * a.x = a.x * p) :
    p ∈ normalizer (a.L₁ : Set G) := by
  have pd := PA8.pairData hb a.toPA10.toPA9.toPA8
  rcases pd.perm p hp with h | h
  · exact (mem_normalizer_iff_map_eq a.L₁ p).2 h
  · exfalso
    apply a.x_not_mem_conj
    have hmem : p * a.x * p⁻¹ ∈ a.L₁.map (MulAut.conj p).toMonoidHom := ⟨a.x, a.x_mem, rfl⟩
    rw [h] at hmem
    rwa [hpx, mul_inv_cancel_right] at hmem

end Normalizer

section Frame2

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

theorem PA11.conj_mem_X {p : G} (hpN : p ∈ normalizer (a.L₁ : Set G)) (hpx : p * a.x = a.x * p)
    {b : G} (hb : b ∈ a.X) : p * b * p⁻¹ ∈ a.X := by
  by_cases h1 : b = 1
  · subst h1
    simp only [mul_one, mul_inv_cancel]
    exact one_mem _
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : orderOf b = 3 := orderOf_eq_prime (a.frame.exp_three hb) h1
    refine a.X_three _ (Subgroup.mem_inf.2 ⟨?_, mem_Cen.2 ?_⟩) (by rw [orderOf_conj_eq, h3])
    · exact (mem_normalizer_iff.1 hpN b).1 (a.frame.X_mem_N hb)
    · have hpx' : Commute p a.x := hpx
      have hbx : Commute b a.x := a.frame.X_comm hb
      exact ((hpx'.mul_left hbx).mul_left hpx'.inv_left).eq

end Frame2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
