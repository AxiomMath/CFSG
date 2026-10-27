module

public import CFSG.GH74.QTGen4.Recog.Ku.Polarity
public import CFSG.GH74.QTGen4.Recog.Ku.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem mul_mem_iff_of_card_two {A W : Subgroup G} (hWA : W ≤ A) (hA : Nat.card A = 16)
    (hW : Nat.card W = 8) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b ∈ W ↔ (a ∈ W ↔ b ∈ W) := by
  have hidx : (W.subgroupOf A).index = 2 := by
    have h1 := (W.subgroupOf A).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWA).toEquiv, hW, hA] at h1
    omega
  have key : ∀ x y : A, x * y ∈ W.subgroupOf A ↔ (x ∈ W.subgroupOf A ↔ y ∈ W.subgroupOf A) := by
    intro x y
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
  simpa [Subgroup.mem_subgroupOf] using key ⟨a, ha⟩ ⟨b, hb⟩

theorem zmod2_eq_add {a b c : ZMod 2} {p q r : Prop} (ha : a = 0 ↔ p) (hb : b = 0 ↔ q)
    (hc : c = 0 ↔ r) (hr : r ↔ (p ↔ q)) : c = a + b := by
  have hv : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hv a with rfl | rfl <;> rcases hv b with rfl | rfl <;> rcases hv c with rfl | rfl <;>
    by_cases hp : p <;> by_cases hq : q <;> by_cases hrr : r <;> simp_all

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuPred_conj_conj_iff {n : G} (hn : n ∈ kuN P H) (x y : G) :
    kuPred P H z (n * x * n⁻¹) (n * y * n⁻¹) ↔ kuPred P H z x y := by
  unfold kuPred
  constructor
  · intro hp m hm hmz
    have hm' : n * m ∈ kuN P H := Subgroup.mul_mem _ hn hm
    have hnm : (n * m) * z * (n * m)⁻¹ = n * x * n⁻¹ := by
      rw [← hmz]
      group
    have := hp (n * m) hm' hnm
    have e : (n * m)⁻¹ * (n * y * n⁻¹) * (n * m) = m⁻¹ * y * m := by group
    rw [e] at this
    exact this
  · intro hq m hm hmz
    have hm' : n⁻¹ * m ∈ kuN P H := Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hm
    have hnm : (n⁻¹ * m) * z * (n⁻¹ * m)⁻¹ = x := by
      have e1 : (n⁻¹ * m) * z * (n⁻¹ * m)⁻¹ = n⁻¹ * (m * z * m⁻¹) * n := by group
      rw [e1, hmz]
      group
    have := hq (n⁻¹ * m) hm' hnm
    have e : (n⁻¹ * m)⁻¹ * y * (n⁻¹ * m) = m⁻¹ * (n * y * n⁻¹) * m := by group
    rw [e] at this
    exact this

theorem kuPolar_conj_conj {n : G} (hn : n ∈ kuN P H) (x y : G) :
    kuPolar P H z (n * x * n⁻¹) (n * y * n⁻¹) = kuPolar P H z x y := by
  unfold kuPolar
  by_cases hp : kuPred P H z x y
  · rw [if_pos hp, if_pos ((kuPred_conj_conj_iff hn x y).mpr hp)]
  · rw [if_neg hp, if_neg (fun h' => hp ((kuPred_conj_conj_iff hn x y).mp h'))]

theorem kuPred_self (h : KuHyp G T M H P z) (x : G) : kuPred P H z x x := by
  by_cases hx : ∃ n ∈ kuN P H, n * z * n⁻¹ = x
  · obtain ⟨n, hn, rfl⟩ := hx
    rw [h.kuPred_conj_iff hn]
    have e : n⁻¹ * (n * z * n⁻¹) * n = z := by group
    rw [e]
    exact h.z_mem_kuW
  · intro n hn hnz
    exact (hx ⟨n, hn, hnz⟩).elim

theorem kuPolar_self (h : KuHyp G T M H P z) (x : G) : kuPolar P H z x x = 0 := by
  unfold kuPolar
  rw [if_pos (h.kuPred_self x)]

theorem kuPolar_of_not_orbit {x : G} (hx : ¬ ∃ n ∈ kuN P H, n * z * n⁻¹ = x) (y : G) :
    kuPolar P H z x y = 0 := by
  have hp : kuPred P H z x y := by
    intro n hn hnz
    exact (hx ⟨n, hn, hnz⟩).elim
  unfold kuPolar
  rw [if_pos hp]

theorem kuPolar_conj_eq_zero_iff (h : KuHyp G T M H P z) {n₀ : G} (hn₀ : n₀ ∈ kuN P H)
    (y : G) : kuPolar P H z (n₀ * z * n₀⁻¹) y = 0 ↔ n₀⁻¹ * y * n₀ ∈ kuW P H := by
  unfold kuPolar
  by_cases hp : kuPred P H z (n₀ * z * n₀⁻¹) y
  · rw [if_pos hp]
    exact ⟨fun _ => (h.kuPred_conj_iff hn₀ y).mp hp, fun _ => rfl⟩
  · rw [if_neg hp]
    exact ⟨fun h1 => absurd h1 (by decide),
      fun hy => absurd ((h.kuPred_conj_iff hn₀ y).mpr hy) hp⟩

theorem inv_conj_mem_kuA {n₀ : G} (hn₀ : n₀ ∈ kuN P H) {y : G} (hy : y ∈ kuA P H) :
    n₀⁻¹ * y * n₀ ∈ kuA P H := by
  have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn₀) y).mp hy
  simpa using h1

theorem kuPolar_conj_mul [KuLeaf LeafCardKuA]
    (h : KuHyp G T M H P z) {n₀ : G} (hn₀ : n₀ ∈ kuN P H) {y₁ y₂ : G}
    (hy₁ : y₁ ∈ kuA P H) (hy₂ : y₂ ∈ kuA P H) :
    kuPolar P H z (n₀ * z * n₀⁻¹) (y₁ * y₂) =
      kuPolar P H z (n₀ * z * n₀⁻¹) y₁ + kuPolar P H z (n₀ * z * n₀⁻¹) y₂ := by
  have e12 : n₀⁻¹ * (y₁ * y₂) * n₀ = (n₀⁻¹ * y₁ * n₀) * (n₀⁻¹ * y₂ * n₀) := by group
  have h12 := h.kuPolar_conj_eq_zero_iff hn₀ (y₁ * y₂)
  have h1 := h.kuPolar_conj_eq_zero_iff hn₀ y₁
  have h2 := h.kuPolar_conj_eq_zero_iff hn₀ y₂
  rw [e12] at h12
  have hmul := mul_mem_iff_of_card_two h.kuW_le_kuA h.card_kuA h.card_kuW
    (inv_conj_mem_kuA hn₀ hy₁) (inv_conj_mem_kuA hn₀ hy₂)
  exact zmod2_eq_add h1 h2 (h12.trans hmul) Iff.rfl

theorem kuPolar_mul [KuLeaf LeafCardKuA]
    (h : KuHyp G T M H P z) {y₁ y₂ : G} (hy₁ : y₁ ∈ kuA P H)
    (hy₂ : y₂ ∈ kuA P H) (x : G) :
    kuPolar P H z x (y₁ * y₂) = kuPolar P H z x y₁ + kuPolar P H z x y₂ := by
  by_cases hx : ∃ n ∈ kuN P H, n * z * n⁻¹ = x
  · obtain ⟨n₀, hn₀, rfl⟩ := hx
    exact h.kuPolar_conj_mul hn₀ hy₁ hy₂
  · simp [kuPolar_of_not_orbit hx]

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
