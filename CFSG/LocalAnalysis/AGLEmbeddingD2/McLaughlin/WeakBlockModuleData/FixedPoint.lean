module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_one_of_odd_orderOf_of_conj {g y c : G} (hc2 : c ^ 2 = 1) (hgc : g * c * g⁻¹ = c)
    (hgy : g * y * g⁻¹ = c * y) (hodd : Odd (orderOf g)) : c = 1 := by
  have key : ∀ k : ℕ, g ^ k * y * (g ^ k)⁻¹ = c ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : g ^ (k + 1) * y * (g ^ (k + 1))⁻¹ = g * (g ^ k * y * (g ^ k)⁻¹) * g⁻¹ := by
        group
      rw [h1, ih]
      have h2 : g * (c ^ k * y) * g⁻¹ = (g * c ^ k * g⁻¹) * (g * y * g⁻¹) := by group
      rw [h2, hgy, ← conj_pow, hgc]
      group
  have h3 := key (orderOf g)
  rw [pow_orderOf_eq_one] at h3
  simp only [one_mul, inv_one, mul_one] at h3
  have h4 : c ^ orderOf g = 1 := by
    have : c ^ orderOf g * y = 1 * y := by rw [← h3]; simp
    simpa using this
  obtain ⟨m, hm⟩ := hodd
  rw [hm, pow_succ, pow_mul, hc2, one_pow, one_mul] at h4
  exact h4

theorem mem_centralizer_of_comm_mem_centralizer {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1) {y g : G}
    (hy : y ∈ V) (hg : g ∈ L) (hodd : Odd (orderOf g))
    (hfix : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    g ∈ Subgroup.centralizer ({y} : Set G) := by
  set c := g * y * g⁻¹ * y⁻¹ with hc
  have hgyV : g * y * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hg) y).mp hy
  have hcV : c ∈ V := V.mul_mem hgyV (V.inv_mem hy)
  have hgc : g * c * g⁻¹ = c := by
    have := Subgroup.mem_centralizer_iff.mp hfix g hg
    calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [this]
      _ = c := by group
  have hgy : g * y * g⁻¹ = c * y := by rw [hc]; group
  have h1 : c = 1 := eq_one_of_odd_orderOf_of_conj (hV2 c hcV) hgc hgy hodd
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : g * y * g⁻¹ = y := by rw [hgy, h1, one_mul]
  calc g * y = g * y * g⁻¹ * g := by group
    _ = y * g := by rw [this]

theorem three_dvd_card_inf_centralizer_of_comm_mem_centralizer [Finite G] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1) {y g : G}
    (hy : y ∈ V) (hg : g ∈ L) {k : ℕ} (hk : orderOf g = 3 ^ (k + 1))
    (hfix : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  have hodd : Odd (orderOf g) := by rw [hk]; exact Odd.pow (by decide)
  have hgC := mem_centralizer_of_comm_mem_centralizer hLV hV2 hy hg hodd hfix
  have hle : Subgroup.zpowers g ≤ L ⊓ Subgroup.centralizer ({y} : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hg, hgC⟩
  have h1 : 3 ^ (k + 1) ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
    rw [← hk, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  exact (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans h1

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
