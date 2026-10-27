module

public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open scoped commutatorElement

theorem pow_mul_conj_of_commutator_central {G : Type*} [Group G] {g l : G}
    (hc : ⁅g, l⁆ ∈ Subgroup.center G) (m : ℕ) : g ^ m * l * (g ^ m)⁻¹ = ⁅g, l⁆ ^ m * l := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hz : ∀ y : G, ⁅g, l⁆ * y = y * ⁅g, l⁆ := fun y =>
      (Subgroup.mem_center_iff.1 hc y).symm
    calc g ^ (m + 1) * l * (g ^ (m + 1))⁻¹ = g * (g ^ m * l * (g ^ m)⁻¹) * g⁻¹ := by group
      _ = g * (⁅g, l⁆ ^ m * l) * g⁻¹ := by rw [ih]
      _ = ⁅g, l⁆ ^ m * (g * l * g⁻¹) := by
        have : g * (⁅g, l⁆ ^ m) = ⁅g, l⁆ ^ m * g :=
          (Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hc m) g)
        calc g * (⁅g, l⁆ ^ m * l) * g⁻¹ = (g * (⁅g, l⁆ ^ m)) * l * g⁻¹ := by group
          _ = ⁅g, l⁆ ^ m * g * l * g⁻¹ := by rw [this]
          _ = ⁅g, l⁆ ^ m * (g * l * g⁻¹) := by group
      _ = ⁅g, l⁆ ^ (m + 1) * l := by
        have : g * l * g⁻¹ = ⁅g, l⁆ * l := by rw [commutatorElement_def]; group
        rw [this, pow_succ, mul_assoc]

theorem mk_mem_map_of_commutator_central {G : Type*} [Group G] {J : Subgroup G} {l g : G}
    (hodd : Odd (Nat.card (Subgroup.center G)))
    (hfix : ∀ h : G, h * l = l * h → h ∈ J) (hc : ⁅g, l⁆ ∈ Subgroup.center G) {k : ℕ}
    (hk : (QuotientGroup.mk' (Subgroup.center G) g) ^ (2 ^ k) = 1) :
    QuotientGroup.mk' (Subgroup.center G) g ∈ J.map (QuotientGroup.mk' (Subgroup.center G)) := by
  set N := Nat.card (Subgroup.center G) with hN
  have hcN : ⁅g, l⁆ ^ N = 1 := by
    have h1 : (⟨⁅g, l⁆, hc⟩ : Subgroup.center G) ^ N = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hgN : g ^ N ∈ J := by
    apply hfix
    have := pow_mul_conj_of_commutator_central hc N
    rw [hcN, one_mul] at this
    calc g ^ N * l = g ^ N * l * (g ^ N)⁻¹ * g ^ N := by group
      _ = l * g ^ N := by rw [this]
  have hmemN : (QuotientGroup.mk' (Subgroup.center G) g) ^ N ∈
      J.map (QuotientGroup.mk' (Subgroup.center G)) :=
    ⟨g ^ N, hgN, by rw [map_pow]⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [pow_zero, pow_one] at hk
    rw [hk]
    exact one_mem _
  · have hcop : Nat.Coprime N (2 ^ k) := Nat.Coprime.pow_right _
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rcases hodd with ⟨m, hm⟩; omega)))
    have hcop' : Nat.Coprime N (orderOf (QuotientGroup.mk' (Subgroup.center G) g)) :=
      hcop.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
    obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop'
    rw [← hs]
    exact Subgroup.pow_mem _ hmemN s

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
