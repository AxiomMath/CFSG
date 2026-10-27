module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem center_eq_bot_of_card_six {R : Type*} [Group R] (h6 : Nat.card R = 6)
    (hnc : ¬ ∀ a b : R, a * b = b * a) : Subgroup.center R = ⊥ := by
  haveI : Finite R := Nat.finite_of_card_ne_zero (by omega)
  by_contra hne
  have hZ1 : Nat.card (Subgroup.center R) ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have hmul := Subgroup.card_mul_index (Subgroup.center R)
  rw [h6] at hmul
  have hZ2 : 2 ≤ Nat.card (Subgroup.center R) := by
    have := Nat.card_pos (α := Subgroup.center R)
    omega
  have hidx3 : (Subgroup.center R).index ≤ 3 := by nlinarith
  have hidxpos : 0 < (Subgroup.center R).index := by
    rcases Nat.eq_zero_or_pos (Subgroup.center R).index with h | h
    · rw [h] at hmul; omega
    · exact h
  apply hnc
  rcases (by omega : (Subgroup.center R).index = 1 ∨ (Subgroup.center R).index = 2 ∨
      (Subgroup.center R).index = 3) with h | h | h
  · have htop : Subgroup.center R = ⊤ := Subgroup.index_eq_one.1 h
    intro a b
    have ha : a ∈ Subgroup.center R := by rw [htop]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic (R ⧸ Subgroup.center R) :=
      isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, h])
    have hc := (QuotientGroup.mk' (Subgroup.center R)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])
    exact hc.is_comm.comm
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic (R ⧸ Subgroup.center R) :=
      isCyclic_of_prime_card (p := 3) (by rw [← Subgroup.index_eq_card, h])
    have hc := (QuotientGroup.mk' (Subgroup.center R)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])
    exact hc.is_comm.comm

theorem pPrimeCore_eq_bot_of_card_six {R : Type*} [Group R] (h6 : Nat.card R = 6)
    (hnc : ¬ ∀ a b : R, a * b = b * a) : CFSG.pPrimeCore 3 R = ⊥ := by
  haveI : Finite R := Nat.finite_of_card_ne_zero (by omega)
  have hZ := center_eq_bot_of_card_six h6 hnc
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hdvd : Nat.card N ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card N
  have hN12 : Nat.card N = 1 ∨ Nat.card N = 2 := by
    have h1 : Nat.card N ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have h2 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [h2] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso; rw [h] at hcop; exact absurd hcop (by decide)
    · exfalso; rw [h] at hcop; exact absurd hcop (by decide)
  rcases hN12 with h1 | h2
  · exact Subgroup.card_eq_one.1 h1
  · rw [eq_bot_iff, ← hZ]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    by_cases hx1 : x = 1
    · rw [hx1]; simp
    · obtain ⟨y₀, -, hy₀⟩ := (Nat.card_eq_two_iff' (1 : ↥N)).1 h2
      have hconj : g * x * g⁻¹ ∈ N := hN.conj_mem x hx g
      have h3 : (⟨x, hx⟩ : ↥N) = y₀ := hy₀ _ (fun h => hx1 (congrArg Subtype.val h))
      have h4 : (⟨g * x * g⁻¹, hconj⟩ : ↥N) = y₀ := hy₀ _ (fun h => by
        have := congrArg Subtype.val h
        apply hx1
        have h5 : g * x * g⁻¹ = 1 := this
        simpa using h5)
      have h5 : g * x * g⁻¹ = x := congrArg Subtype.val (h4.trans h3.symm)
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [h5]

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
