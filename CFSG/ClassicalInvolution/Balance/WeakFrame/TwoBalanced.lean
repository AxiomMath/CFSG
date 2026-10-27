module

public import CFSG.ClassicalInvolution.Balance.TwoBalancedFrame
public import CFSG.ClassicalInvolution.Balance.WeakFrame.A2

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}

theorem mem_centralizer_of_mem_weakFrame [Finite G] (Fr : WeakPreFrame F Ω E S) {a z : G}
    (ha : a ∈ E) {K : Subgroup G} (hK : K ∈ S) (hz : IsCentralInvolution K z) :
    z ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Fr.comm ha (Fr.mem_of_central hK hz)).symm

theorem oddQuotMk_centralizes_of_omegaFree_or_rankOne_weak [Finite G] (Fr : WeakPreFrame F Ω E S)
    {a z : G} (ha : a ∈ E) {K : Subgroup G} (hK : K ∈ S) (haK : a ∈ axisSub E K)
    (hz : IsCentralInvolution K z) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨z, mem_centralizer_of_mem_weakFrame Fr ha hK hz⟩ * y =
      y * oddQuotMk a ⟨z, mem_centralizer_of_mem_weakFrame Fr ha hK hz⟩ := by
  have hKC := le_centralizer_of_mem_axisSub haK
  have hKΩ : K ∈ Ω := Fr.subset hK
  have hzmem : oddQuotMk a ⟨z, mem_centralizer_of_mem_weakFrame Fr ha hK hz⟩ ∈ modOdd a K :=
    oddQuotMk_mem_modOdd hz.mem _
  rcases hL with hL | ⟨-, hL⟩
  · exact hL K hKΩ hKC _ hzmem y hy
  · rcases hL K hKΩ hKC with h | h
    · rw [← h] at hy
      obtain ⟨k, hkK, rfl⟩ := hy
      have hkK' : (k : G) ∈ K := hkK
      have hzk : z * (k : G) = (k : G) * z := hz.central k hkK'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext hzk)
    · exact h _ hzmem y hy

theorem oddQuotMk_centralizes_of_mem_weakZClosure [Finite G] (Fr : WeakPreFrame F Ω E S) {a : G}
    (ha : a ∈ E) {L : Subgroup (OddQuot a)} (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) {f : G}
    (hf : f ∈ weakZClosure E S a) (hfC : f ∈ Subgroup.centralizer ({a} : Set G)) (y : OddQuot a)
    (hy : y ∈ L) : oddQuotMk a ⟨f, hfC⟩ * y = y * oddQuotMk a ⟨f, hfC⟩ := by
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : weakZClosure E S a ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨K, ⟨hK, haK⟩, hz⟩
    refine ⟨⟨z, mem_centralizer_of_mem_weakFrame Fr ha hK hz⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (oddQuotMk_centralizes_of_omegaFree_or_rankOne_weak Fr ha hK haK hz hL y hy).symm
  obtain ⟨q, hq, hqf⟩ := hsub hf
  have hqe : q = ⟨f, hfC⟩ := Subtype.ext hqf
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm

private theorem exists_two_ne_one' {F₀ : Subgroup G} (h4 : Nat.card F₀ = 4) :
    ∃ x ∈ F₀, ∃ y ∈ F₀, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F₀ := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F₀
  have hc : 2 < Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha1.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha1.trans (Subtype.ext h).symm)
  · by_cases hb1 : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h), ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (hb1.trans (Subtype.ext h).symm)
    · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

theorem exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne_weak [Finite G]
    (Fr : WeakToralFrame F Ω E S) {a : G} (ha : a ∈ E) {F₀ : Subgroup G} (hF₀ : F₀ ≤ E)
    (h4 : Nat.card F₀ = 4) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) :
    ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f := by
  have finish : ∀ f ∈ F₀, f ≠ 1 → f ∈ weakZClosure E S a →
      ∃ f' ∈ modOdd a F₀, f' ≠ 1 ∧ ∀ y ∈ L, f' * y = y * f' := by
    intro f hfF hf1 hfA
    have hfE : f ∈ E := hF₀ hfF
    have hfC : f ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Fr.comm ha hfE).symm
    refine ⟨oddQuotMk a ⟨f, hfC⟩, oddQuotMk_mem_modOdd hfF hfC, ?_, fun y hy =>
      oddQuotMk_centralizes_of_mem_weakZClosure Fr.toWeakPreFrame ha hL hfA hfC y hy⟩
    intro h
    have hsq : (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) *
        ⟨f, hfC⟩ = 1 := Subtype.ext (Fr.elem f hfE)
    exact hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one' h4
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxy
    have hyy : y * y = 1 := Fr.elem y (hF₀ hy)
    calc x = x * (y * y) := by rw [hyy, mul_one]
      _ = (x * y) * y := (mul_assoc _ _ _).symm
      _ = y := by rw [h, one_mul]
  rcases mem_or_mem_or_mul_mem_weakZClosure Fr ha (hF₀ hx) (hF₀ hy) with h | h | h
  · exact finish x hx hx1 h
  · exact finish y hy hy1 h
  · exact finish (x * y) (F₀.mul_mem hx hy) hxy1 h

theorem twoBalancedWrt_of_weakFrame [Finite G] (Fr : WeakToralFrame F Ω E S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a) : TwoBalancedWrt E := by
  have hcomm := weak_isMulCommutative Fr.toWeakPreFrame
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hcomm ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Fr.comm ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => Fr.elem f (hF₀E hf)
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_locallyTwoBalanced (pPrimeCore_oddQuot_eq_bot a) ?_ ?_ ?_
  · rw [card_modOdd_of_exponent_two hFC hF2, h4]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  · intro L hL _ hfaith
    rcases hloc a ha ha1 L hL with h | h | h
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne_weak Fr ha hF₀E h4 (Or.inl h)
      exact absurd hfc (hfaith f hf hf1)
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne_weak Fr ha hF₀E h4 (Or.inr h)
      exact absurd hfc (hfaith f hf hf1)
    · exact h

theorem twoBalancedWrt_of_weakFrame_of_a2Dichotomy [Finite G] (Fr : WeakPreFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : WeakFibreLE2 S) (hnc : NonCommConnected S)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a) : TwoBalancedWrt E :=
  twoBalancedWrt_of_weakFrame (Fr.toFrame hA2 hfib hnc) hloc

section Triviality

variable {G : Type} [Group G] [Finite G]
variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem deltaCore_eq_bot_of_weakFrame (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E) :
    ∀ F₀ ∈ signalizerFunctorEk 2 2 E, deltaCore F₀ = ⊥ :=
  deltaCore_eq_bot_of_fusionGenerated
    ⟨weak_isMulCommutative Fr.toWeakPreFrame, fun x hx => by rw [pow_two]; exact Fr.elem x hx⟩
    h16 (twoBalancedWrt_of_weakFrame Fr hloc) hO hGen

theorem deltaCore_eq_bot_of_weakFrame_of_a2Dichotomy (Fr : WeakPreFrame F Ω E S)
    (hA2 : A2Dichotomy E S) (hfib : WeakFibreLE2 S) (hnc : NonCommConnected S)
    (h16 : 16 ≤ Nat.card E) (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E) :
    ∀ F₀ ∈ signalizerFunctorEk 2 2 E, deltaCore F₀ = ⊥ :=
  deltaCore_eq_bot_of_weakFrame (Fr.toFrame hA2 hfib hnc) h16 hloc hO hGen

end Triviality

end CFSG.ClassicalInvolution.Balance
