module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

set_option linter.unusedSectionVars false

private theorem orderOf_eq_of_pow_eq_one_of_not_inner {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    {x : MulAut K} (hxp : x ^ p = 1) (hxo : x ∉ innerAut K) : orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hxp fun h => hxo (by rw [h]; exact one_mem _)

private theorem degCount_F4_pos_of_dvd_ordF4' {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (hpq : ¬ p ∣ q) (h : p ∣ ordF4 q) : 0 < degCount Tag.F4 (orderOf ((q : ℕ) : ZMod p)) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((q : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he]
  have key : ∀ d ∈ degreesW Tag.F4, p ∣ q ^ d - 1 → 0 < degCount Tag.F4 e := by
    intro d hd hdvd
    have hed : e ∣ d := (dvd_pow_sub_one_iff_orderOf hq he).1 hdvd
    exact List.length_pos_of_mem (List.mem_filter.2 ⟨hd, by simpa using hed⟩)
  unfold ordF4 at h
  simp only [hp.dvd_mul] at h
  rcases h with ((((h | h) | h) | h) | h)
  · exact absurd (hp.dvd_of_dvd_pow h) hpq
  · exact key 12 (by decide) h
  · exact key 8 (by decide) h
  · exact key 6 (by decide) h
  · exact key 2 (by decide) h

private theorem degCount_pos_of_dvd_two {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {e : ℕ} (he : e ∣ 2) :
    0 < degCount τ e := by
  have h2 : 2 ∈ degreesW τ := by rcases hτ with rfl | rfl <;> decide
  exact List.length_pos_of_mem (List.mem_filter.2 ⟨h2, by simpa using he⟩)

private theorem orderOf_dvd_two_of_not_three_dvd {n : ℕ} (h : ¬ 3 ∣ n) :
    orderOf ((n : ℕ) : ZMod 3) ∣ 2 := by
  have hn : ((n : ℕ) : ZMod 3) ≠ 0 := fun h0 => h ((ZMod.natCast_eq_zero_iff n 3).1 h0)
  have h2 : ((n : ℕ) : ZMod 3) ^ 2 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hn
  exact orderOf_dvd_of_pow_eq_one h2

private theorem five_le_of_degCount_zero {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {n p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hpn : ¬ p ∣ n)
    (h0 : degCount τ (orderOf ((n : ℕ) : ZMod p)) = 0) : 5 ≤ p := by
  have hne3 : p ≠ 3 := by
    rintro rfl
    exact (degCount_pos_of_dvd_two hτ (orderOf_dvd_two_of_not_three_dvd hpn)).ne' h0
  have hne4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  omega

section F4


theorem outerFields_adjointF4_odd (q : TauCeti.PrimePower) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpK : ¬ p ∣ Nat.card K) :
    OuterFields p (adjointGroup Tag.F4 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have : CharP K q.p := finite_field_prime_power_characteristic q.prime_p q.exponent_pos hK'
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K)
  by_cases hdvd : p ∣ Nat.card (adjointGroup Tag.F4 K)
  · intro D hD _ hDin
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    rw [card_adjointGroup_F4] at hdvd
    exact ⟨x, hxD, hxin, fieldCoreAt_adjointF4 q.prime_p q.exponent_pos K hK' hp (by omega)
      (degCount_F4_pos_of_dvd_ordF4' hp (Nat.card_pos (α := K)) hpK hdvd)
      (orderOf_eq_of_pow_eq_one_of_not_inner hp (hD.2 x hxD) hxin) hxin⟩
  · obtain ⟨Q, _, _, Θ, -, hker⟩ := exists_hom_cyclic_F4 q K hK
    exact outerFields_of_hom Θ hp hinj (fun x hx _ => by rw [hker] at hx; exact hx)
      (Or.inl (elemAbelian_card_eq_one_of_not_dvd hp hdvd))

end F4

section E8E7


theorem outerFields_adjointE7_odd (q : TauCeti.PrimePower) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpK : ¬ p ∣ Nat.card K) :
    OuterFields p (adjointGroup Tag.E7 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E7) (K := K)
  by_cases h0 : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0
  · have hp5 := five_le_of_degCount_zero (τ := Tag.E7) (Or.inl rfl) hp hp3 hpK h0
    obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (τ := Tag.E7) (Or.inr (Or.inl rfl)) K hp hp5
    have : IsCyclic (RingAut K) := fieldAut_isCyclic K
    exact outerFields_of_hom Θ hp hinj hΘ (Or.inl fun F hF =>
      elemAbelian_card_eq_one_of_degCount_zero (Or.inr (Or.inl rfl)) K hp (by omega) hpK rfl h0 hF)
  · intro D hD _ hDin
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    exact ⟨x, hxD, hxin, fieldCoreAt_adjointE7 q.prime_p q.exponent_pos K hK' hp (by omega)
      (Nat.pos_of_ne_zero h0) (orderOf_eq_of_pow_eq_one_of_not_inner hp (hD.2 x hxD) hxin) hxin⟩

theorem outerFields_adjointE8_odd (q : TauCeti.PrimePower) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpK : ¬ p ∣ Nat.card K) :
    OuterFields p (adjointGroup Tag.E8 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E8) (K := K)
  by_cases h0 : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0
  · have hp5 := five_le_of_degCount_zero (τ := Tag.E8) (Or.inr rfl) hp hp3 hpK h0
    obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (τ := Tag.E8) (Or.inr (Or.inr rfl)) K hp hp5
    have : IsCyclic (RingAut K) := fieldAut_isCyclic K
    exact outerFields_of_hom Θ hp hinj hΘ (Or.inl fun F hF =>
      elemAbelian_card_eq_one_of_degCount_zero (Or.inr (Or.inr rfl)) K hp (by omega) hpK rfl h0 hF)
  · intro D hD _ hDin
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    exact ⟨x, hxD, hxin, fieldCoreAt_adjointE8 q.prime_p q.exponent_pos K hK' hp
      (Nat.pos_of_ne_zero h0) (orderOf_eq_of_pow_eq_one_of_not_inner hp (hD.2 x hxD) hxin) hxin⟩

end E8E7

section E6


theorem outerFields_adjointE6_ge_five (q : TauCeti.PrimePower) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) :
    OuterFields p (adjointGroup Tag.E6 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  by_cases h0 : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0
  · obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (τ := Tag.E6) (Or.inl rfl) K hp hp5
    have : IsCyclic (RingAut K) := fieldAut_isCyclic K
    exact outerFields_of_hom Θ hp hinj hΘ (Or.inl fun F hF =>
      elemAbelian_card_eq_one_of_degCount_zero (Or.inl rfl) K hp (by omega) hpK rfl h0 hF)
  · intro D hD _ hDin
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    exact ⟨x, hxD, hxin, fieldCoreAt_adjointE6 q.prime_p q.exponent_pos K hK' hp (by omega)
      (Nat.pos_of_ne_zero h0) (orderOf_eq_of_pow_eq_one_of_not_inner hp (hD.2 x hxD) hxin) hxin⟩

end E6

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
