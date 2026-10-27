module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

set_option linter.unusedSectionVars false

theorem seven_le_of_prime_of_five_lt {p : ℕ} (hp : p.Prime) (h : 5 < p) : 7 ≤ p := by
  by_contra h7
  have : p = 6 := by omega
  subst this
  exact absurd hp (by norm_num)

theorem orderOf_eq_of_pow_eq_one_of_not_mem {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    {x : MulAut K} (hxp : x ^ p = 1) (hxo : x ∉ innerAut K) : orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hxp fun h => hxo (by rw [h]; exact one_mem _)

theorem degCount_E8_ge_two {e : ℕ} (h : 2 ≤ degCount Tag.E8 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E8) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ degCount Tag.E8 e →
      e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by decide
  exact key e h30 h

theorem degCount_E7_ge_two {e : ℕ} (h : 2 ≤ degCount Tag.E7 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E7) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ degCount Tag.E7 e → e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem degCount_E6_ge_two {e : ℕ} (h : 2 ≤ degCount Tag.E6 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ degCount Tag.E6 e → e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem crossCharTwoFamCat_E8_of_planes
    (h : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) (p : ℕ), p.Prime →
      7 ≤ p → p ≠ q.p → 2 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) →
      InnerPlaneBalance p (CatT ⟨.E8 q, hv⟩)) :
    CrossCharTwoFamCat .E8 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p hp hp5 hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp7 := seven_le_of_prime_of_five_lt hp hp5
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E8) (K := K)
  have hin : InnerPlaneBalance p (adjointGroup Tag.E8 K) := by
    by_cases h2 : 2 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))
    · exact (h q hv p hp hp7 hpq h2).of_mulEquiv e.symm
    · rw [← hK] at h2
      exact innerPlaneBalance_of_rankLE1 hp hinj (rankLE1_E8 K hp hpK (by omega))
  have hout : OuterFields p (adjointGroup Tag.E8 K) := by
    obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inr rfl)) K hp (by omega)
    have : IsCyclic (RingAut K) := fieldAut_isCyclic K
    refine outerFields_of_hom Θ hp hinj hΘ ?_
    by_cases h0 : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0
    · exact Or.inl fun F hF => elemAbelian_card_eq_one_of_degCount_zero (Or.inr (Or.inr rfl)) K hp
        (by omega) hpK rfl h0 hF
    · exact Or.inr fun x hxp hxo => fieldCoreAt_adjointE8 q.prime_p q.exponent_pos K hK' hp
        (Nat.pos_of_ne_zero h0) (orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo) hxo
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin hout

theorem crossCharTwoFamCat_E8_of_classes
    (h : ∀ e ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12], InnerPlaneBalanceAt .E8 e) :
    CrossCharTwoFamCat .E8 := by
  refine crossCharTwoFamCat_E8_of_planes fun q hv p hp hp7 hpq h2 => ?_
  have := degCount_E8_ge_two h2
  rcases this with he | he | he | he | he | he | he | he | he <;>
    exact h _ (by simp) q hv p hp hp7 trivial hpq he

theorem crossCharTwoFamCat_E7_of_planes
    (h : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) (p : ℕ), p.Prime →
      7 ≤ p → p ≠ q.p → 2 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) →
      InnerPlaneBalance p (CatT ⟨.E7 q, hv⟩)) :
    CrossCharTwoFamCat .E7 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p hp hp5 hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp7 := seven_le_of_prime_of_five_lt hp hp5
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E7) (K := K)
  have hin : InnerPlaneBalance p (adjointGroup Tag.E7 K) := by
    by_cases h2 : 2 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))
    · exact (h q hv p hp hp7 hpq h2).of_mulEquiv e.symm
    · rw [← hK] at h2
      exact innerPlaneBalance_of_rankLE1 hp hinj (rankLE1_E7 K hp hpK (by omega))
  have hout : OuterFields p (adjointGroup Tag.E7 K) := by
    obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inr (Or.inl rfl)) K hp (by omega)
    have : IsCyclic (RingAut K) := fieldAut_isCyclic K
    refine outerFields_of_hom Θ hp hinj hΘ ?_
    by_cases h0 : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0
    · exact Or.inl fun F hF => elemAbelian_card_eq_one_of_degCount_zero (Or.inr (Or.inl rfl)) K hp
        (by omega) hpK rfl h0 hF
    · exact Or.inr fun x hxp hxo => fieldCoreAt_adjointE7 q.prime_p q.exponent_pos K hK' hp
        (by omega) (Nat.pos_of_ne_zero h0) (orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo) hxo
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin hout

theorem crossCharTwoFamCat_E7_of_classes
    (h : ∀ e ∈ [1, 2, 3, 4, 6], InnerPlaneBalanceAt .E7 e) : CrossCharTwoFamCat .E7 := by
  refine crossCharTwoFamCat_E7_of_planes fun q hv p hp hp7 hpq h2 => ?_
  have := degCount_E7_ge_two h2
  rcases this with he | he | he | he | he <;>
    exact h _ (by simp) q hv p hp hp7 trivial hpq he

theorem crossCharTwoFamCat_E6_of_planes
    (h : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (p : ℕ), p.Prime →
      7 ≤ p → p ≠ q.p → 2 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) →
      InnerPlaneBalance p (CatT ⟨.E6 q, hv⟩)) :
    CrossCharTwoFamCat .E6 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p hp hp5 hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp7 := seven_le_of_prime_of_five_lt hp hp5
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  have hin : InnerPlaneBalance p (adjointGroup Tag.E6 K) := by
    by_cases h2 : 2 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))
    · exact (h q hv p hp hp7 hpq h2).of_mulEquiv e.symm
    · rw [← hK] at h2
      exact innerPlaneBalance_of_rankLE1 hp hinj (rankLE1_E6 K hp hpK (by omega))
  have hout : OuterFields p (adjointGroup Tag.E6 K) := by
    obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E (Or.inl rfl) K hp (by omega)
    have : IsCyclic (RingAut K) := fieldAut_isCyclic K
    refine outerFields_of_hom Θ hp hinj hΘ ?_
    by_cases h0 : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0
    · exact Or.inl fun F hF => elemAbelian_card_eq_one_of_degCount_zero (Or.inl rfl) K hp
        (by omega) hpK rfl h0 hF
    · exact Or.inr fun x hxp hxo => fieldCoreAt_adjointE6 q.prime_p q.exponent_pos K hK' hp
        (by omega) (Nat.pos_of_ne_zero h0) (orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo) hxo
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin hout

theorem crossCharTwoFamCat_E6_of_classes
    (h : ∀ e ∈ [1, 2, 3, 4, 6], InnerPlaneBalanceAt .E6 e) : CrossCharTwoFamCat .E6 := by
  refine crossCharTwoFamCat_E6_of_planes fun q hv p hp hp7 hpq h2 => ?_
  have := degCount_E6_ge_two h2
  rcases this with he | he | he | he | he <;>
    exact h _ (by simp) q hv p hp hp7 trivial hpq he

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
