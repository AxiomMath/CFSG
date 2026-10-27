module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MBender
public import CFSG.GH74.KGroups.CoverEven

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
  CFSG.ComponentClassification.Asc76X CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem noN1_U34 {Y : Type} [Group Y]
    (hY : LieModel Y .PSU 3 2 2) {p : ℕ} {b : MulAut Y} {R₀ : Subgroup Y} :
    ¬ N1Config Y p b R₀ := by
  intro h
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (S := Y) (f := 2) le_rfl hY
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hsimple : IsSimpleGroup (CFSG.Open.PSU3 2 2) :=
    CFSG.ShultStronglyClosedTI.unitaryCover_native_simple 2 le_rfl
  have : IsSimpleGroup Y := MulEquiv.isSimpleGroup e
  have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [CFSG.Open.PSU3, CFSG.Theory.Comparator.PSU3Model]
  have hBT : BenderType Y 2 3 5 := by
    have := BenderType.unitary 2 le_rfl (e.trans (MulEquiv.subgroupCongr hmodel.symm))
    norm_num at this
    exact this
  have hO : Nat.card (Outer Y) = 4 := by
    obtain ⟨Dd, -, -, hd, -, hq⟩ := hBT.outer_unitary
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
    rw [hq, hd] at h1
    norm_num at h1
    exact h1
  have hp : p.Prime := h.1
  have hp2 : p ≠ 2 := h.2.1
  have hbo : orderOf b = p := h.2.2.1
  have hb : b ∈ innSub Y := by
    refine mem_innSub_of_pow_coprime (n := p) (hbo ▸ pow_orderOf_eq_one b) ?_
    rw [hO, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  exact noN1_of_bender_inner (fusionBenderBorel_of_mulEquiv_psu3 le_rfl e)
    (by norm_num) (by norm_num) (isBenderGroup_of_mulEquiv_psu3 le_rfl e)
    (card_sylow_of_mulEquiv_psu3 le_rfl e) hb h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
