module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsBalanceCop

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Assembly


variable {K : Type} [Field K] [Finite K]

theorem innerOneBalanceThree_E6_four_of_fusion
    (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3)
    (hfus : ∀ {s : ModGL Tag.E6 K}, s ∈ adjointGroup Tag.E6 K → s ^ 3 = 1 →
      ∃ c ∈ adjointGroup Tag.E6 K, ∃ y : Fin 5 → ZMod 3,
        c * s * c⁻¹ = (dE6 (pow_three_of_orderOf hω) y : ModGL Tag.E6 K)) :
    InnerOneBalanceThree (adjointGroup Tag.E6 K) := by
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  refine innerOneBalanceThree_of_toral_coprime
    (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K))
    {t | ∃ y : Fin 5 → ZMod 3, y ≠ 0 ∧ t = dE6 (pow_three_of_orderOf hω) y} ?_ ?_ ?_
  · intro s hs3 hs1
    obtain ⟨c, hc, y, hcy⟩ := hfus s.2 (by
      have := congrArg Subtype.val hs3
      simpa using this)
    refine ⟨⟨c, hc⟩, y, ?_, Subtype.ext hcy⟩
    rintro rfl
    apply hs1
    apply Subtype.ext
    have h := hcy
    rw [coe_dE6, subLin_zero, dV_zero] at h
    change (s : ModGL Tag.E6 K) = 1
    calc (s : ModGL Tag.E6 K) = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · rintro _ ⟨y, hy, rfl⟩
    exact gLAPPrimeCoreOf_centralizer_dS_E6_four hK hω hy
  · rintro _ ⟨y, hy, rfl⟩ α hα3 hα
    exact mem_innerAut_of_fix_E6_four hK hω hy α hα3 hα

theorem innerOneBalanceThree_E6_four
    (hK : Nat.card K = 4) :
    InnerOneBalanceThree (adjointGroup Tag.E6 K) := by
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [card_units_four hK])
  refine innerOneBalanceThree_E6_four_of_fusion hK hω fun hs hs3 => ?_
  obtain ⟨c, hc, y, hcy⟩ := exists_conj_dE6_four hK hω hs hs3
  exact ⟨c, hc, y, by rw [coe_dE6]; exact hcy⟩

end Assembly

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
