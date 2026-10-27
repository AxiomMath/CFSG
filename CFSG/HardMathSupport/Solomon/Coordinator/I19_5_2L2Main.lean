module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Hilb
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

open scoped MatrixGroups

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem l2op_isLocallyBalancedAbs_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) : IsLocallyBalancedAbs 3 2 SL(2, F) := by
  have hZ : Subgroup.center SL(2, F) = ⊥ := CFSG.Walter.sl2_center_eq_bot_of_charTwo
  refine l2op_isLocallyBalancedAbs_of_fix hZ fun D hD hcard9 => ?_
  have hout : ∃ f ∈ D, f ∉ innerAut SL(2, F) := by
    by_contra hcon
    push Not at hcon
    have hmap : (D.comap (MulAut.conj : SL(2, F) →* MulAut SL(2, F))).map MulAut.conj = D :=
      Subgroup.map_comap_eq_self fun f hf => hcon f hf
    have hcardE : Nat.card (D.comap (MulAut.conj : SL(2, F) →* MulAut SL(2, F))) = 9 := by
      rw [← hcard9]
      nth_rewrite 2 [← hmap]
      rw [Subgroup.card_map_of_injective (l2op_conj_injective hZ)]
    have hexp : ∀ x ∈ D.comap (MulAut.conj : SL(2, F) →* MulAut SL(2, F)), x ^ 3 = 1 := by
      intro x hx
      apply l2op_conj_injective hZ
      rw [map_pow, map_one]
      exact hD.2 _ hx
    have := l2op_card_le_three _ hexp
    omega
  obtain ⟨f, hfD, hfI⟩ := hout
  obtain ⟨σ, c, hσ, rfl⟩ := l2op_exists_conj_fieldAut f (hD.2 f hfD) hfI
  have hf1 : c * l2opFieldAutHom σ * c⁻¹ ≠ 1 := fun h => hfI (h ▸ one_mem _)
  have hσ3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨hi, hii⟩ := l2op_fix_conditions_conj c (l2opFieldAutHom σ)
    (l2op_glapPrimeCore_fix_fieldAut σ)
    (fun y hy hcop => l2op_fix_fieldAut_centralizer hn hcard σ hσ3 y hy hcop)
  exact ⟨_, hfD, hf1, hi, hii⟩

theorem l2op_statedSL_eq_range (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range :=
  CFSG.Open.StatedAPI.statedSL_eq_range_toGL n K

@[expose] noncomputable def l2opStatedSLEquiv (n : ℕ) (K : Type) [Field K] :
    ↥(StatedSL n K) ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  (MulEquiv.subgroupCongr (l2op_statedSL_eq_range n K)).trans
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem isLocallyBalancedAbs_L2OddPow : ∀ (S : Type) [Group S] [Finite S],
    CFSG.HardMathSupport.Solomon.LocalBalance.IsLTwoOddPow S →
      CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs 3 2 S := by
  intro S _ _ hS
  obtain ⟨K, _, _, n, -, hn1, hcard, ⟨e⟩⟩ := hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hcard])
  exact IsLocallyBalancedAbs.of_mulEquiv (e.trans (l2opStatedSLEquiv 2 K))
    (l2op_isLocallyBalancedAbs_sl2 (by omega) hcard)

end CFSG.HardMathSupport.Solomon.Coordinator
