module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SubfieldMaximalSL2Three
public import CFSG.LocalAnalysis.SubfieldPairReeG2.FixedSubgroupData
public import CFSG.LocalAnalysis.SubfieldPairReeG2.PairAssembly
public import CFSG.LocalAnalysis.SubfieldPairReeG2.PsiFieldAut
public import CFSG.LocalAnalysis.SubfieldPairReeG2.SL2MaxPrime

public section

open CFSG CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Seitz.TrialityOdd.Proving (sl2Range)
open CFSG.Walter.Ree.Model (smallReeH smallReeU smallReeH_neg_one_mem_reeGamma)

namespace CFSG.LocalAnalysis.SubfieldPairReeG2

section Dichotomy


theorem sl2Range_dichotomy_three {F K : Type} [Field F] [Field K]
    [Algebra F K] [Finite F] [Finite K] (hdeg : Module.finrank F K = 3) (hK : ringChar K ≠ 2)
    (hF : 5 ≤ Nat.card F ∨ Nat.card F = 3)
    (M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (hM : sl2Range F K ≤ M) :
    M = sl2Range F K ∨ M = ⊤ := by
  by_cases hle : M ≤ sl2Range F K
  · exact Or.inl (le_antisymm hle hM)
  · right
    obtain ⟨j, hjM, hjn⟩ := Set.not_subset.1 hle
    rcases hF with h5 | h3
    · exact sl2_range_maximal_prime Nat.prime_three (by norm_num) hdeg hK (Or.inl h5) M hM hjM hjn
    · exact CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.sl2_range_maximal_of_card_three hdeg h3
        M hM hjM hjn

end Dichotomy

section Final


theorem subfieldPairReeG2_three {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {β : K ≃+* K} (hβ : orderOf β = 3)
    (g : G2.reeGamma K a)
    (hne : (fixedSubgroup (G2.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
      fixedSubgroup (G2.reeGammaFieldAut K a β)) :
    Subgroup.closure ((fixedSubgroup (G2.reeGammaFieldAut K a β) : Set (G2.reeGamma K a)) ∪
      ((fixedSubgroup (G2.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
        Set (G2.reeGamma K a))) = ⊤ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨ψ, huψ, hwψ, -, hker, -, hIDP, -, hψs, hψnc⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.ree_socle_psi_structure ha hK
  set t : G2.reeGamma K a := ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ with ht
  have ht2 : orderOf t = 2 := CFSG.Walter.Ree.Model.orderOf_smallReeH_neg_one hK
  have htR := torusInvolution_mem_fixedSubgroup hK β
  have hequiv := reeGammaFieldAut_psi hK huψ hwψ
  have hψR := fun x => psi_mem_fixedSubgroup_iff hker hequiv hp hp2 hβ x
  obtain ⟨b, hbp, hk, hchar, -⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK hp hp2 hβ
  have hdeg : Module.finrank (fixSubfield β) K = 3 := by
    have h1 := Module.natCard_eq_pow_finrank (K := fixSubfield β) (V := K)
    rw [hK, hk] at h1
    have h2 : (3 ^ (2 * b + 1)) ^ 3 = (3 ^ (2 * b + 1)) ^ Module.finrank (fixSubfield β) K := by
      rw [← pow_mul, hbp]; exact h1
    have h3 : 2 ≤ 3 ^ (2 * b + 1) :=
      le_trans (by norm_num)
        (Nat.pow_le_pow_right (by norm_num : 0 < 3) (Nat.le_add_left 1 (2 * b)))
    exact (Nat.pow_right_injective h3 h2).symm
  have hK2 : ringChar K ≠ 2 := by
    have h3 : ringChar K = G2.prime := ringChar.eq K G2.prime
    rw [h3]; decide
  have hF : 5 ≤ Nat.card (fixSubfield β) ∨ Nat.card (fixSubfield β) = 3 := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · right; subst hb; simpa using hk
    · left; rw [hk]
      calc 5 ≤ 3 ^ 1 * 3 := by norm_num
        _ ≤ 3 ^ (2 * b + 1) := by
          calc 3 ^ 1 * 3 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdich : ∀ M : Subgroup (SL2 K), sl2Range (fixSubfield β) K ≤ M →
      M = sl2Range (fixSubfield β) K ∨ M = ⊤ :=
    fun M hM => sl2Range_dichotomy_three hdeg hK2 hF M hM
  obtain ⟨S, hSR⟩ := exists_sylow_two_le_fixedSubgroup hK hp hp2 hβ
  obtain ⟨E, hER, hE4, hE2⟩ := exists_kleinFour_le_fixedSubgroup hK hp hp2 hβ
  obtain ⟨W, hWR, hWs, hWnc, hWinv⟩ := exists_simple_le_fixedSubgroup hK hp hp2 hβ
  have := pair_closure_eq_top (A := SL2 K) _ g hne htR ht2
    (fixedSubgroup_involution_conj hK hp hp2 hβ htR ht2) S hSR hER hE4 hE2 hWR hWs hWnc hWinv
    ψ (sl2Range (fixSubfield β) K) hdich hψR
    (fun x hx => by
      obtain ⟨_, ⟨y, rfl⟩, h⟩ := exists_mul_of_internalDirectProduct ht2 hIDP hx
      exact ⟨y, h⟩)
    hψs hψnc (exists_involution_range_psi ψ hker)
  exact this

end Final

end CFSG.LocalAnalysis.SubfieldPairReeG2
