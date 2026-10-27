module

public import CFSG.Goldschmidt.Basic
import CFSG.Goldschmidt.Steps.GoldType
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GClause
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

theorem psl2_odd_or_psu34_of_goldschmidtSimpleType_omega1_card_four
    {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hType : CFSG.Open.goldschmidtSimpleType K) (T : Sylow 2 K)
    (hOmega : IsMulCommutative (CFSG.Goldschmidt.Omega1 (T : Subgroup K)))
    (hOmega4 : Nat.card (CFSG.Goldschmidt.Omega1 (T : Subgroup K)) = 4) :
    (∃ (p f : ℕ) (_hp : Fact p.Prime),
      Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧
      Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f))) ∨
    Nonempty (K ≃* CFSG.Open.PSU3 2 2) := by
  obtain ⟨habel, hnonabel⟩ :=
    CFSG.Goldschmidt.N11a K hType T hOmega
  by_cases hTcomm : IsMulCommutative (T : Subgroup K)
  ·
    have hexp : ∀ t ∈ (T : Subgroup K), t ^ 2 = 1 := habel hTcomm
    have hTeq : CFSG.Goldschmidt.Omega1 (T : Subgroup K) = (T : Subgroup K) :=
      CFSG.Goldschmidt.GoldType.omega1_eq_self hexp
    have hT4 : Nat.card (T : Subgroup K) = 4 := by
      rw [← hTeq]
      exact hOmega4
    exact Or.inl (CFSG.OddStandard.SmallF3.Omega.sec5g_psl2_of_sylow_card_four hType T hT4)
  ·
    have hmodels := hnonabel hTcomm
    have hOmZ : CFSG.Goldschmidt.Omega1 (T : Subgroup K) =
        CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T : Subgroup K) :=
      (CFSG.Goldschmidt.N11c K hmodels T).1
    have hZ4 : Nat.card
        (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
          (T : Subgroup K)) = 4 := by
      rw [← hOmZ]
      exact hOmega4
    rcases hmodels with ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
    ·
      exfalso
      have hB := CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_sz hn e
      have hZcard :=
        (CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter
          hB T).2.2.1
      have h8 : 8 ≤ 2 ^ (2 * n + 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    ·
      have hB := CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e
      have hZcard :=
        (CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter
          hB T).2.2.1
      have hpow : 2 ^ f = 2 ^ 2 := by
        rw [← hZcard, hZ4]
        norm_num
      have hf2 : f = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
      subst f
      exact Or.inr ⟨e⟩

end CFSG.GH74.GLS.NT44
