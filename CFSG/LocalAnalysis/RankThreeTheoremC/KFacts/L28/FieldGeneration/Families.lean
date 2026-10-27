module

public import CFSG.LieType.SeitzGeneration.OuterLinearTwo
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFieldAut
public import CFSG.RankThree.PartTwo.Sec4.E27.FieldAutSUOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.FieldGeneration

open CFSG.RankThree.PartOne.CTP TauCeti

theorem three_ne_p_of_mod {q : PrimePower} (hq : q.card % 3 ≠ 0) : 3 ≠ q.p := by
  intro h
  apply hq
  rw [PrimePower.card_def, ← h]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 q.exponent_pos.ne')

section Families


theorem fieldAutData_three_A1 {K : Type} [Group K] {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid) (hq8 : q.card ≠ 8)
    (e : K ≃* (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : FieldAutData K 3 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let F := GaloisField q.p q.exponent
  let e' : K ≃* CFSG.GorensteinWalter.PSL2 F :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  refine FieldAutData.of_mulEquiv e' Nat.prime_three ?_
  have hchar : ringChar F = q.p := ringChar.eq F q.p
  have hcard : Nat.card F = q.card := by
    rw [PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  by_cases h2 : q.p = 2
  · exact CFSG.LieType.SeitzGeneration.fieldAutData_psl2_even_odd_prime Nat.prime_three
      (by norm_num) (fun h => hq8 (hcard ▸ h.2)) (by rw [hchar, h2])
  · exact CFSG.LieType.SeitzGeneration.fieldAutData_psl2_odd_prime Nat.prime_three
      (by norm_num) (by rw [hchar]; exact h2)

theorem fieldAutData_three_A2 {K : Type} [Group K] {q : PrimePower}
    (hv : (LieTypeIndex.A 2 q).Valid) (hq : q.card % 3 = 2)
    (e : K ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) : FieldAutData K 3 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let F := GaloisField q.p q.exponent
  let e' : K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  refine FieldAutData.of_mulEquiv e' Nat.prime_three ?_
  have hcard : Nat.card F = q.p ^ q.exponent := GaloisField.card q.p q.exponent q.exponent_pos.ne'
  refine CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.fieldAutData_projectiveSL_of_cop
    le_rfl Nat.prime_three (by norm_num) q.prime_p (three_ne_p_of_mod (by omega))
    q.exponent_pos hcard ?_
  rw [hcard, ← PrimePower.card_def]
  refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem fieldAutData_three_twistedA2 {K : Type} [Group K] {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.card % 3 = 1)
    (e : K ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) : FieldAutData K 3 := by
  obtain ⟨-, -, -, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e)
  refine FieldAutData.of_mulEquiv θ Nat.prime_three ?_
  have hg : ¬ 3 ∣ Nat.gcd (2 + 1) (q.p ^ q.exponent + 1) := by
    intro h
    have h' := h.trans (Nat.gcd_dvd_right _ _)
    rw [← PrimePower.card_def] at h'
    omega
  refine CFSG.RankThree.PartTwo.Sec4.E27.fieldAutData_primeFormP_of_instance_pub (by norm_num) hU
    ?_ hne Nat.prime_three (by norm_num) (three_ne_p_of_mod (by omega)) hg
  intro f₀ k h₀ hbar hf _ hq2 A hA
  exact CFSG.LieType.SeitzGeneration.subfieldPairSUOdd_of_ne_two q.p q.exponent f₀ F hU k h₀ hbar
    3 Nat.prime_three (by norm_num) hf (fun h2 => hq2 ⟨rfl, h2⟩) (2 + 1) (by norm_num) A hA

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.FieldGeneration
