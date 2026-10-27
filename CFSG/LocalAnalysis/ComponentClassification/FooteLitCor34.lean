module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitConjugate
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_normalizer_of_mem_footeFamilyOf
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    {a : G} {A : Subgroup G} (hA : IsTwoComponentAt a A) (hAF : A ∈ footeFamilyOf L) :
    centralizer ({a} : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  have hAg : IsTwoComponentAt a (conjugate A g) :=
    ⟨hA.1, conjugate_le_of_mem hA.2.1 hg, isPComponent_conjugate_subgroupOf hg hA.2.2⟩
  exact mem_normalizer_of_conjugate_eq
    (huniq a _ _ hAg hA (conjugate_mem_footeFamilyOf hAF g) hAF)

theorem exists_footeFixed_of_commute (hLB : FooteLBalanceInput)
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    {b : G} (hb : orderOf b = 2) (hzb : z * b = b * z) (hne : z ≠ b)
    (hbA : b ∈ coreActionKernel A) :
    IsTwoComponentAt b (footeFixed A b) ∧ FootePointedMaximal b (footeFixed A b) ∧
      footeFixed A b ∈ footeFamilyOf L := by
  obtain ⟨B, hBb, hstep, ⟨eAB⟩, hcase⟩ :=
    footeStep_cases_index_of_maximal hLB hAmax hb hzb hne hbA
  have hBmax : FootePointedMaximal b B := hAmax.of_reach (FootePointedReach.single hstep)
  obtain ⟨-, ⟨eAL⟩⟩ := id hAF
  have hBF : B ∈ footeFamilyOf L := ⟨⟨b, hBmax⟩, ⟨eAB.symm.trans eAL⟩⟩
  rcases hcase with ⟨-, hBfix⟩ | ⟨hBz, -, -⟩
  · rw [hBfix]
    exact ⟨hBb, hBmax, hBF⟩
  · exfalso
    have hzC : z ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr hzb
    have hBzb : IsTwoComponentAt b (conjugate B z) :=
      ⟨hb, conjugate_le_of_mem hBb.2.1 hzC, isPComponent_conjugate_subgroupOf hzC hBb.2.2⟩
    exact hBz (huniq b _ _ hBzb hBb (conjugate_mem_footeFamilyOf hBF z) hBF)

omit [Finite G] in
theorem oddResidualIn_inf_le_footeFixed (A : Subgroup G) (b : G) :
    oddResidualIn (A ⊓ centralizer ({b} : Set G)) ≤ footeFixed A b := by
  rw [footeFixed_eq_oddResidualIn]
  exact oddResidualIn_mono le_sup_left

omit [Finite G] in
theorem mul_zpow_eq_zpow_neg_mul_of_involutions {z b : G} (hzz : z * z = 1) (hbb : b * b = 1)
    (m : ℤ) : z * (z * b) ^ m = (z * b) ^ (-m) * z := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hzx : z * (z * b) * z⁻¹ = (z * b)⁻¹ := by
    rw [hzinv, mul_inv_rev, hbinv, hzinv, ← mul_assoc, hzz, one_mul]
  have h1 : z * (z * b) ^ m * z⁻¹ = ((z * b)⁻¹) ^ m := by
    rw [← hzx]
    exact (map_zpow (MulAut.conj z) (z * b) m)
  rw [zpow_neg, ← inv_zpow, ← h1]
  group

omit [Finite G] in
theorem conj_eq_of_orderOf_odd {z b : G} (hzz : z * z = 1) (hbb : b * b = 1) {k : ℕ}
    (hk : orderOf (z * b) = 2 * k + 1) :
    ((z * b) ^ ((k : ℤ) + 1))⁻¹ * z * (z * b) ^ ((k : ℤ) + 1) = b := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hxn : (z * b) ^ ((2 * k + 1 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hk, pow_orderOf_eq_one]
  rw [mul_assoc, mul_zpow_eq_zpow_neg_mul_of_involutions hzz hbb, ← mul_assoc, ← zpow_neg,
    ← zpow_add, show -((k : ℤ) + 1) + -((k : ℤ) + 1) = -(((2 * k + 1 : ℕ) : ℤ)) + -1 by
      push_cast; ring, zpow_add, zpow_neg, hxn, inv_one, one_mul, zpow_neg_one, mul_inv_rev,
    hbinv, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_mem_footeFamilyOf_of_mem_coreActionKernel (hLB : FooteLBalanceInput)
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    {b : G} (hb : orderOf b = 2) (hbA : b ∈ coreActionKernel A) :
    ∃ B : Subgroup G, IsTwoComponentAt b B ∧ FootePointedMaximal b B ∧ B ∈ footeFamilyOf L ∧
      oddResidualIn (A ⊓ centralizer ({b} : Set G)) ≤ B := by
  have hz := hAmax.1.1
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hzA : z ∈ coreActionKernel A := GSLit.mem_coreActionKernel_of_le_centralizer hAmax.1.2.1
  by_cases hbz : z = b
  · subst hbz
    exact ⟨A, hAmax.1, hAmax, hAF, (oddResidualIn_le _).trans inf_le_left⟩
  by_cases hcomm : z * b = b * z
  · obtain ⟨h1, h2, h3⟩ := exists_footeFixed_of_commute hLB huniq hAmax hAF hb hcomm hbz hbA
    exact ⟨footeFixed A b, h1, h2, h3, oddResidualIn_inf_le_footeFixed A b⟩
  set x := z * b with hx
  have hxC : ∀ m : ℤ, x ^ m ∈ coreActionKernel A := fun m => zpow_mem (mul_mem hzA hbA) m
  rcases Nat.even_or_odd (orderOf x) with ⟨k, hk⟩ | ⟨k, hk⟩
  ·
    set c := x ^ (k : ℤ) with hc
    have hn0 : 0 < orderOf x := orderOf_pos x
    have hc2 : c ^ 2 = 1 := by
      rw [hc, ← zpow_natCast, ← zpow_mul, show ((k : ℤ) * ((2 : ℕ) : ℤ)) = ((orderOf x : ℕ) : ℤ)
        by rw [hk]; push_cast; ring, zpow_natCast, pow_orderOf_eq_one]
    have hc1 : c ≠ 1 := by
      rw [hc, zpow_natCast]
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hcord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    have hcc : c * c = 1 := by rw [← sq, hc2]
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    have hzc : z * c = c * z := by
      rw [hc, mul_zpow_eq_zpow_neg_mul_of_involutions hzz hbb, zpow_neg, ← hc, hcinv]
    have hbx : b = z * x := by rw [hx, ← mul_assoc, hzz, one_mul]
    have hxc : x * c = c * x := by rw [hc]; exact (Commute.self_zpow x k).eq
    have hbc : b * c = c * b := by
      rw [hbx, mul_assoc, hxc, ← mul_assoc, hzc, mul_assoc]
    have hcz : z ≠ c := by
      intro h
      apply hcomm
      have h1 : z * x = x * z := by rw [h]; exact hxc.symm
      have h2 : b = z * b * z := by
        have := h1
        rw [hx, ← mul_assoc, hzz, one_mul] at this
        exact this
      calc z * b = z * b * z * z := by rw [mul_assoc _ z z, hzz, mul_one]
        _ = b * z := by rw [← h2]
    have hcb : c ≠ b := by
      intro h
      apply hcomm
      have h1 : b * x = x * b := by rw [← h]; exact hxc.symm
      have h2 : b * z * b = z := by
        have := h1
        rw [hx, mul_assoc z b b, hbb, mul_one, ← mul_assoc] at this
        exact this
      calc z * b = b * z * b * b := by rw [h2]
        _ = b * z := by rw [mul_assoc _ b b, hbb, mul_one]
    have hcA : c ∈ coreActionKernel A := hxC k
    obtain ⟨hAc, hAcmax, hAcF⟩ :=
      exists_footeFixed_of_commute hLB huniq hAmax hAF hcord hzc hcz hcA
    have hbAc : b ∈ coreActionKernel (footeFixed A c) :=
      mem_coreActionKernel_footeFixed hbc.symm hbA hAc
    obtain ⟨hB, hBmax, hBF⟩ :=
      exists_footeFixed_of_commute hLB huniq hAcmax hAcF hb hbc.symm hcb hbAc
    refine ⟨footeFixed (footeFixed A c) b, hB, hBmax, hBF, ?_⟩
    refine (closure_le _).mpr fun g hg => ?_
    obtain ⟨hgAb, h2⟩ := hg
    obtain ⟨hgA, hgb⟩ := mem_inf.mp hgAb
    have hgz : g * z = z * g := mem_centralizer_singleton_iff.mp (hAmax.1.2.1 hgA)
    have hgb' : g * b = b * g := mem_centralizer_singleton_iff.mp hgb
    have hgx : g * x = x * g := by
      rw [hx, ← mul_assoc, hgz, mul_assoc, hgb', ← mul_assoc]
    have hgc : g ∈ centralizer ({c} : Set G) :=
      mem_centralizer_singleton_iff.mpr (by rw [hc]; exact (Commute.zpow_right hgx k).eq)
    have hgAc : g ∈ footeFixed A c :=
      oddResidualIn_inf_le_footeFixed A c (mem_oddResidualIn (mem_inf.mpr ⟨hgA, hgc⟩) h2)
    exact oddResidualIn_inf_le_footeFixed _ b (mem_oddResidualIn (mem_inf.mpr ⟨hgAc, hgb⟩) h2)
  ·
    set w := x ^ ((k : ℤ) + 1) with hw
    have hwz : w⁻¹ * z * w = b := conj_eq_of_orderOf_odd hzz hbb hk
    have hwA : conjugate A w = A := conjugate_eq_of_mem_normalizer (hxC _).1
    have h1 := hAmax.conjugate w
    rw [hwz, hwA] at h1
    exact ⟨A, h1.1, h1, ⟨⟨b, h1⟩, hAF.2⟩, (oddResidualIn_le _).trans inf_le_left⟩

end CFSG.ComponentClassification.FooteLit
