module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldCases
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldAutPSU
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldGlue

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.GH74.GLS.IVK

theorem input14_5Aut_holds : LocalBalance.Lemma53Ns.Input14_5Aut := by
  intro K _ _ hK hcore α hα hord
  rcases hα with h1 | h2 | h3
  · rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · obtain ⟨F, _, _, e, σ, hψ⟩ := l3bf_cases_psl h2
    obtain ⟨-, L, -, hq, -, -, hlay⟩ := l3bf_core_layer hcore e α hψ (l3bf_fixData_psl σ)
    right
    rw [hlay]
    exact hq
  · obtain ⟨p, f, f₀, F, _, hF, e, σ, -, hf, h₀, hψ⟩ := l3bf_cases_psu hK hord h3
    by_cases hq : p ^ f₀ = 2
    · left
      exact l3bf_layer_bot_of_descent e α hψ (l3bUfix_solvable hF hf h₀ hq)
    · obtain ⟨-, L, -, hLq, -, -, hlay⟩ :=
        l3bf_core_layer hcore e α hψ (l3bf_fixData_psu hF hf h₀ hq)
      right
      rw [hlay]
      exact hLq

theorem input9_2_8_holds : LocalBalance.Lemma53Ns.Input9_2_8 := by
  intro K _ _ hK hcore α hα hord
  have hOf : GLAPPrimeCore 3 ↥(LocalBalance.Lemma53Ns.fixSub α) = ⊥ → GLAPPrimeCoreOf 3
      (LocalBalance.Lemma53Ns.fixSub α) = ⊥ := fun h => by rw [GLAPPrimeCoreOf, h, Subgroup.map_bot]
  apply hOf
  rcases hα with h1 | h2 | h3
  · rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · obtain ⟨F, _, _, e, σ, hψ⟩ := l3bf_cases_psl h2
    exact (l3bf_core_layer hcore e α hψ (l3bf_fixData_psl σ)).1
  · obtain ⟨p, f, f₀, F, _, hF, e, σ, hσ, hf, h₀, hψ⟩ := l3bf_cases_psu hK hord h3
    by_cases hq : p ^ f₀ = 2
    · have hp2 : p = 2 := by
        have h1 : p ∣ 2 := hq ▸ dvd_pow_self p (by have := h₀.one_le; omega)
        exact (Nat.prime_dvd_prime_iff_eq hF.prime Nat.prime_two).1 h1
      subst hp2
      have hf1 : f₀ = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using hq)
      subst hf1
      subst hf
      exact l3bf_core_of_descent hcore e α hψ (l3bUfix_core_small hF hσ rfl h₀)
    · exact (l3bf_core_layer hcore e α hψ (l3bf_fixData_psu hF hf h₀ hq)).1

theorem l3bf_mem_zpowers_of_descent {Y P : Type*} [Group Y] [Group P]
    (hY : CFSG.Open.IsQuasisimple Y) (e : (Y ⧸ Subgroup.center Y) ≃* P) (α β : MulAut Y)
    {ψ : MulAut P} (hψ : MulAut.congr e (centerDescend Y α) = ψ)
    (hρ : MulAut.congr e (centerDescend Y β) ∈ Subgroup.zpowers ψ) :
    β ∈ Subgroup.zpowers α := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hρ
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have h1 : centerDescend Y (β * α ^ (-k)) = 1 := by
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, map_zpow, map_zpow, hψ, ← hk, map_one]
    simp
  have h2 := eq_one_of_centerDescend_eq_one hY h1
  have h3 : β = α ^ k := by
    have : β = (α ^ (-k))⁻¹ := mul_eq_one_iff_eq_inv.1 h2
    rw [this, ← zpow_neg, neg_neg]
  exact h3.symm

theorem l3bf_descend_fix {Y P : Type*} [Group Y] [Group P] (e : (Y ⧸ Subgroup.center Y) ≃* P)
    (β : MulAut Y) {L : Subgroup Y} (hβ : ∀ y ∈ L, β y = y) {x : P}
    (hx : x ∈ L.map ((e : _ →* P).comp (QuotientGroup.mk' (Subgroup.center Y)))) :
    MulAut.congr e (centerDescend Y β) x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  show MulAut.congr e (centerDescend Y β) (e (QuotientGroup.mk y)) = e (QuotientGroup.mk y)
  rw [← descend_compat e β y, hβ y hy]

theorem input9_5_holds : LocalBalance.Lemma53Ns.Input9_5 := by
  intro K _ _ hK hcore α hα hord hlay β hβ
  rcases hα with h1 | h2 | h3
  · rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · obtain ⟨F, _, _, e, σ, hψ⟩ := l3bf_cases_psl h2
    obtain ⟨-, L, -, -, hLmap, -, hL⟩ := l3bf_core_layer hcore e α hψ (l3bf_fixData_psl σ)
    rw [hL] at hβ
    refine l3bf_mem_zpowers_of_descent hK e α β hψ ?_
    refine l3bf_rigid_psl σ _ (fun g => ?_)
    refine l3bf_descend_fix e β hβ ?_
    rw [hLmap, commutator_fix_eq]
    exact ⟨g, rfl⟩
  · obtain ⟨p, f, f₀, F, _, hF, e, σ, -, hf, h₀, hψ⟩ := l3bf_cases_psu hK hord h3
    by_cases hq : p ^ f₀ = 2
    · exact absurd (l3bf_layer_bot_of_descent e α hψ (l3bUfix_solvable hF hf h₀ hq)) hlay
    · obtain ⟨-, L, -, -, hLmap, -, hL⟩ :=
        l3bf_core_layer hcore e α hψ (l3bf_fixData_psu hF hf h₀ hq)
      rw [hL] at hβ
      have h2 : 2 ≤ p ^ f₀ :=
        hF.prime.two_le.trans (Nat.le_self_pow (by have := h₀.one_le; omega) p)
      have hq2 : 2 < p ^ f := by
        have : p ^ f = (p ^ f₀) ^ 3 := by rw [hf, mul_comm, pow_mul]
        rw [this]
        have : 2 ^ 3 ≤ (p ^ f₀) ^ 3 := Nat.pow_le_pow_left h2 3
        omega
      refine l3bf_mem_zpowers_of_descent hK e α β hψ ?_
      refine l3bf_rigid_psu hF hf h₀ hq2 hq _ (fun g => ?_)
      refine l3bf_descend_fix e β hβ ?_
      rw [hLmap, commutator_fix_eq_U hF hf h₀ hq]
      exact ⟨g, rfl⟩

end CFSG.HardMathSupport.Solomon.Coordinator
