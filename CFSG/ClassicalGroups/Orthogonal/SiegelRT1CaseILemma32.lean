module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseIAxes

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79
  CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

theorem CaseI.Tsp_injective_scalar (hs : Setting hBN Qf ρ) {a : N} (ha : a ≠ 0) {l l' : K}
    (h : ρ (Tsp hBN a l) = ρ (Tsp hBN a l')) : l = l' := by
  have h1 : Tsp hBN a l = Tsp hBN a l' := hs.inj h
  obtain ⟨z, hz⟩ : ∃ z, BN z a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (hs.nondegN.2 a hcon)
  have h2 := congrArg (fun g : Gsp BN => g.app z) h1
  simp only [Tsp_app, add_right_inj] at h2
  have h3 : l * BN z a = l' * BN z a := smul_left_injective K ha h2
  exact mul_right_cancel₀ hz h3

theorem CaseI.Tsp_ne_of_linearIndependent (hs : Setting hBN Qf ρ) {a c : N}
    (hli : LinearIndependent K ![a, c]) {l m : K} (hm : m ≠ 0) :
    ρ (Tsp hBN a l) ≠ ρ (Tsp hBN c m) := by
  intro h
  have hc : c ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
  have h1 : Tsp hBN a l = Tsp hBN c m := hs.inj h
  obtain ⟨z, hz⟩ : ∃ z, BN z c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (hs.nondegN.2 c hcon)
  have h2 := congrArg (fun g : Gsp BN => g.app z) h1
  simp only [Tsp_app, add_right_inj] at h2
  have h3 : (l * BN z a) • a + (-(m * BN z c)) • c = 0 := by
    rw [h2, neg_smul]
    abel
  have h4 := neg_eq_zero.mp (LinearIndependent.pair_iff.mp hli _ _ h3).2
  exact hz ((mul_eq_zero.mp h4).resolve_left hm)

theorem false_of_axis_eq (hs : Setting hBN Qf ρ) {a c : N} (hli : LinearIndependent K ![a, c])
    (h : ∀ l m : K, l ≠ 0 → m ≠ 0 → axis hBN ρ a l = axis hBN ρ c m) : False := by
  have ha : a ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
  have hA2 : finrank K (axis hBN ρ a 1) = 2 := CaseI.finrank_axis hs ha one_ne_zero
  have hAs : ∀ w ∈ axis hBN ρ a 1, Qf w = 0 := axis_totallySingular hs a 1
  obtain ⟨a₁, a₂, ha₁, ha₂, hli₂, hspan⟩ := exists_basis_of_finrank_eq_two hA2
  have h₁ : Qf a₁ = 0 := hAs a₁ ha₁
  have h₂ : Qf a₂ = 0 := hAs a₂ ha₂
  have h₁₂ : polarBilin Qf a₁ a₂ = 0 := polar_eq_zero_of_totallySingular hAs ha₁ ha₂
  have h11 : axis hBN ρ c 1 = axis hBN ρ a 1 := (h 1 1 one_ne_zero one_ne_zero).symm
  have hk : ∀ (x : N) (l : K), (l ≠ 0 → axis hBN ρ x l = axis hBN ρ a 1) →
      ∃ k : K, ρ (Tsp hBN x l) = siegelEquiv Qf a₁ a₂ h₁ h₂ h₁₂ k := by
    intro x l hl
    by_cases hl0 : l = 0
    · exact ⟨0, by rw [hl0, (Tsp_eq_one_iff hBN hs.nondegN x 0).mpr (Or.inr rfl), map_one,
        siegelEquiv_zero]⟩
    · obtain ⟨k, -, hk⟩ := exists_eq_siegelEquiv hs.nondeg (hs.iso (Tsp hBN x l)) hli₂
        (hspan.trans (hl hl0).symm) (fun w hw => axis_totallySingular hs x l w hw) h₁ h₂ h₁₂
      exact ⟨k, hk⟩
  choose f hf using fun l : K => hk a l fun hl => (h l 1 hl one_ne_zero).trans h11
  obtain ⟨kc, hkc⟩ := hk c 1 fun _ => h11
  have hinj : Function.Injective f := fun l l' hll' =>
    CaseI.Tsp_injective_scalar hs ha (by rw [hf l, hf l', hll'])
  obtain ⟨l, hl⟩ := Finite.injective_iff_surjective.mp hinj kc
  exact CaseI.Tsp_ne_of_linearIndependent hs hli one_ne_zero (by rw [hf l, hl, hkc])

theorem exists_axis_ne (hs : Setting hBN Qf ρ) {a c : N} (hli : LinearIndependent K ![a, c]) :
    ∃ l m : K, l ≠ 0 ∧ m ≠ 0 ∧ axis hBN ρ a l ≠ axis hBN ρ c m := by
  by_contra hcon
  push Not at hcon
  exact false_of_axis_eq hs hli hcon

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
