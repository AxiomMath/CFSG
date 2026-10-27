module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

theorem ringChar_algebraicClosure (K : Type) [Field K] : ringChar (AlgebraicClosure K) = ringChar K := by
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  exact ringChar.eq (AlgebraicClosure K) (ringChar K)


theorem lieCompExport_inner_untw (hres : ExcRationalLieTypes) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) (hpK : ¬ 3 ∣ Nat.card K)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1)
    (hlayer : PerfectInLayer β) {ℓ : ℕ} (hℓ : ringChar K = ℓ) : LieCompExport ℓ β := by
  classical
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h | h
    · subst h
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
        (hG2 rfl)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h])
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) Nat.prime_three (by norm_num)
  have hsmall : τ = .G2 → 5 ≤ 3 ∨ 4 ≤ Nat.card K := fun hg => by
    right
    have h3 := hG2 hg
    by_contra hlt
    have : Nat.card K = 3 := by omega
    exact hpK (by rw [this])
  have hAC : ringChar (AlgebraicClosure K) = ℓ := by rw [ringChar_algebraicClosure, hℓ]
  by_cases hq : 5 ≤ 3 ∨ 4 ≤ Nat.card K
  · obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_untw hτ Nat.prime_three hpK hq hmon hperf β h hhL hβ hp1 hh1
    exact lieCompExport_of_langSetup hres S ι hinj hrange β hconj hT hap h1
      (langSetup_hTame S hT hap h1) hlayer hAC
  · have hK1 : 0 < Nat.card K := Nat.card_pos
    have h5K : ¬ 5 ∣ Nat.card K := fun h5 => by
      have := Nat.le_of_dvd hK1 h5
      omega
    obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_untw_of_prime hτ Nat.prime_three hpK Nat.prime_five h5K
        (Or.inl le_rfl) hmon hperf β h hhL hβ hp1 hh1
    exact lieCompExport_of_langSetup hres S ι hinj hrange β hconj hT hap h1
      (langSetup_hTame_of_prime S Nat.prime_three (natCast_ne_zero_algebraicClosure Nat.prime_three hpK)
        (fun hG2' => (hq (hsmall hG2')).elim) hT hap h1) hlayer hAC

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
