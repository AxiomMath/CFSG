module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldConc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section NF


theorem exists_conj_entrywise_exc_of_diag {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiag : τ = .E6 → p ≠ 3 ∨ ¬ p ∣ Nat.card K - 1) {β : MulAut (adjointGroup τ K)}
    (hβp : β ^ p = 1)
    (hβ : β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup τ K)), orderOf σ = p ∧
      δ * β * δ⁻¹ = entrywiseAdjointAut τ σ := by
  rcases hτ with rfl | hE
  · exact exists_conj_entrywise_excF4 hK2 hp hβp hβ
  · refine exists_conj_entrywise_excE_of_not_innerDiag hE hp hp2 hβp fun g a h => ?_
    obtain ⟨h1, h2⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hE K hp g a β h hβp hβ
    rcases hE with rfl | rfl | rfl
    · rcases hdiag rfl with h3 | h3
      · rw [det_cartan_E6] at h1
        exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)
      · exact h3 h2
    · rw [det_cartan_E7] at h1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
    · rw [det_cartan_E8] at h1
      exact hp.not_dvd_one h1

end NF


variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_adjointGroup_of_outer_of_diag {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiag : τ = .E6 → p ≠ 3 ∨ ¬ p ∣ Nat.card K - 1) (hpQ : p ∣ Nat.card K ^ 2 - 1)
    (hS : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hBc : Nat.card B = p ^ (frameSize τ + 2)) (eX : ↥(adjointGroup τ K) ≃* PSimple p S)
    (hX : ∀ F : Subgroup ↥(adjointGroup τ K), IsElemAbelian p F →
      Nat.card F ≤ p ^ frameSize τ) :
    S267ConcA p S B :=
  concA_of_adjointGroup_of_outer_of_nf hτ hK2 hp hp2
    (fun _ h1 h2 => exists_conj_entrywise_exc_of_diag hτ hK2 hp hp2 hdiag h1 h2) hpQ hS hcore hZ
    hB hBC hBc eX hX

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
