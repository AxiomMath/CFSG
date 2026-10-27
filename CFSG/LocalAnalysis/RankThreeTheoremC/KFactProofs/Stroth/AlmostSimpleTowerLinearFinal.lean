module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerLinearOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem linearOuterResidual_holds : LinearOuterResidual := by
  intro p hp hp2 X _ _ L _ hC hE m q hv hm ⟨e⟩ hφ hq1 x hx
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hn3 : 3 ≤ m + 1 := by omega
  have hcardK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hpK : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    rw [hcardK]
    exact hq1
  let eL : ↥L ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _))
  have hTwo : ∃ x₁ x₂ : projectiveSL (m + 1) (GaloisField q.p q.exponent), Commute x₁ x₂ ∧
      x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      ∀ σ : GaloisField q.p q.exponent ≃+* GaloisField q.p q.exponent,
        fieldAut (m + 1) _ σ x₁ = x₁ ∧ fieldAut (m + 1) _ σ x₂ = x₂ := by
    by_cases hpc : p = q.p
    · subst hpc
      exact exists_two_indep_fixed_unip (K := GaloisField q.p q.exponent) (ℓ := q.p) hn3
    · have hd0 : 0 < Nat.gcd (m + 1) (q.card - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
      have hd : 2 * p ≤ Nat.gcd (m + 1) (q.card - 1) := by
        by_contra h
        exact not_dvd_totient_of_lt hp hp2 hd0 (by omega) hφ
      have hn2 : 2 * p ≤ m + 1 := hd.trans (Nat.gcd_le_left _ (by omega))
      have h3 := hp.two_le
      exact exists_two_indep_fixed_blocks (K := GaloisField q.p q.exponent) (ℓ := q.p) hp
        (by omega) hpc hpK (by omega)
  let ψ : X →* MulAut (projectiveSL (m + 1) (GaloisField q.p q.exponent)) :=
    (MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal
  have hψ : Function.Injective ψ := by
    have h1 : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
      CFSG.LieType.SeitzGeneration.conjNormal_injective hC
    exact (MulAut.congr eL).injective.comp h1
  have hL : ∀ y : projectiveSL (m + 1) (GaloisField q.p q.exponent),
      ∃ l ∈ L, ψ l = MulAut.conj y := by
    intro y
    refine ⟨((eL.symm y : ↥L) : X), (eL.symm y).2, ?_⟩
    ext z
    simp [ψ, MulAut.conjNormal_val, MulAut.congr_apply, MulAut.conj_apply]
  have hrk : CFSG.LieType.SeitzGeneration.RankLE2 p X := hE
  have hin := linear_pElements_inner_of_two_indep hn3 hp hp2 hpK hTwo hrk ψ hψ L hL hx
  obtain ⟨y, hy⟩ := hin
  obtain ⟨l, hlL, hl⟩ := hL y
  have : l = x := hψ (by rw [hl, hy])
  exact this ▸ hlL

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
