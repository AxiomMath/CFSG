module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Field
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.Assembly.LowTwoRank

theorem lieS3_noL2_e6
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {P : Type} [Group P] [Finite P] {n f : ℕ} (hadm : StatedLieAdmissible .E6 n 3 f)
    (hm : LieModel P .E6 n 3 f) {ψ : MulAut P} (hψ3 : ψ ^ 3 = 1) (hψ : ψ ∉ inner P) :
    NoL2Layer ψ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E6 (3 ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E6 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hq : ¬ 3 ∣ Nat.card F - 1 := by
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h1 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    rw [hFcard]
    omega
  obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, -, -, hrj, hδ⟩ :=
    exists_conj_entrywise_of_not_innerDiag .E6 (Or.inl rfl) hf F hFcard Nat.prime_three
      (by norm_num) _ hβ3 fun g a hdiag =>
        hq (prime_dvd_of_diag_noninner .E6 (Or.inl rfl) F Nat.prime_three g a _ hdiag hβ3 hβinn).2
  refine noL2Layer_congr θ (noL2Layer_of_conj_pow hrj hδ ?_)
  exact noL2Layer_entrywise_e6 hO Nat.prime_three (by omega) T hTc

theorem lieS3_noL2_twE6
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {P : Type} [Group P] [Finite P] {n f : ℕ} (hadm : StatedLieAdmissible .twistedE6 n 3 f)
    (hm : LieModel P .twistedE6 n 3 f) {ψ : MulAut P} (hψ3 : ψ ^ 3 = 1) (hψ : ψ ∉ inner P) :
    NoL2Layer ψ := by
  have hf : 1 ≤ f := hadm.2.1
  have hE : ChevalleyExceptionalModel P .twistedE6 3 f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv Nat.prime_three hf hE.2
  let θ : P ≃* twistedE6RootGroup K σ := e.symm
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv P θ.toEquiv
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ twistedE6Inn K σ := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hg : Nat.gcd 3 (3 ^ f + 1) = 1 := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  have hΔ : twistedE6Diag K σ ≤ twistedE6Inn K σ := by
    rintro _ ⟨u, rfl⟩
    exact compatDiagAutHom_mem_inner hK hσ hg u
  have hdiag : MulAut.congr θ ψ ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [sup_eq_left.2 hΔ]
    exact hβinn
  exact noL2Layer_congr θ
    (noL2Layer_of_not_mem_twistedE6Inndiag hO Nat.prime_three hf hK σ hσ hβ3 hdiag)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
