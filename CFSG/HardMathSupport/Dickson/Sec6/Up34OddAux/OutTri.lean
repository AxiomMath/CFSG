module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.A2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.D4Normal

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.Sec66T
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section TriD4


theorem OutTri.exists_graphFixed_of_exceptionalModel {T : Type} [Group T] {ℓ f : ℕ}
    (hm : ChevalleyExceptionalModel T .trialityD4 ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ (ℓ ^ f)) ∧ Nonempty (T ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, σ₀, hK, hσ₀, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hadm.1 hadm.2.1
      hmod
  have hbij : Function.Bijective σ₀ := ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ c, σ c = c ^ (ℓ ^ f) := hσ₀
  have hK3 : Nat.card K = (ℓ ^ f) ^ 3 := hK
  let e' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* T := e
  exact ⟨K, inferInstance, inferInstance, σ, hK3, hσ, ⟨e'.symm⟩⟩

theorem noL34OuterAt_triD4 (hA2 : TriD4A2NoL34) : NoL34OuterAt FamTriD4 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hninn
  obtain rfl := hF
  have hexc : ChevalleyExceptionalModel P .trialityD4 p f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · exact hexc
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := OutTri.exists_graphFixed_of_exceptionalModel hexc
  obtain ⟨hp, hf, -⟩ := hadm
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  refine noL34Layer_congr e ?_
  have hφ3 : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hφ : MulAut.congr e ψ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rintro ⟨c, hc⟩
    apply hninn
    refine ⟨e.symm c, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hc
  exact OutTri.noL34Layer_three_D4_outer_odd hA2 hp hp5 hf hK σ hσ _ hφ3 hφ

theorem noL34OuterAt_triD4_of_minus (hMinus : TriD4A2Minus34) : NoL34OuterAt FamTriD4 :=
  noL34OuterAt_triD4 (triD4A2NoL34_of_minus hMinus)

end TriD4

section D4


theorem noL34OuterAt_d4_of_order (hO : LieOrderFormulasInput) (hA2 : TriD4A2NoL34) :
    NoL34OuterAt FamD4 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hninn
  obtain ⟨rfl, rfl⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus 4 p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  obtain ⟨e'⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  haveI : Fact p.Prime := ⟨hp⟩
  let E : P ≃* adjointGroup Tag.D4 K := e.trans e'
  haveI := D4Aux.finite_adjointD4 K
  refine noL34Layer_congr E ?_
  have hα3 : MulAut.congr E ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hα : MulAut.congr E ψ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K) := by
    rintro ⟨c, hc⟩
    apply hninn
    refine ⟨E.symm c, (MulAut.congr E).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hc
  exact OutTri.noL34Layer_adjointD4_outer hO hA2 hp5 hf K hK _ hα3 hα

end D4

section D4Final


theorem noL34OuterAt_d4 (hA2 : TriD4A2NoL34) : NoL34OuterAt FamD4 :=
  noL34OuterAt_d4_of_order CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hA2

theorem noL34OuterAt_d4_of_minus (hMinus : TriD4A2Minus34) : NoL34OuterAt FamD4 :=
  noL34OuterAt_d4 (triD4A2NoL34_of_minus hMinus)

end D4Final

end CFSG.HardMathSupport.Dickson.Sec6
