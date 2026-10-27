module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.TriD4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.TwE6

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.LieType.Chevalley (twistedE6RootGroup twistedE6Inn)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (range_twistedE6InndiagConj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Dickson.Sec6.I923

section TriD4


theorem ssTw_exists_graphFixed_of_exceptionalModel {T : Type} [Group T] {ℓ f : ℕ}
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

theorem noL34InnAt_triD4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34InnAt FamTriD4 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain rfl := hF
  have hexc : ChevalleyExceptionalModel P .trialityD4 p f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · exact hexc
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := ssTw_exists_graphFixed_of_exceptionalModel hexc
  obtain ⟨hp, hf, -⟩ := hadm
  refine noL34Layer_congr e ?_
  obtain ⟨c, hc⟩ := hψ
  have hcong : MulAut.congr e ψ = MulAut.conj (e c) := by
    rw [← hc]
    exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e c
  rw [hcong]
  refine noL34Layer_conj_graphFixedD4 hO hp hp5 hf hK σ hσ (e c) ?_
  rw [← hcong, ← map_pow, hψ3, map_one]

end TriD4

section TwE6


theorem noL34InnAt_twE6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34InnAt FamTwE6 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain rfl := hF
  have hf : 1 ≤ f := hadm.2.1
  have hE : ChevalleyExceptionalModel P .twistedE6 p f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv hadm.1 hf hE.2
  let θ : P ≃* twistedE6RootGroup K σ := e.symm
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∈ twistedE6Inn K σ :=
    (congr_mem_inner_iff_of_equiv θ ψ).2 hψ
  refine noL34Layer_congr θ ?_
  refine noL34Layer_inndiag_twE6 hO hadm.1 hp5 hf hK σ hσ _ ?_ hβ3
  rw [range_twistedE6InndiagConj]
  exact Subgroup.mem_sup_left hβinn

theorem up34DiagTwE6_holds (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Up34DiagTwE6 := by
  intro ℓ f hℓ hℓ5 hf K _ _ hK σ hσ x hx3 _ hx
  refine noL34Layer_inndiag_twE6 hO hℓ hℓ5 hf hK σ hσ x ?_ hx3
  rw [range_twistedE6InndiagConj]
  exact hx

end TwE6

end CFSG.HardMathSupport.Dickson.Sec6
