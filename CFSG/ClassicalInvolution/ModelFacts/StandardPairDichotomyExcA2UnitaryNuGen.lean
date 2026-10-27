module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Data
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Nu

variable {τ : Tag} {θ : Fin τ.rank → ℤ} {k : Type} [Field k]

variable (τ k) in
@[expose] noncomputable def nuElt (l : List (Fin τ.rank)) (θ : Fin τ.rank → ℤ) : ModGL τ k :=
  simpleWordElt τ k l * rootSL2 τ k θ WSL

theorem nuElt_mem_monomialSubgroup (hθ : IsRoot τ θ) (l : List (Fin τ.rank)) :
    nuElt τ k l θ ∈ monomialSubgroup τ k :=
  mul_mem (simpleWordElt_mem_monomialSubgroup _) (rootSL2_WSL_mem_monomialSubgroup hθ)

theorem nuElt_conj_pinnedX (hθ : IsRoot τ θ) (l : List (Fin τ.rank)) {γ γ'' : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ)
    (h : simpleWordAct τ l (γ - (2 * iform θ γ / iform θ θ) • θ) = γ'') :
    ∃ μ : kˣ, ∀ c : k, nuElt τ k l θ * pinnedX τ k γ c * (nuElt τ k l θ)⁻¹ =
      pinnedX τ k γ'' (μ * c) := by
  obtain ⟨μ, hμ⟩ := rootSL2_WSL_conj_pinnedX (K := k) hθ hγ
  have hγ₁ : IsRoot τ (γ - (2 * iform θ γ / iform θ θ) • θ) := by
    have := IsRoot.smul hγ (rootReflection θ)
    rwa [((exceptional_Lang_root_rank_one_torus_transport τ k hθ).2.2.2.1 γ).1] at this
  obtain ⟨ε, hε, hε'⟩ := simpleWordElt_conj_pinnedX (F := k) l hγ₁
  have hε0 : ε ≠ 0 := fun h0 => by simp [h0] at hε
  refine ⟨Units.mk0 ε hε0 * μ, fun c => ?_⟩
  rw [h] at hε'
  calc nuElt τ k l θ * pinnedX τ k γ c * (nuElt τ k l θ)⁻¹ =
      simpleWordElt τ k l * (rootSL2 τ k θ WSL * pinnedX τ k γ c *
        (rootSL2 τ k θ WSL)⁻¹) * (simpleWordElt τ k l)⁻¹ := by
        rw [nuElt]; group
    _ = _ := by
        rw [hμ, hε']
        simp [mul_assoc]

theorem nuElt_comm_rootDiagUnit_thetaDiag (hθ : IsRoot τ θ) (l : List (Fin τ.rank))
    {δ : Fin τ.rank → ℤ}
    (h1 : ((coxeterSystem τ).wordProd l * rootReflection θ) • δ = -δ) :
    rootDiagUnit τ (thetaDiag δ (-1 : kˣ)) * nuElt τ k l θ =
      nuElt τ k l θ * rootDiagUnit τ (thetaDiag δ (-1 : kˣ)) := by
  have hw : MapsRootLines (nuElt τ k l θ)
      ((coxeterSystem τ).wordProd l * rootReflection θ) :=
    (mapsRootLines_list_prod l).mul (mapsRootLines_rootSL2_WSL hθ)
  refine monomial_comm_rootDiagUnit (a := thetaDiag δ (-1 : kˣ))
    (nuElt_mem_monomialSubgroup hθ l) hw ?_
  set w₀ := (coxeterSystem τ).wordProd l * rootReflection θ with hw₀
  have h2 : w₀⁻¹ • δ = -δ := by
    have h : w₀⁻¹ • (w₀ • δ) = w₀⁻¹ • (-δ) := by rw [h1]
    rw [inv_smul_smul, smul_neg] at h
    exact (neg_eq_iff_eq_neg.1 h.symm)
  have h3 : ∀ v : Fin τ.rank → ℤ, iform δ (w₀ • v) = -iform δ v := fun v => by
    have := iform_smul_smul (τ := τ) w₀ (w₀⁻¹ • δ) v
    rw [smul_inv_smul, h2, iform_neg_left] at this
    exact this
  intro v
  rw [rootChar_thetaDiag, rootChar_thetaDiag, h3]
  rcases Int.even_or_odd (iform δ v) with h | h
  · rw [h.neg.neg_one_zpow, h.neg_one_zpow]
  · rw [h.neg.neg_one_zpow, h.neg_one_zpow]

theorem thetaDiag_neg_one_eq_one_or_neg_one (δ : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    thetaDiag δ (-1 : kˣ) i = 1 ∨ thetaDiag δ (-1 : kˣ) i = -1 := by
  unfold thetaDiag
  rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
  · left
    exact h.neg_one_zpow
  · right
    exact h.neg_one_zpow

end Nu

end CFSG.ClassicalInvolution.ModelFacts.Levi
