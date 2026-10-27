module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSylow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelMaximal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalSmallFamilyOrbit CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise

variable {n : ℕ} {K : Type} [Field K]

theorem charP_of_card {p f : ℕ} [Finite K] (hp : p.Prime) (hK : Nat.card K = p ^ f) :
    CharP K p := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)

theorem witness_unipotent_isSylow_normalizer {G : Type} [Group G] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (hn : 3 ≤ n)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    (∃ S : Sylow p G, (S : Subgroup G) = (plusProjectiveUnipotent n K).map e.symm.toMonoidHom) ∧
      Subgroup.normalizer
          (((plusProjectiveUnipotent n K).map e.symm.toMonoidHom : Subgroup G) : Set G) =
        (plusProjectiveBorel n K).map e.symm.toMonoidHom := by
  obtain ⟨S, hS⟩ := plusProjectiveUnipotent_isSylow n K p hn
  have hsurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  refine ⟨⟨Sylow.mapSurjective (f := e.symm.toMonoidHom) hsurj S, ?_⟩, ?_⟩
  · rw [Sylow.coe_mapSurjective, hS]
  · rw [← Subgroup.map_equiv_normalizer_eq, plusProjectiveUnipotent_normalizer n K hn]

theorem witness_flagFamily_aut {G : Type} [Group G] [Finite K] (hn : 3 ≤ n)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) (alpha : MulAut G) :
    (fun J => J.map alpha.toMonoidHom) ''
        ((fun J => J.map e.symm.toMonoidHom) '' plusProjectiveFlagFamily n K) =
      (fun J => J.map e.symm.toMonoidHom) '' plusProjectiveFlagFamily n K := by
  have hbeta := plusProjectiveFlagFamily_aut n K hn (MulAut.congr e alpha)
  have key := familyTransport_automorphism e.symm (plusProjectiveFlagFamily n K)
    (MulAut.congr e alpha)
  have hcc : MulAut.congr e.symm (MulAut.congr e alpha) = alpha := by
    ext x
    change e.symm (e (alpha (e.symm (e x)))) = alpha x
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  rw [hcc] at key
  change familyTransport e.symm
    ((fun J => J.map (MulAut.congr e alpha).toMonoidHom) '' plusProjectiveFlagFamily n K) =
      alpha • familyTransport e.symm (plusProjectiveFlagFamily n K) at key
  rw [hbeta] at key
  exact key.symm

theorem orthogonal_geometry_plus_model_Borel_normalizer {G : Type} [Group G] {p f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n p f) [Finite K] (hK : Nat.card K = p ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    (∀ g : GL (Fin n ⊕ Fin n) K, g ∈ plusMatrixUnipotent n K ↔
      ∃ (A : GL (Fin n) K) (C : Matrix (Fin n) (Fin n) K),
        (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular ∧
        (∀ i, (A : Matrix (Fin n) (Fin n) K) i i = 1) ∧
        Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
        g.val = Matrix.fromBlocks (A : Matrix (Fin n) (Fin n) K)
          ((A : Matrix (Fin n) (Fin n) K) * C) 0
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) ∧
    plusMatrixUnipotent n K ≤ StatedOmega (StatedQuadPlus n K) ∧
    (∃ S : Sylow p (StatedProj (StatedOmega (StatedQuadPlus n K))),
      (S : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) =
        plusProjectiveUnipotent n K) ∧
    Subgroup.normalizer (plusProjectiveUnipotent n K :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) = plusProjectiveBorel n K ∧
    (∀ alpha : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))),
      (fun J => J.map alpha.toMonoidHom) '' plusProjectiveFlagFamily n K =
        plusProjectiveFlagFamily n K) ∧
    (∃ S : Sylow p G, (S : Subgroup G) = (plusProjectiveUnipotent n K).map e.symm.toMonoidHom) ∧
    Subgroup.normalizer
        (((plusProjectiveUnipotent n K).map e.symm.toMonoidHom : Subgroup G) : Set G) =
      (plusProjectiveBorel n K).map e.symm.toMonoidHom ∧
    (∀ alpha : MulAut G,
      (fun J => J.map alpha.toMonoidHom) ''
          ((fun J => J.map e.symm.toMonoidHom) '' plusProjectiveFlagFamily n K) =
        (fun J => J.map e.symm.toMonoidHom) '' plusProjectiveFlagFamily n K) := by
  obtain ⟨hp, -, hn4⟩ := h.1
  have hn : 3 ≤ n := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card hp hK
  obtain ⟨hSylow, hnorm⟩ := witness_unipotent_isSylow_normalizer p hn e
  exact ⟨mem_plusMatrixUnipotent n K, plusMatrixUnipotent_le_derived n K hn,
    plusProjectiveUnipotent_isSylow n K p hn, plusProjectiveUnipotent_normalizer n K hn,
    plusProjectiveFlagFamily_aut n K hn, hSylow, hnorm, witness_flagFamily_aut hn e⟩

theorem orthogonal_geometry_plus_model_maximal_Borel_overgroups {G : Type} [Group G]
    {p f : ℕ} (h : StatedClassicalModel G .POmegaPlus n p f) [Finite K]
    (M : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hM : IsCoatom M) (hBM : plusProjectiveBorel n K ≤ M) :
    (∃ i : ℕ, 1 ≤ i ∧ i ≤ n - 2 ∧
      M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K i)) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
      (Xstar n K (by have := h.1.2.2; omega)) ∨
    M = statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n) :=
  plusProjectiveMaximalBorel_overgroups n K (by have := h.1.2.2; omega) M hM hBM

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
