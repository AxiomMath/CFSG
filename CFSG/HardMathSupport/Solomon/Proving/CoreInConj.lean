module

public import CFSG.HardMathSupport.Solomon.Proving.Signalizer
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem coreIn_map_equiv {G : Type*} [Group G] [Finite G] (p k : ℕ) (e : G ≃* G)
    (P X : Subgroup G) :
    coreIn p k (P.map e.toMonoidHom) (X.map e.toMonoidHom) =
      (coreIn p k P X).map e.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun Q hQ => ?_
    obtain ⟨Q', rfl⟩ : ∃ Q' : Subgroup G, Q = Q'.map e.toMonoidHom :=
      ⟨Q.comap e.toMonoidHom, (Subgroup.map_comap_eq_self_of_surjective e.surjective Q).symm⟩
    have hQ'P : Q' ≤ P := (Subgroup.map_le_map_iff_of_injective e.injective).1 hQ.1
    have hk : k ≤ pRank p Q' := by
      rw [← CFSG.AGLEmbedding.Norton.OrdinaryProofs.pRank_map_equiv e Q']
      exact hQ.2
    rw [← Subgroup.map_normalizer_eq_of_bijective Q' e.bijective,
      ← Subgroup.map_inf_eq _ _ _ e.injective]
    exact Subgroup.map_mono (le_coreIn hQ'P hk)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun Q hQ => ?_
    have h1 : (X ⊓ Subgroup.normalizer (Q : Set G)).map e.toMonoidHom ≤
        X.map e.toMonoidHom ⊓ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.map_inf_eq _ _ _ e.injective, Subgroup.map_normalizer_eq_of_bijective Q e.bijective]
    have hkQ : k ≤ pRank p (Q.map e.toMonoidHom) := by
      rw [CFSG.AGLEmbedding.Norton.OrdinaryProofs.pRank_map_equiv e Q]
      exact hQ.2
    have h2 : X.map e.toMonoidHom ⊓ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup G) : Set G) ≤
        coreIn p k (P.map e.toMonoidHom) (X.map e.toMonoidHom) :=
      le_coreIn (Subgroup.map_mono hQ.1) hkQ
    exact Subgroup.map_le_iff_le_comap.1 (h1.trans h2)

theorem coreIn_gLBConj {G : Type*} [Group G] [Finite G] (p k : ℕ) (g : G)
    (P X : Subgroup G) :
    coreIn p k (GLBConj g P) (GLBConj g X) = GLBConj g (coreIn p k P X) :=
  coreIn_map_equiv p k (MulAut.conj g⁻¹) P X

end CFSG.HardMathSupport.Solomon.Proving

end
