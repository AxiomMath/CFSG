module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Borel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34ModelS
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutionsBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Embed

open CFSG.ComponentClassification.PSL3Four

theorem exists_embedding_R {X : Type} [Group X] [Finite X]
    {K : Subgroup X} [K.Normal] (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (hL : IsRankThreeL34 ↥K) :
    ∃ (ε : ↥K ≃* ↥S) (ψ : X →* Equiv.Perm (Fin 42)), Function.Injective ψ ∧ (∀ x, ψ x ∈ R) ∧
      ∀ k : ↥K, ψ k = (ε k : Equiv.Perm (Fin 42)) := by
  obtain ⟨ε⟩ := CFSG.AGLEmbedding.KFactProofs.L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour
    (L34Borel.isLinThreeFour_of_isRankThreeL34 hL)
  obtain ⟨φ, hφ, -⟩ := full_automorphism_action
  let θ : X →* MulAut ↥K := MulAut.conjNormal
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h3 : ((MulAut.conjNormal g : MulAut ↥K) ⟨k, hk⟩ : X) = g * k * g⁻¹ :=
        MulAut.conjNormal_apply g ⟨k, hk⟩
      have h2 : g * k * g⁻¹ = k := by
        rw [← h3]
        have := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : X)) hg
        exact this
      calc k * g = g * k * g⁻¹ * g := by rw [h2]
        _ = g * k := by group
    rw [hC] at hmem
    exact hmem
  let ψ : X →* Equiv.Perm (Fin 42) :=
    R.subtype.comp (φ.symm.toMonoidHom.comp ((MulAut.congr ε).toMonoidHom.comp θ))
  have hψ_inj : Function.Injective ψ :=
    Subtype.val_injective.comp (φ.symm.injective.comp ((MulAut.congr ε).injective.comp hθ))
  refine ⟨ε, ψ, hψ_inj, fun x => (φ.symm _).2, fun k => ?_⟩
  have hεR : ((ε k : ↥S) : Equiv.Perm (Fin 42)) ∈ R := S_le_R (ε k).2
  have hφk : φ ⟨(ε k : Equiv.Perm (Fin 42)), hεR⟩ = MulAut.congr ε (θ k) := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [hφ]
    obtain ⟨k', rfl⟩ := ε.surjective s
    have h1 : (MulAut.congr ε (θ k)) (ε k') = ε ((θ k) k') := by
      rw [MulAut.congr_apply]
      simp
    rw [h1]
    have h2 : (θ k) k' = k * k' * k⁻¹ := by
      apply Subtype.ext
      exact MulAut.conjNormal_apply (k : X) k'
    rw [h2, map_mul, map_mul, map_inv]
    rfl
  show ((φ.symm (MulAut.congr ε (θ k)) : ↥R) : Equiv.Perm (Fin 42)) = _
  rw [← hφk, MulEquiv.symm_apply_apply]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Embed
