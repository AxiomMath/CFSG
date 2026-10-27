module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar

theorem autIn_eq_autImage {Y : Type} [Group Y] (N : Subgroup Y) [N.Normal] :
    autIn N = autImage N := by
  have hπ : Function.Surjective (MonoidHom.id Y) := Function.surjective_id
  have h := map_autImage_eq_autIn N N (MonoidHom.id Y) hπ (MulEquiv.refl _) (fun n => rfl)
  have hid : (mulAutTransport (MulEquiv.refl ↥N)).toMonoidHom = MonoidHom.id (MulAut ↥N) := by
    ext f b
    simp [mulAutTransport_apply]
  rw [hid, Subgroup.map_id] at h
  exact h.symm

theorem autInOK_of_surj_equiv {Y W : Type} [Group Y] [Group W] (N : Subgroup Y) [N.Normal]
    (M' : Subgroup W) [M'.Normal] (π : Y →* W) (hπ : Function.Surjective π) (φ : ↥N ≃* ↥M')
    (hφ : ∀ n : ↥N, (φ n : W) = π (n : Y)) (h : AutInOK N) : AutInOK M' := by
  have hA : (autIn N).map (mulAutTransport φ).toMonoidHom = autIn M' := by
    rw [autIn_eq_autImage N]
    exact map_autImage_eq_autIn N M' π hπ φ hφ
  have hI : (innSub ↥N).map (mulAutTransport φ).toMonoidHom = innSub ↥M' :=
    innSub_map_transport φ
  have hrel : (innSub ↥N).relIndex (autIn N) = (innSub ↥M').relIndex (autIn M') := by
    rw [← hI, ← hA]
    exact (Subgroup.relIndex_map_map_of_injective _ _ (mulAutTransport φ).injective).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrel]; exact h.1
  · intro hA6 h2
    obtain ⟨eA⟩ := hA6
    obtain ⟨e⟩ := h.2.1 ⟨φ.trans eA⟩ (by rw [hrel]; exact h2)
    have eB : ↥(autIn M') ≃* ↥(autIn N) :=
      (subgroupEquivOfMap (mulAutTransport φ) _ _ hA).symm
    exact ⟨eB.trans e⟩
  · intro hS
    rw [← hrel]
    exact h.2.2 (statedPSL_of_equiv φ.symm hS)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
