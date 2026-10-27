module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzukiRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import Certificates.Certificate113
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

namespace BorelSuzuki

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

theorem aut_inner
    (hm : 0 < m) (σ : MulAut G) (hσ : ∀ q ∈ suzukiCoverRoot m, σ q = q) :
    ∃ r ∈ suzukiCoverRoot m, ∀ k : G, σ k = r * k * r⁻¹ := by
  have hK : Nat.card K = 2 ^ (2 * m + 1) := GaloisField.card 2 (2 * m + 1) (by omega)
  let e := SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK
  let H := CFSG.Blueprint.suzukiGroup m K
  let Q : Sylow 2 H :=
    Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective (suzukiCoverSylow m hm)
  have hQ : (Q : Subgroup H) = (suzukiCoverRoot m).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  let γ : MulAut H := (e.trans σ).trans e.symm
  have hγ : ∀ x ∈ (Q : Subgroup H), γ x = x := by
    intro x hx
    rw [hQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e.symm (σ (e (e.symm y))) = e.symm y
    rw [MulEquiv.apply_symm_apply, hσ y hy]
  let V : Subgroup H :=
    (CFSG.omega₁ (Q : Subgroup H) (p := 2)).map (Q : Subgroup H).subtype
  have hγQ : (Q : Subgroup H).map γ.toMonoidHom = Q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change γ y ∈ (Q : Subgroup H)
      rw [hγ y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hγ x hx⟩
  have hγV : ∀ v ∈ V, γ v = v := by
    rintro v ⟨y, -, rfl⟩
    exact hγ _ y.2
  have hγQV : ∀ x ∈ (Q : Subgroup H), x⁻¹ * γ x ∈ V := by
    intro x hx
    rw [hγ x hx, inv_mul_cancel]
    exact V.one_mem
  obtain ⟨b, hb, hγb⟩ :=
    suzuki_rank_one_Sylow_layer_kernel (by omega) hK Q V rfl γ hγQ hγV hγQV
  refine ⟨e b, ?_, fun k => ?_⟩
  · rw [hQ] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    simpa using hy
  · have h : γ (e.symm k) = b * e.symm k * b⁻¹ := by rw [hγb, MulAut.conj_apply]
    change e.symm (σ (e (e.symm k))) = _ at h
    have h' := congrArg e h
    rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h'

end BorelSuzuki

end CFSG.ProperTwoGeneratedCore.TheoremC
