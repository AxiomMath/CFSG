module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gPos
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Hx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE



local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
  (aeBar8 vq vq_mul vq_eq_iff conj_vq vq_inv vq_empty E8Pkg A6eCtx)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (ae6M₀ ae6Vertex_of_ident AE6Vertex ae6_exists_r ae6_card8 ae6_mem_DSet ae6_conj_of_mem_DSet le_ae6L
    AE6ModelPar)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}

section Vert

variable (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
  (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
include H fr

theorem t_comm_tau : t * (y * t * y⁻¹) = (y * t * y⁻¹) * t := by
  rw [fr.hy]
  exact A6c.t_tau_comm (A6c.frameCalc_of H fr)

theorem inv_trich' {J : Subgroup Y} {z : Y} (hJΩ : J ∈ Ω[R]) (hJD : J ∈ DSet Ω[R] W)
    (hz : IsUniqueInvolution J z) : z = t ∨ z = y * t * y⁻¹ ∨ z = t * (y * t * y⁻¹) := by
  rcases A6c.inv_trich H fr hJΩ hJD hz with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl (by rw [h1, fr.hy]))
  · exact Or.inr (Or.inr (by rw [h1, ← fr.hy]; exact (t_comm_tau H fr).symm))

theorem M_le_M₀ :
    MGrp Ω[R] W ≤ ae6M₀ (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) t (y * t * y⁻¹) := by
  have hd := H.ex.1.datum
  have hΩ := hd.hyp
  have hinv := conjInvariant_conjClass (tightCore R)
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨m, hm, hmJ⟩ := A6d.exists_M_conj_of_mem_D H hJ
  have hJΩ : J ∈ Ω[R] := hmJ ▸ hinv m K hd.mem
  have hJP : J ∈ ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K :=
    ⟨m, (le_sup_left : MGrp Ω[R] W ≤ ae6I Ω[R] W (u₁ * u₂)) hm, hmJ⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJΩ
  refine le_iSup₂_of_le J ⟨hJP, ?_⟩ le_rfl
  rcases inv_trich' H fr hJΩ hJ hz with h1 | h1 | h1
  · exact Or.inl (h1 ▸ hz)
  · exact Or.inr (Or.inl (h1 ▸ hz))
  · exact Or.inr (Or.inr (h1 ▸ hz))

theorem M₀_le_L (x : Y) :
    ae6M₀ (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) t (y * t * y⁻¹) ≤ ae6L Ω[R] t (y * t * y⁻¹) x := by
  have hd := H.ex.1.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨r, hr, hrτ⟩ := ae6_exists_r H fr
  have hKL : K ≤ ae6L Ω[R] t (y * t * y⁻¹) x := le_ae6L (Or.inl (Or.inl ⟨hd.mem, hd.hz⟩))
  have hrL := hKL hr
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨hJX, hJt⟩ := hJ
  have hJΩ : J ∈ Ω[R] := by
    obtain ⟨g, -, rfl⟩ := hJX
    exact hinv g K hd.mem
  rcases hJt with h' | h' | h'
  · exact le_ae6L (Or.inl (Or.inl ⟨hJΩ, h'⟩))
  · exact le_ae6L (Or.inl (Or.inr ⟨hJΩ, h'⟩))
  · have h1 : IsUniqueInvolution (conjSub r⁻¹ J) (y * t * y⁻¹) := by
      have h2 := h'.conj r⁻¹
      rwa [show r⁻¹ * (t * (y * t * y⁻¹)) * r⁻¹⁻¹ = y * t * y⁻¹ by rw [← hrτ]; group] at h2
    have h3 : conjSub r⁻¹ J ≤ ae6L Ω[R] t (y * t * y⁻¹) x :=
      le_ae6L (Or.inl (Or.inr ⟨hinv _ J hJΩ, h1⟩))
    calc J = conjSub r (conjSub r⁻¹ J) := (conjSub_conjSub_inv r J).symm
      _ ≤ conjSub r _ := conjSub_mono h3
      _ = _ := conjSub_eq_self_of_mem hrL

theorem vertex_I (hPar : AE6ModelPar) (A : AEIdent (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) 8)
    (hspan : pSpan (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) = ae6I Ω[R] W (u₁ * u₂))
    (hker : A.φ.ker = ⊥) :
    AE6Vertex (ae6I Ω[R] W (u₁ * u₂)) (ae6M₀ (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) t (y * t * y⁻¹))
      (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hΩ : HypOmegaGen Ω[R] := hd.hyp
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hinv := conjInvariant_conjClass (tightCore R)
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  have hτW : y * t * y⁻¹ ∈ W := by
    rw [fr.hy]
    exact W.mul_mem (W.mul_mem (W.mul_mem fr.h₁.2 fr.h₂.2) fr.h₃.2) fr.h₄.2
  have hKy : IsUniqueInvolution (conjSub y K) (y * t * y⁻¹) := hd.hz.conj y
  have hKyΩ : conjSub y K ∈ Ω[R] := hinv y K hd.mem
  obtain ⟨m, hm, hmK⟩ := ae6_conj_of_mem_DSet H hKyΩ (ae6_mem_DSet hP h2g H.hW hτW hKyΩ hKy)
  obtain ⟨r, hr, hrτ⟩ := ae6_exists_r H fr
  have hKM : K ≤ MGrp Ω[R] W := le_iSup₂_of_le K H.hK le_rfl
  have hrM : r ∈ MGrp Ω[R] W := hKM hr
  have hJτ : IsUniqueInvolution (conjSub m K) (y * t * y⁻¹) := hmK ▸ hKy
  have hJtτ : IsUniqueInvolution (conjSub (r * m) K) (t * (y * t * y⁻¹)) := by
    rw [conjSub_mul, hmK]
    have h1 := hKy.conj r
    rwa [hrτ] at h1
  have hPΩ : ∀ J ∈ ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K, J ∈ Ω[R] := by
    rintro J ⟨g, -, rfl⟩
    exact hinv g K hd.mem
  have hMI : MGrp Ω[R] W ≤ ae6I Ω[R] W (u₁ * u₂) := le_sup_left
  have hv := ae6Vertex_of_ident hPar A hker (fun J hJ => A6h1.ae6_card8 H J (hPΩ J hJ))
    (fun J hJ => Sec6Gen.exists_uniqueInvolution hΩ (hPΩ J hJ))
    (⟨1, (ae6I Ω[R] W (u₁ * u₂)).one_mem, conjSub_one K⟩ :
      K ∈ ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K)
    (⟨m, hMI hm, rfl⟩ : conjSub m K ∈ ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K)
    (⟨r * m, (ae6I Ω[R] W (u₁ * u₂)).mul_mem (hMI hrM) (hMI hm), rfl⟩ :
      conjSub (r * m) K ∈ ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K)
    hd.hz hJτ hJtτ
  rwa [hspan] at hv

end Vert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
