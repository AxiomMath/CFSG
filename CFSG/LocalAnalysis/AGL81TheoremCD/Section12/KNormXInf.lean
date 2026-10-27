module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {M H : Subgroup G} {p : ℕ}

theorem kSub_le_normalizer_xSub_inf (hp : p.Prime)
    (hOp : CFSG.Open.relPPrimeCore p H ≤ M) :
    kSub p M H ≤ Subgroup.normalizer (xSub p M H ⊓ M : Set G) := by
  rw [show (xSub p M H ⊓ M : Set G) =
      ((xSub p M H ⊓ M : Subgroup G) : Set G) from (Subgroup.coe_inf _ _).symm]
  rw [Subgroup.le_normalizer_iff]
  intro k hk x hx
  have hkH : k ∈ H := kSub_le p M H hk
  have hxM : x ∈ M := hx.2
  obtain ⟨xH, hxHcent, rfl⟩ := Subgroup.mem_map.mp (show x ∈
    CFSG.AGLEmbedding.d1PlusCore p H (kStar p M H) from hx.1)
  let kH : ↥H := ⟨k, hkH⟩
  set π : ↥H →* (↥H ⧸ primeComplementCore (G := ↥H) p) :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p) with hπ
  have hkKstar : π kH ∈ kStar p M H := by
    refine Subgroup.mem_map.mpr ⟨kH, ?_, rfl⟩
    change (kH : G) ∈ kSub p M H
    simpa [kH] using hk
  have hxCent : π xH ∈ Subgroup.centralizer
      ((kStar p M H : Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
        Set (↥H ⧸ primeComplementCore (G := ↥H) p)) :=
    Subgroup.mem_comap.mp hxHcent
  have hcomm : π kH * π xH = π xH * π kH :=
    (Subgroup.mem_centralizer_iff.mp hxCent) (π kH) hkKstar
  have hconj : π (kH * xH * kH⁻¹) = π xH := by
    rw [map_mul, map_mul, map_inv]
    calc
      π kH * π xH * (π kH)⁻¹ = (π xH * π kH) * (π kH)⁻¹ := by rw [hcomm]
      _ = π xH := by group
  have hmemX : k * ↑xH * k⁻¹ ∈ xSub p M H := by
    have h : ((kH * xH * kH⁻¹ : ↥H) : G) ∈
        CFSG.AGLEmbedding.d1PlusCore p H (kStar p M H) := by
      refine Subgroup.mem_map.mpr ⟨kH * xH * kH⁻¹, ?_, rfl⟩
      exact Subgroup.mem_comap.mpr (hconj ▸ hxCent)
    simpa [xSub, kH] using h
  have hzker : π (xH⁻¹ * (kH * xH * kH⁻¹)) = 1 := by
    rw [map_mul, hconj, map_inv]
    exact inv_mul_cancel (π xH)
  have hzO : xH⁻¹ * (kH * xH * kH⁻¹) ∈
      primeComplementCore (G := ↥H) p :=
    (QuotientGroup.eq_one_iff (N := primeComplementCore (G := ↥H) p) _).mp hzker
  have hzRel : ((xH⁻¹ * (kH * xH * kH⁻¹) : ↥H) : G) ∈
      CFSG.Open.relPPrimeCore p H := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      hp H]
    exact Subgroup.mem_map.mpr ⟨_, hzO, rfl⟩
  have hzM : ((xH⁻¹ * (kH * xH * kH⁻¹) : ↥H) : G) ∈ M := hOp hzRel
  have hkxM : k * ↑xH * k⁻¹ ∈ M := by
    have hdecomp : k * ↑xH * k⁻¹ =
        ↑xH * ((xH⁻¹ * (kH * xH * kH⁻¹) : ↥H) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, kH]
      group
    rw [hdecomp]
    exact M.mul_mem hxM hzM
  exact ⟨hmemX, hkxM⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
