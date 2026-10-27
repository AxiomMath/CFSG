module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem l44_decomp {Y : Type*} [Group Y] (L : Subgroup Y) [L.Normal]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) = 1) (y : Y) :
    ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set Y), y = ℓ * d := by
  have hsub : Subsingleton (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) :=
    (Nat.card_eq_one_iff_unique.mp hout).1
  have h1 : MulAut.conjNormal (H := L) y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥L :=
    (QuotientGroup.eq_one_iff _).mp (hsub.elim
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)
        (MulAut.conjNormal (H := L) y)) 1)
  obtain ⟨ℓ, hℓ⟩ := h1
  refine ⟨ℓ, ℓ.2, (ℓ : Y)⁻¹ * y, ?_, by group⟩
  rw [mem_centralizer_iff]
  intro m hm
  have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨m, hm⟩ : ↥L) : Y)) hℓ
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    at h2
  calc m * ((ℓ : Y)⁻¹ * y) = (ℓ : Y)⁻¹ * ((ℓ : Y) * m * (ℓ : Y)⁻¹) * y := by group
    _ = (ℓ : Y)⁻¹ * (y * m * y⁻¹) * y := by rw [h2]
    _ = (ℓ : Y)⁻¹ * y * m := by group

theorem l44_nonempty_mulEquiv_map {G : Type} [Group G] [Finite G] {C J : Subgroup G}
    (hJC : J ≤ C) (hCJ : C ≤ normalizer (J : Set G)) {Q : Type} [Group Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 3 J).subgroupOf J) :
    Nonempty
      (↥((J.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3))) ≃* Q) := by
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  let f : ↥J →* C ⧸ O := (QuotientGroup.mk' O).comp (Subgroup.inclusion hJC)
  have hrange : f.range = (J.subgroupOf C).map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkerf : f.ker = ψ.ker := by
    ext j
    rw [hker, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk' O (Subgroup.inclusion hJC j) = 1 ↔ _
    rw [CFSG.AGLEmbedding.mk'_primeComplementCore_eq_one_iff]
    change (j : G) ∈ GLBPrimeCore 3 C ↔ (j : G) ∈ GLBPrimeCore 3 J
    rw [CFSG.AGLEmbedding.glbPrimeCore_eq_inf_of_le_normalizer 3 hJC hCJ]
    exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
  let e1 : ↥f.range ≃* Q :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerf).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans e1⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
