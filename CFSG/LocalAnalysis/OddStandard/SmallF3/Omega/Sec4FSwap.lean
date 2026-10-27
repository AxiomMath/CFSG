module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCBrConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FType

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4F_pair_data [Finite G] (hD : Asc82FactD) (hABC : Asc82ClaimsABC) {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z) {g : G}
    (hgc : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hg6 : InducesTypeSome L (g⁻¹ * t * g) 7 1 6 1) :
    InducesTypeSome (CFSG.conjugate L g) t 7 1 6 1 ∧
      L ⊓ centralizer ({g⁻¹ * t * g} : Set G) ≤ (L ⊓ CFSG.conjugate L g) ⊔ Sec4FOdd L ∧
      CFSG.conjugate L g ⊓ centralizer ({t} : Set G) ≤
        (L ⊓ CFSG.conjugate L g) ⊔ Sec4FOdd (CFSG.conjugate L g) ∧
      Sec4FDConcl L (g⁻¹ * t * g) (L ⊓ CFSG.conjugate L g) ∧
      Sec4FDConcl (CFSG.conjugate L g) t (L ⊓ CFSG.conjugate L g) := by
  obtain ⟨hB, hC1, hC2⟩ := hABC G t L S z hctx g hgc hg6
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hL' : IsOmega7Group (CFSG.conjugate L g) :=
    sec4_isOmega7Group (hctx.conjugate g).toSec4Setting
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [orderOf_conjugate_eq, hctx.involution]
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer hctx.toSec3Setting
  refine ⟨hB, hC1, hC2, ?_, ?_⟩
  · exact Sec4FDConcl.of_oddCent (sec4FC_inf_conjugate_le_left htC g) hC1
      (sec4FC_oddCent_odd hL inf_le_left) (Asc82FactD.apply hD hL hs2 hg6)
  · exact Sec4FDConcl.of_oddCent (sec4FC_inf_conjugate_le_right htC g) hC2
      (sec4FC_oddCent_odd hL' inf_le_left) (Asc82FactD.apply hD hL' hctx.involution hB)

theorem sec4_frame_swap [Finite G] (h39 : Asc82Lemma39) (hk6 : Asc82FactK6) (hD : Asc82FactD)
    (hABC : Asc82ClaimsABC) {t : G} {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z) {g : G}
    (hgc : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hg6 : InducesTypeSome L (g⁻¹ * t * g) 7 1 6 1) {v : G}
    (hv : Asc82SetU (L ⊓ CFSG.conjugate L g) v) :
    InducesTypeSome L v 7 1 2 (-1) ↔ InducesTypeSome (CFSG.conjugate L g) v 7 1 6 (-1) := by
  obtain ⟨hB, hC1, hC2, hFx, hFy⟩ := sec4F_pair_data hD hABC hctx hgc hg6
  have hL' : IsOmega7Group (CFSG.conjugate L g) :=
    sec4_isOmega7Group (hctx.conjugate g).toSec4Setting
  have stepB : ∀ w, Asc82SetU (L ⊓ CFSG.conjugate L g) w →
      InducesTypeSome (CFSG.conjugate L g) w 7 1 6 (-1) →
      InducesTypeSome L w 7 1 2 (-1) := by
    intro w hw h6'
    rcases hFx.1 w hw with h2 | h6
    · exact h2
    · exact (sec4_frame_lemma h39 hk6 hctx hg6 hw.1.1 hw.1.2 hw.2.1 h6 h6').elim
  refine ⟨?_, stepB v hv⟩
  intro h2
  obtain ⟨v₀, hv0, h6v0⟩ := hFy.2.2.2.1
  have h2v0 : InducesTypeSome L v₀ 7 1 2 (-1) := stepB v₀ hv0 h6v0
  have hconj : v ∈ conjClassIn (L ⊓ CFSG.conjugate L g) v₀ :=
    hFx.2.1 v₀ v hv0 hv (Or.inl ⟨h2v0, h2⟩)
  obtain ⟨d, hdD, hdv⟩ := hconj
  have hdL' : d ∈ CFSG.conjugate L g := hdD.2
  have hnorm : d ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => (CFSG.conjugate L g).mul_mem
        ((CFSG.conjugate L g).mul_mem hdL' hh) ((CFSG.conjugate L g).inv_mem hdL'), ?_⟩
    intro hh
    have h2 : d⁻¹ * (d * h * d⁻¹) * d ∈ CFSG.conjugate L g :=
      (CFSG.conjugate L g).mul_mem
        ((CFSG.conjugate L g).mul_mem ((CFSG.conjugate L g).inv_mem hdL') hh) hdL'
    rwa [show d⁻¹ * (d * h * d⁻¹) * d = h by group] at h2
  rw [hdv]
  exact sec4F_type_conj_norm hL' hnorm (Or.inr (Or.inr rfl)) h6v0

end CFSG.OddStandard.SmallF3.Omega
