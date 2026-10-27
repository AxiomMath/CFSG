module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aComp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec123_comp' [Finite G] {t s : G} {L : Subgroup G} (h36 : Asc82Lemma36)
    (h63 : Asc82Lemma63) (hH : Asc82Hyp62 G) (hS : Sec3SettingLB G t L)
    (hs : orderOf s = 2) (hts : t * s = s * t)
    (hJ : IsComponentIn (layerCent L s) (L ⊓ centralizer ({s} : Set G)))
    (hJ29 : IsL29 (layerCent L s)) :
    ∃ I : Subgroup G, IsComponentIn I (centralizer ({s} : Set G)) ∧ InFStar I ∧
      centralizer ({s} : Set G) ≤ normalizer (I : Set G) ∧ layerCent L s ≤ I := by
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hJ2 : IsComponentIn (layerCent L s) (centralizer ({t, s} : Set G)) := by
    rw [centralizer_pair_eq_inf]
    exact IsComponentIn.of_normal_inf_centralizer hLt hnorm hJ
  have hJF : InFStar (layerCent L s) := sec123_inFStar_of_isL29 hJ.isQuasisimple hJ29
  obtain ⟨K, hK, hle⟩ := hS.lBalance t s hS.involution hs hts _ hJ2
  have hKF : InFStar K := hS.a2 t s hS.involution hs hts _ K hJ2 hK hle hJF
  have hN : centralizer ({s} : Set G) ≤ normalizer (K : Set G) := by
    intro c hc
    have hc' : IsComponentIn (CFSG.conjugate K c) (centralizer ({s} : Set G)) :=
      hK.conjugate hc
    exact sec123_mem_normalizer_of_conjugate_eq
      (h63 G t L hS hH s hs _ _ hc' (hKF.conjugate c) hK hKF)
  have htN : t ∈ normalizer (K : Set G) := hN (Subgroup.mem_centralizer_singleton_iff.mpr hts)
  have hKt : CFSG.conjugate K t = K := by
    ext x
    have hmem : x ∈ CFSG.conjugate K t ↔ t * x * t⁻¹ ∈ K := by
      unfold CFSG.conjugate
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hk
      · intro hx
        exact ⟨t * x * t⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [hmem]
    exact ((Subgroup.mem_normalizer_iff.mp htN) x).symm
  refine ⟨K, hK, hKF, hN, ?_⟩
  rw [hKt, sup_idem] at hle
  exact hle

end CFSG.OddStandard.SmallF3.Omega
