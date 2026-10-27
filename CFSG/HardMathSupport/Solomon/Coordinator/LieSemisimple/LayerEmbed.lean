module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open

variable {S G : Type*} [Group S] [Group G]

theorem isSubnormal_comap_of_injective (ι : S →* G) (hι : Function.Injective ι)
    {H K : Subgroup G} (hK : K ≤ ι.range) (h : IsSubnormal H K) :
    IsSubnormal (H.comap ι) (K.comap ι) := by
  clear hι
  revert hK
  induction h with
  | refl H' =>
    intro _
    exact CFSG.Open.IsSubnormal.refl _
  | @step H' M K' hle hnormal _ ih =>
    intro hK
    have hle' : H'.comap ι ≤ M.comap ι := Subgroup.comap_mono hle
    have hn : ((H'.comap ι).subgroupOf (M.comap ι)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle']
      rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
      intro h1 k hh hk
      rw [Subgroup.mem_comap] at hh hk ⊢
      rw [map_mul, map_mul, map_inv]
      exact hnormal (ι h1) (ι k) hh hk
    exact CFSG.Open.IsSubnormal.step hle' hn (ih hK)

theorem glaLayer_map_le_of_injective (ι : S →* G) (hι : Function.Injective ι) (F : Subgroup S) :
    GLALayer (F.map ι) ≤ (GLALayer F).map ι := by
  unfold GLALayer
  refine sSup_le fun L hL => ?_
  have hL0 : IsComponentOf L (F.map ι) := hL
  obtain ⟨hLK, hsub, hq⟩ := hL0
  have hFr : F.map ι ≤ ι.range := Subgroup.map_le_range ι F
  have hLr : L ≤ ι.range := hLK.trans hFr
  have hLmap : (L.comap ι).map ι = L := Subgroup.map_comap_eq_self hLr
  have hcomapF : (F.map ι).comap ι = F := Subgroup.comap_map_eq_self_of_injective hι F
  have hLF : L.comap ι ≤ F := by
    have h1 : L.comap ι ≤ (F.map ι).comap ι := Subgroup.comap_mono hLK
    rwa [hcomapF] at h1
  have hsubF : CFSG.Open.IsSubnormal (L.comap ι) F := by
    have h1 := isSubnormal_comap_of_injective ι hι hFr hsub
    rwa [hcomapF] at h1
  have e : ↥(L.comap ι) ≃* ↥L :=
    (Subgroup.equivMapOfInjective (L.comap ι) ι hι).trans (MulEquiv.subgroupCongr hLmap)
  have hqF : CFSG.Open.IsQuasisimple ↥(L.comap ι) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq
  have hcomp : IsComponentOf (L.comap ι) F := ⟨hLF, hsubF, hqF⟩
  have hmem : L.comap ι ∈ {K : Subgroup S | IsComponentOf K F} := hcomp
  calc L = (L.comap ι).map ι := hLmap.symm
    _ ≤ (sSup {K : Subgroup S | IsComponentOf K F}).map ι :=
      Subgroup.map_mono (le_sSup hmem)

theorem perfectInLayer_of_embedding (ι : S →* G) (hι : Function.Injective ι) (β : MulAut S)
    (y : G) (hy : ∀ s, ι (β s) = y * ι s * y⁻¹)
    (h : ∀ P : Subgroup G, P ≤ ι.range ⊓ Subgroup.centralizer {y} → ⁅P, P⁆ = P →
      P ≤ GLALayer (ι.range ⊓ Subgroup.centralizer {y})) :
    PerfectInLayer β := by
  have hfix : (fixSubgroup β).map ι = ι.range ⊓ Subgroup.centralizer {y} := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      have hβs : β s = s := mem_fixSubgroup.1 hs
      have h1 : ι s = y * ι s * y⁻¹ := by rw [← hy s, hβs]
      have hcomm : ι s * y = y * ι s := by
        calc ι s * y = (y * ι s * y⁻¹) * y := by rw [← h1]
          _ = y * ι s := inv_mul_cancel_right _ _
      exact Subgroup.mem_inf.2
        ⟨MonoidHom.mem_range.2 ⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    · intro x hx
      obtain ⟨hr, hc⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hr
      have hcomm : ι s * y = y * ι s := Subgroup.mem_centralizer_singleton_iff.1 hc
      refine Subgroup.mem_map.2 ⟨s, ?_, rfl⟩
      rw [mem_fixSubgroup]
      apply hι
      rw [hy s, ← hcomm, mul_inv_cancel_right]
  intro P hP hperf
  have hPmap : P.map ι ≤ ι.range ⊓ Subgroup.centralizer {y} := by
    rw [← hfix]
    exact Subgroup.map_mono hP
  have hperf' : ⁅P.map ι, P.map ι⁆ = P.map ι := by
    rw [← Subgroup.map_commutator, hperf]
  have h2 : P.map ι ≤ GLALayer (ι.range ⊓ Subgroup.centralizer {y}) :=
    h (P.map ι) hPmap hperf'
  rw [← hfix] at h2
  have h3 : P.map ι ≤ (GLALayer (fixSubgroup β)).map ι :=
    h2.trans (glaLayer_map_le_of_injective ι hι (fixSubgroup β))
  exact (Subgroup.map_le_map_iff_of_injective hι).1 h3

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
