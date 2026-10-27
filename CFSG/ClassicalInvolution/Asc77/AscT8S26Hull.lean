module

public import CFSG.ClassicalInvolution.Asc77.AscT8Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Hull

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem s26_le_sigmaNorm_of_mem_dComp (hΩ : ConjInvariant Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) : M ≤ sigmaNorm Ω K := fun _ hx =>
  T8.normalizer_le_sigmaNorm_of_mem hΩ hK hM (Subgroup.le_normalizer hx)

theorem s26_kPerp_subset_dComp {K M : Subgroup G} (hM : M ∈ KPerp Ω K) (hK : K ∈ Ω) :
    M ∈ dComp Ω K := by
  rcases hM with rfl | hM
  · exact Relation.ReflTransGen.refl
  · exact T8.mem_dComp_of_mem_omegaNbr hM

theorem s26_kPerp_subset_dComp_of_mem {K J M : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ dComp Ω K)
    (hM : M ∈ KPerp Ω J) : M ∈ dComp Ω K := by
  have hJΩ : J ∈ Ω := by
    rcases Relation.ReflTransGen.cases_tail hJ with rfl | ⟨_, _, h⟩
    · exact hK
    · exact h.1
  rw [← T8.dComp_eq_of_mem hK hJ]
  exact s26_kPerp_subset_dComp hM hJΩ

theorem s26_hull_le_sigmaNorm (hΩ : ConjInvariant Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaNbr Ω K) :
    (⨆ M ∈ KPerp Ω K, M) ⊔ (⨆ M ∈ KPerp Ω J, M) ≤ sigmaNorm Ω K := by
  refine sup_le (iSup₂_le fun M hM => ?_) (iSup₂_le fun M hM => ?_)
  · exact s26_le_sigmaNorm_of_mem_dComp hΩ hK (s26_kPerp_subset_dComp hM hK)
  · exact s26_le_sigmaNorm_of_mem_dComp hΩ hK
      (s26_kPerp_subset_dComp_of_mem hK (T8.mem_dComp_of_mem_omegaNbr hJ) hM)

end Hull

variable {p f : ℕ} [Fact p.Prime]

theorem c26_7_of_c26_6 (h6 : C26_6 p f) : C26_7 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hE4 hL5
  have hK : K ∈ Ω := hs.stand.mem
  have hle := s26_hull_le_sigmaNorm hs.stand.hyp.conjInvariant hK hs.hJ
  rw [h6 G Ω K J S R T W z t hs hE4 hL5, top_le_iff] at hle
  exact dConnected_of_sigmaNorm_eq_top hK hs.stand.trans hle

end CFSG.ClassicalInvolution.Asc77
