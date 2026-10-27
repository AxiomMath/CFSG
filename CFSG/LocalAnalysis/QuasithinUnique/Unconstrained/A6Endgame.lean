module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsData
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section Endgame

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

theorem Notation25.SK0_eq (hK0 : N.K0 = N.K) : N.SK0 = N.SK := by
  unfold Notation25.SK0 Notation25.SK
  rw [hK0]

theorem Notation25.zK_unique (h258 : Facts258 N) {z₁ z₂ : G} (h1 : z₁ ∈ N.K0)
    (h1' : z₁⁻¹ * N.z ∈ N.SC) (h2 : z₂ ∈ N.K0) (h2' : z₂⁻¹ * N.z ∈ N.SC) : z₁ = z₂ := by
  have hmem : z₁⁻¹ * z₂ ∈ N.K0 ⊓ N.SC := by
    refine ⟨N.K0.mul_mem (N.K0.inv_mem h1) h2, ?_⟩
    have := N.SC.mul_mem h1' (N.SC.inv_mem h2')
    simpa [mul_assoc] using this
  rw [h258.K0_inf_SC, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

variable {N}

theorem Facts2511.zK_sq {t zK : G} (h : Facts2511 N t zK) : zK * zK = 1 := by
  have hz : zK ∈ centerOf N.S := by
    rw [h.centerS_zK]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have := h.centerS_E4.1.2 zK hz
  rwa [sq] at this

theorem Facts2511.zK_mem_center {t zK : G} (h : Facts2511 N t zK) : zK ∈ centerOf N.S := by
  rw [h.centerS_zK]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem Facts2511.t_mem_center {t zK : G} (h : Facts2511 N t zK) : t ∈ centerOf N.S := by
  rw [h.centerS_zK]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem Facts2511.t_mul_t {t zK : G} (h : Facts2511 N t zK) : t * t = 1 := by
  have := h.t_sq
  rwa [sq] at this

theorem Facts2511.t_mul_zK {t zK : G} (h : Facts2511 N t zK) : t * zK = zK * t :=
  (Subgroup.mem_centralizer_iff.mp h.t_mem_center.2 zK h.zK_mem_center.1).symm

theorem Facts2511.zK_mem_SK {t zK : G} (h : Facts2511 N t zK) (hK0 : N.K0 = N.K) :
    zK ∈ N.SK := ⟨h.zK_mem_center.1, hK0 ▸ h.zK_mem⟩

theorem Notation25.center_inf_SK_eq (hK0 : N.K0 = N.K) (h258 : Facts258 N) {t zK : G}
    (h : Facts2511 N t zK) : centerOf N.S ⊓ N.SK = Subgroup.zpowers zK := by
  obtain ⟨zK', hzK'0, hzK'proj, hcen, -⟩ := h258.zK_exists
  have : zK = zK' := Notation25.zK_unique N h258 h.zK_mem h.zK_proj hzK'0 hzK'proj
  rw [← N.SK0_eq hK0, hcen, this]

theorem Notation25.z_cases (h254 : Facts254 N) {t zK : G} (h : Facts2511 N t zK) :
    N.z = zK ∨ N.z = t * zK := by
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) hzT.2⟩
  rw [h.centerS_zK] at hzS
  rcases mem_closure_pair_of_involutions h.t_mul_t h.zK_sq h.t_mul_zK hzS with h1 | h1 | h1 | h1
  · exact absurd h1 N.tuple.z_ne_one
  · exact absurd (h1 ▸ h.t_mem) h254.z_not_mem
  · exact Or.inl h1
  · exact Or.inr h1

theorem Notation25.S_le_normalizer_SK (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) :
    N.S ≤ Subgroup.normalizer (N.SK : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
    Subgroup.le_normalizer (N.S_le_normalizer_K hKH)

theorem Notation25.S_le_normalizer_SK_inf (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    {A : Subgroup G} (hA : N.S ≤ Subgroup.normalizer (A : Set G)) :
    N.S ≤ Subgroup.normalizer ((N.SK ⊓ A : Subgroup G) : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
    (N.S_le_normalizer_SK hKH) hA

theorem Notation25.SK_inf_conjugate_SC {t zK : G} (hK0 : N.K0 = N.K)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h254 : Facts254 N) (h258 : Facts258 N)
    (hf : Facts2511 N t zK) (hzK : N.z = zK) :
    N.SK ⊓ CFSG.conjugate N.SC N.x = ⊥ := by
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hxz : N.x⁻¹ * N.z * N.x = N.z := by
    have hc : N.x * N.z = N.z * N.x :=
      Subgroup.mem_centralizer_iff.mp N.tuple.z_mem.2 N.x N.x_mem.1
    calc N.x⁻¹ * N.z * N.x = N.x⁻¹ * (N.z * N.x) := mul_assoc _ _ _
      _ = N.x⁻¹ * (N.x * N.z) := by rw [hc]
      _ = N.z := inv_mul_cancel_left _ _
  by_contra hne
  have hWS : N.SK ⊓ CFSG.conjugate N.SC N.x ≤ N.S := inf_le_left.trans N.SK_le_S
  have hSW := N.S_le_normalizer_SK_inf hKH N.S_le_normalizer_conjugate_SC
  have hne' := inf_centralizer_ne_bot_of_normalizes hS2 hWS hSW hne
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
  have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
  have hwS : w ∈ N.S := hWS hw.1
  have hwZ : w ∈ centerOf N.S ⊓ N.SK := ⟨⟨hwS, hw.2⟩, hw.1.1⟩
  rw [N.center_inf_SK_eq hK0 h258 hf] at hwZ
  rcases mem_zpowers_involution hf.zK_sq hwZ with h1 | h1
  · exact hw1' h1
  · have hwx : w ∈ CFSG.conjugate N.SC N.x := hw.1.2
    rw [mem_conjugate_iff, h1, ← hzK] at hwx
    have : N.x * N.z * N.x⁻¹ = N.z := by
      calc N.x * N.z * N.x⁻¹ = N.x * (N.x⁻¹ * N.z * N.x) * N.x⁻¹ := by rw [hxz]
        _ = N.z := by group
    rw [this] at hwx
    exact h254.z_not_mem hwx

end Endgame

end CFSG.QuasithinUnique
