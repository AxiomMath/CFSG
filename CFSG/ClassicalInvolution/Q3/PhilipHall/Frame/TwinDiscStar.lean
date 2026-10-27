module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc



section Star

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_omegaStarNbr_gen (hΩ : HypOmegaGen Ω) (K : Subgroup G) :
    omegaNbr Ω K ⊆ omegaStarNbr Ω K := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  obtain ⟨U, hUR, hUc, hcard⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_cyclic_index_two
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    have hU0 : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  exact ⟨hJ, hJK, U, ⟨R, hR, hUR, hUc, hrel⟩, hUR.trans hRJ, hUR.trans hRN⟩

theorem mem_dstarComp_of_twin_gen (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ twinSet Ω K) : L ∈ dstarComp Ω K := by
  by_cases hLK : L = K
  · rw [hLK]
    exact Relation.ReflTransGen.refl
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  exact Relation.ReflTransGen.single ⟨hLΩ, Or.inl
    (omegaNbr_subset_omegaStarNbr_gen hΩ K
      (Q3.Q3CL.T3.twin_mem_omegaNbr hΩ hK hLΩ hLK hzK hzL))⟩

theorem mem_dstarComp_of_mem_dComp_gen (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hJ : J ∈ dComp Ω K) : J ∈ dstarComp Ω K := by
  induction hJ with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨hbc.1, ?_⟩
    rcases hbc.2 with h | h
    · exact Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩ _ h)
    · exact Or.inr (omegaNbr_subset_omegaStarNbr_gen hΩ _ h)

theorem mem_sigmaStarNorm_of_mem_sup_gen (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {g : G} (hg : g ∈ K ⊔ K') : g ∈ sigmaStarNorm Ω K := by
  have hgK : conjSub g K = K := mem_normalizer_iff_conjSub_eq.mp
    ((sup_le Subgroup.le_normalizer (Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz)) hg)
  exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
    (by rw [hgK]; exact Relation.ReflTransGen.refl)

theorem stdCent_sigmaStarNorm_gen (hΩ : HypOmegaGen Ω) {K : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M)
    (htail : StdCentTail Ω K (sigmaStarNorm Ω K) z) : StdCent Ω K (sigmaStarNorm Ω K) z := by
  have hz_le : Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
    intro c hc
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
        _ = z := by group
    have hL : conjSub c K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant c K hK, z, hz, hcz ▸ hz.conj c⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (mem_dstarComp_of_twin_gen hΩ hK hL)
  refine ⟨hz_le, ?_, htail.twin⟩
  intro L hL J hJ z' hz' hzz
  have hKL := A7Q.Gen.kPerp_eq_of_twin hΩ hK hL
  have hJperp : J ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ
  have hnot : J ∉ twinSet Ω K := by
    rintro ⟨-, z₀, hz₀K, hz₀J⟩
    exact hzz ((hz₀J.eq hz').symm.trans (hz.eq hz₀K).symm)
  have hJΩ : J ∈ Ω := hJ.1
  have hJd : J ∈ dstarComp Ω K := by
    rcases Set.mem_insert_iff.mp hJperp with h | h
    · exact absurd (by rw [h]; exact mem_twinSet_self hK hz) hnot
    · exact Relation.ReflTransGen.single ⟨hJΩ, Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩ K h)⟩
  obtain ⟨y, hy⟩ := htrans J hJΩ
  have hyH : y ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hy ▸ hJd)
  have hzy : IsUniqueInvolution J (y * z * y⁻¹) := hy ▸ hz.conj y
  exact ⟨T7A.centralizer_conj_le hyH (hz'.eq hzy) hz_le, htail.nonTwin L hL J hJ z' hz' hzz⟩

theorem stdCentTail_of_frames_gen (hΩ : HypOmegaGen Ω) {K K' J W : Subgroup G} {z u t : G}
    (h : Data Ω K K' z u J t W)
    (hfr : ∀ {L L' J₁ W₁ : Subgroup G} {u₁ t₁ : G}, L ∈ twinSet Ω K →
      Data Ω L L' z u₁ J₁ t₁ W₁ →
        Subgroup.centralizer ({t₁ * z} : Set G) ≤ sigmaStarNorm Ω L ∧
          Subgroup.centralizer ({u₁} : Set G) ≤ sigmaStarNorm Ω L) :
    StdCentTail Ω K (sigmaStarNorm Ω K) z := by
  have hf := h.frame
  have hK : K ∈ Ω := hf.mem
  have hK'Ω : K' ∈ Ω := hf.hK'.1
  have hzK' := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  have hKK : K ∈ twinSet Ω K := mem_twinSet_self hK hf.hz
  have hstar : ∀ {L : Subgroup G}, L ∈ twinSet Ω K → sigmaStarNorm Ω L = sigmaStarNorm Ω K :=
    fun {L} hL => sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK
      (mem_dstarComp_of_twin_gen hΩ hK hL))
  refine ⟨?_, ?_⟩
  · intro L hL J'' hJ'' z'' hz'' hzz
    have hKL := A7Q.Gen.kPerp_eq_of_twin hΩ hK hL
    have hJperp : J'' ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ''
    have hnot : J'' ∉ twinSet Ω K := by
      rintro ⟨-, z₀, hz₀K, hz₀J⟩
      exact hzz ((hz₀J.eq hz'').symm.trans (hf.hz.eq hz₀K).symm)
    have hJmem : J'' ∈ omegaOfSet Ω (twinSet Ω K) :=
      A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hK hJperp hnot
    obtain ⟨g, hgQ, W₁, hfr', hW₁, hzW₁, htW₁⟩ :=
      Hat2A7S.exists_twinFrameData_at hΩ hK hf.hz hf.hK' hf.hne hf.hu hf.hu2 hf.hu1 hf.huz
        hJmem hz''
    have h' : Data Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ := ⟨hfr', hW₁, hzW₁, htW₁⟩
    have hcl := (hfr hKK h').1
    have hgH : g ∈ sigmaStarNorm Ω K :=
      mem_sigmaStarNorm_of_mem_sup_gen hΩ hK hK'Ω hf.hne hf.hz hzK' hgQ
    have hgz : g * z * g⁻¹ = z := by
      have := T7A.z_comm_of_mem_sup hf.hz hzK' hgQ
      calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
        _ = (z * g) * g⁻¹ := by rw [← this]
        _ = z := by group
    have hcomm : z * (g * z'' * g⁻¹) = (g * z'' * g⁻¹) * z := A7Q.Gen.comm_zt hΩ hfr'
    have e1 : (g * z'' * g⁻¹) * z = g * (z * z'') * g⁻¹ := by
      calc (g * z'' * g⁻¹) * z = z * (g * z'' * g⁻¹) := hcomm.symm
        _ = (g * z * g⁻¹) * (g * z'' * g⁻¹) := by rw [hgz]
        _ = g * (z * z'') * g⁻¹ := by group
    intro c hc
    refine T7A.mem_of_conj_mem hgH ?_
    have hc' := T7A.mem_centralizer_conj (g := g) hc
    rw [← e1] at hc'
    exact hcl hc'
  · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
    have hLΩ : L ∈ Ω := hL.1
    have hzL := isUniqueInvolution_of_mem_twinSet hf.hz hL
    have htwL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet hf.hz hL
    have hL'L : L' ∈ twinSet Ω L := by rw [htwL]; exact hL'
    have hJL : J ∈ omegaOfSet Ω (twinSet Ω L) := by rw [htwL]; exact hf.hJ
    obtain ⟨g, hgQ, W₂, hJg, htg, hW₂, hzW₂, htW₂, hfr'⟩ :=
      Hat2A7S.exists_twinFrameData_of_sylows hΩ hLΩ hzL hL'L hne hJL hf.ht hR₁ hR₂ hc
    have hfr'' := hfr' x hx y hy hx4 hy4
    have h' : Data Ω L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ := ⟨hfr'', hW₂, hzW₂, htW₂⟩
    have := (hfr hL h').2
    rwa [hstar hL] at this

end Star

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
