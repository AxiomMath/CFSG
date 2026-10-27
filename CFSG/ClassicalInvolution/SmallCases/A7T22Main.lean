module

public import CFSG.ClassicalInvolution.SmallCases.A7T22Const
public import CFSG.ClassicalInvolution.Asc77.AscT7JCent

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem omegaNbr_subset_kPerp_of_twin (hΩ : HypOmegaGen Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) :
    omegaNbr Ω K ⊆ KPerp Ω L := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  by_cases hJL : J = L
  · exact Set.mem_insert_iff.mpr (Or.inl hJL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hJ, hJL, R, hR, hRJ, ?_⟩)
    obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    exact Sec6Gen.le_normalizer_of_le_centralizer hΩ hL hJ (Ne.symm hJL) hzL hRJ hRJ'.2.1
      (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hR; omega)
      (le_centralizer_of_le_normalizer hzK hRN)

theorem mem_kPerp_of_twin (hΩ : HypOmegaGen Ω) {L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) : K ∈ KPerp Ω L := by
  by_cases hKL : K = L
  · exact Set.mem_insert_iff.mpr (Or.inl hKL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hK, hKL, ?_⟩)
    obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
    exact ⟨R, hR, hRK.1, fun x hx =>
      Sec6Gen.le_normalizer_of_twin hΩ hK hL hKL hzK hzL (hRK.1 hx)⟩

theorem kPerp_eq_of_twin (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) {L : Subgroup G}
    (hL : L ∈ twinSet Ω K) : KPerp Ω L = KPerp Ω K := by
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  apply Set.Subset.antisymm
  · exact Set.insert_subset (mem_kPerp_of_twin hΩ hLΩ hK hzL hzK)
      (omegaNbr_subset_kPerp_of_twin hΩ hK hzL hzK)
  · exact Set.insert_subset (mem_kPerp_of_twin hΩ hK hLΩ hzK hzL)
      (omegaNbr_subset_kPerp_of_twin hΩ hLΩ hzK hzL)

namespace Hyp22G

omit [Finite G] in
theorem exists_centralizer_conj (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (htr : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) {J : Subgroup G} (hJ : J ∈ twinSet Ω K) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K = J := by
  obtain ⟨g, hg⟩ := htr J hJ.1
  have hzJ : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.hz hJ
  have h1 : IsUniqueInvolution J (g * z * g⁻¹) := hg ▸ h.hz.conj g
  have h2 : g * z * g⁻¹ = z := h1.eq hzJ
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hg⟩
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [h2]

theorem stdCent_of_twin (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    {H : Subgroup G} (hz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H) :
    StdCent Ω K H z where
  z_le := hz
  nonTwin := by
    intro L hL J hJ z' hz' hzz
    exfalso
    have hJperp : J ∈ KPerp Ω L := Set.mem_insert_of_mem _ hJ
    rw [kPerp_eq_of_twin h.hyp h.mem hL, hperp] at hJperp
    exact hzz (hz'.eq (isUniqueInvolution_of_mem_twinSet h.hz hJperp))
  twin := htwin

theorem exists_datum_of_pair (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {L L' : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) {R₁ R₂ : Subgroup G}
    (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : G}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ (L₃ : Subgroup G) (w : G), Hyp22G Ω L L' L₃ z x y w := by
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.mem h.hz
  obtain ⟨L₃, hL₃, hL₃L, hL₃L'⟩ : ∃ L₃ ∈ twinSet Ω K, L₃ ≠ L ∧ L₃ ≠ L' := by
    rcases T7B.exists_ne_of_three (a := L) (b := L') h.hne h.hK₃K h.hK₃K' with hh | hh | hh
    · exact ⟨K, hKV, hh.1, hh.2⟩
    · exact ⟨K', h.hK', hh.1, hh.2⟩
    · exact ⟨K₃, h.hK₃, hh.1, hh.2⟩
  obtain ⟨R₃, hR₃, c₁, c₂⟩ := exists_third_sylow h.hyp hL.1 hL'.1 hL₃.1
    (isUniqueInvolution_of_mem_twinSet h.hz hL) (isUniqueInvolution_of_mem_twinSet h.hz hL')
    (isUniqueInvolution_of_mem_twinSet h.hz hL₃) hL₃L hL₃L' hR₁ hR₂ hc
  obtain ⟨w, hw, ow⟩ := exists_orderOf_eq_four_of_isSylow2In h.hyp hL₃.1 hR₃
  exact ⟨L₃, w, h.of_sylows hL hL' hL₃ hne hL₃L hL₃L' hR₁ hR₂ hR₃ hc c₁ c₂ hx hy hw ox oy ow⟩

theorem mul_ne_one (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₂ ≠ 1 := by
  intro he
  refine Hyp22Core.not_mem_of_orderOf_four h.hyp h.mem h.hK'.1 h.hne h.hu₂.2 ?_ h.hu₂.1
  rw [eq_inv_of_mul_eq_one_right he]
  exact K.inv_mem h.hu₁.1

theorem cent_of_zstar (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hzs : z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G))) :
    Subgroup.centralizer ({u₁ * u₂} : Set G) ≤
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) ⊔
        (Subgroup.centralizer ({u₁ * u₂} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hu1 : u₁ * u₂ ≠ 1 := h.mul_ne_one
  have hz2 : z * z = 1 := h.hz.sq
  obtain ⟨zh, hzh, hzhz⟩ := Subgroup.mem_map.mp hzs
  rw [Subgroup.mem_comap] at hzh
  have hzH : z ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) := by
    rw [← hzhz]
    exact zh.2
  refine T7J.le_sup_of_zstar hz2 hzH (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)
    (oddCoreOf_odd_natCard _)
    (fun h' hh' n hn =>
      CFSG.ClassicalInvolution.Balance.Bootstrap.conj_mem_oddCoreIn_of_mem_normalizer
        (Subgroup.le_normalizer hh') hn) (fun g hg => ?_) ?_
  · have hc := Subgroup.mem_center_iff.mp hzh (QuotientGroup.mk' _ ⟨g, hg⟩)
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer
        ({u₁ * u₂} : Set G))) (⟨g, hg⟩ * zh * ⟨g, hg⟩⁻¹ * zh⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine ⟨_, h1, ?_⟩
    simp [commutatorElement_def, ← hzhz]
  · have hu_mem : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hz_mem : z ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
      Subgroup.subset_closure (by simp)
    refine le_trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hz_mem)) ?_
    unfold alphaOf
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le (u₁ * u₂) hu_mem
      (le_iSup (fun _ : u₁ * u₂ ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)),
        Subgroup.closure ({u₁ * u₂, z} : Set G)⁆) hu1)

end Hyp22G

end CFSG.ClassicalInvolution.A7T22
