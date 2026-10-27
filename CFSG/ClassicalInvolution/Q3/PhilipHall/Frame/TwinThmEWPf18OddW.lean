module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf18Lift
public import CFSG.ClassicalInvolution.AschTight.Sec7L713C

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace TwinThmEW

section OddW

theorem relIndex_two_of_card {G : Type} [Group G] [Finite G] {A R : Subgroup G} (hAR : A ≤ R)
    (hcard : Nat.card R = 2 * Nat.card A) : A.relIndex R = 2 :=
  Sec7.relIndex_eq_two_of_card hAR hcard

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem inf_bot_of_isPGroup (hN : Odd (Nat.card N)) {K : Subgroup G} (hK : IsPGroup 2 K) :
    K ⊓ N = ⊥ :=
  AscQuot.inf_eq_bot_of_isPGroup_of_odd N hK le_rfl (odd_natCard_inf hN K)

theorem natCard_map_of_isPGroup (hN : Odd (Nat.card N)) {K : Subgroup G} (hK : IsPGroup 2 K) :
    Nat.card ↥(K.map (QuotientGroup.mk' N)) = Nat.card K :=
  (Nat.card_congr (AscQuot.quotRestrictEquiv (inf_bot_of_isPGroup hN hK)).toEquiv).symm

theorem map_mem_USet (hN : Odd (Nat.card N)) {U : Subgroup G} (hU : U ∈ USet Ω) :
    U.map (QuotientGroup.mk' N) ∈ USet (quotFamily Ω N) := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hR2 : IsPGroup 2 R := hRJ.2.1
  have hU2 : IsPGroup 2 U := hR2.to_le hUR
  have hcard : Nat.card R = 2 * Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR] at h1
    have : U.relIndex R = 2 := hidx
    rw [this] at h1
    omega
  refine ⟨R.map (QuotientGroup.mk' N), mem_RSet_of_isSylow2In (map_mem_quotFamily hJ)
    (isSylow2In_map_mk hN hRJ), Subgroup.map_mono hUR, ?_, ?_⟩
  · exact ((AscQuot.quotRestrictEquiv (inf_bot_of_isPGroup hN hU2)).isCyclic).mp hcyc
  · refine relIndex_two_of_card (Subgroup.map_mono hUR) ?_
    rw [natCard_map_of_isPGroup hN hR2, natCard_map_of_isPGroup hN hU2, hcard]

theorem lift_USet (hΩ' : HypOmegaGen (quotFamily Ω N)) (hΩ : HypOmegaGen Ω)
    (hN : Odd (Nat.card N)) {T : Subgroup G} (hT : IsPGroup 2 T)
    {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hle : Ub ≤ T.map (QuotientGroup.mk' N)) :
    (T ⊓ Ub.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = Ub ∧
      ∃ M' ∈ Ω, T ⊓ Ub.comap (QuotientGroup.mk' N) ≤ M' ∧
        T ⊓ Ub.comap (QuotientGroup.mk' N) ∈ USet Ω := by
  set π := QuotientGroup.mk' N with hπ
  set U := T ⊓ Ub.comap π with hU
  have hmap : U.map π = Ub := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      obtain ⟨t, ht, hty⟩ := hle hy
      exact ⟨t, ⟨ht, by simpa [hty] using hy⟩, hty⟩
  refine ⟨hmap, ?_⟩
  have hU2 : IsPGroup 2 U := hT.to_le inf_le_left
  obtain ⟨Rb, hRb, hUbR, hcyc, hidx⟩ := hUb
  obtain ⟨Jb, hJb, hRbJ⟩ := exists_isSylow2In_of_mem_RSet hRb
  obtain ⟨J₀, hJ₀, rfl⟩ := hJb
  have hUle : U ≤ J₀ ⊔ N := by
    refine le_sup_of_map_le ?_
    rw [hmap]
    exact hUbR.trans hRbJ.1
  obtain ⟨n, hn, hnU⟩ := exists_conj_le_of_le_sup hN hU2 hUle
  have hM'Ω : conjSub n⁻¹ J₀ ∈ Ω := hΩ.conjInvariant _ J₀ hJ₀
  have hUM' : U ≤ conjSub n⁻¹ J₀ := by
    rw [conjSub_le_iff] at hnU
    exact hnU
  have hnπ : π n⁻¹ = 1 := (QuotientGroup.eq_one_iff _).mpr (N.inv_mem hn)
  have hM'map : (conjSub n⁻¹ J₀).map π = J₀.map π := by
    rw [AscQuot.map_conjSub, hnπ, conjSub_one]
  refine ⟨conjSub n⁻¹ J₀, hM'Ω, hUM', ?_⟩
  obtain ⟨R', hR', hUR'⟩ := IsSylow2In.exists_ge hU2 hUM'
  have hRbcard : Nat.card Rb = 2 * Nat.card Ub := by
    have h1 := Subgroup.relIndex_mul_card Ub Rb
    rw [inf_eq_left.mpr hUbR] at h1
    have : Ub.relIndex Rb = 2 := hidx
    rw [this] at h1
    omega
  have hR'b : IsSylow2In (R'.map π) (J₀.map π) := by
    have := isSylow2In_map_mk hN hR'
    rwa [hM'map] at this
  have hcardR' : Nat.card R' = Nat.card Rb := by
    rw [← natCard_map_of_isPGroup hN hR'.2.1, hR'b.natCard_eq hRbJ]
  have hcardU : Nat.card Ub = Nat.card U := by
    rw [← hmap, natCard_map_of_isPGroup hN hU2]
  refine ⟨R', mem_RSet_of_isSylow2In hM'Ω hR', hUR', ?_, ?_⟩
  · have hcycU : IsCyclic ↥(U.map π) := by rw [hmap]; exact hcyc
    exact ((AscQuot.quotRestrictEquiv (inf_bot_of_isPGroup hN hU2)).isCyclic).mpr hcycU
  · refine relIndex_two_of_card hUR' ?_
    rw [hcardR', hRbcard, hcardU]

theorem inf_comap_map_eq (hN : Odd (Nat.card N)) {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T) :
    T ⊓ (U.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = U := by
  ext x
  constructor
  · rintro ⟨hxT, hx⟩
    obtain ⟨u, hu, hux⟩ := hx
    have h1 : u⁻¹ * x ∈ T ⊓ N := by
      refine ⟨T.mul_mem (T.inv_mem (hUT hu)) hxT, ?_⟩
      have h0 : QuotientGroup.mk' N (u⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hux, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    rw [inf_bot_of_isPGroup hN hT] at h1
    have h2 : u⁻¹ * x = 1 := h1
    have : u = x := inv_mul_eq_one.mp h2
    rw [← this]
    exact hu
  · intro hx
    exact ⟨hUT hx, Subgroup.mem_map_of_mem _ hx⟩

theorem image_conj (T : Subgroup G) {s : G} (U : Subgroup G) :
    (conjSub s U).map (QuotientGroup.mk' N) = conjSub (QuotientGroup.mk' N s) (U.map (QuotientGroup.mk' N)) :=
  AscQuot.map_conjSub _ _ _

theorem map_mem_WSet (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    W.map (QuotientGroup.mk' N) ∈ WSet (quotFamily Ω N) := by
  obtain ⟨η, ⟨T, hη, hinv⟩, rfl⟩ := hW
  set π := QuotientGroup.mk' N with hπ
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  let Tb : Sylow 2 (G ⧸ N) := Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective N) T
  have hTb : (Tb : Subgroup (G ⧸ N)) = (T : Subgroup G).map π :=
    Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective N) T
  have hUle : ∀ U ∈ η, U ≤ (T : Subgroup G) := fun U hU => (hη.1 hU).2
  have hinj : Set.InjOn (fun U : Subgroup G => U.map π) η := by
    intro U₁ h₁ U₂ h₂ h
    have e1 := inf_comap_map_eq hN hT2 (hUle U₁ h₁)
    have e2 := inf_comap_map_eq hN hT2 (hUle U₂ h₂)
    have h' : U₁.map π = U₂.map π := h
    rw [← e1, ← e2, h']
  set ηb : Set (Subgroup (G ⧸ N)) := (fun U => U.map π) '' η with hηb
  have hηb_set : ηb ∈ etaSet (quotFamily Ω N) (Tb : Subgroup (G ⧸ N)) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨U, hU, rfl⟩
      exact ⟨map_mem_USet hN (hη.1 hU).1, hTb ▸ Subgroup.map_mono (hUle U hU)⟩
    · rintro _ ⟨U₁, hU₁, rfl⟩ _ ⟨U₂, hU₂, rfl⟩ hne _ ⟨J₀, hJ₀, rfl⟩ ⟨h1, h2⟩
      have hne' : U₁ ≠ U₂ := fun h => hne (by rw [h])
      have hP2 : IsPGroup 2 ↥(U₁ ⊔ U₂) := hT2.to_le (sup_le (hUle U₁ hU₁) (hUle U₂ hU₂))
      have hle : U₁ ⊔ U₂ ≤ J₀ ⊔ N := by
        refine le_sup_of_map_le ?_
        rw [Subgroup.map_sup]
        exact sup_le h1 h2
      obtain ⟨n, hn, hnle⟩ := exists_conj_le_of_le_sup hN hP2 hle
      rw [conjSub_le_iff] at hnle
      exact hη.2.1 U₁ hU₁ U₂ hU₂ hne' _ (hΩ.conjInvariant n⁻¹ J₀ hJ₀)
        ⟨le_sup_left.trans hnle, le_sup_right.trans hnle⟩
    · intro ηb' hsub hdist
      set L : Subgroup (G ⧸ N) → Subgroup G := fun Ub => (T : Subgroup G) ⊓ Ub.comap π with hL
      have hLmap : ∀ Ub ∈ ηb', (L Ub).map π = Ub := fun Ub hUb =>
        (lift_USet hΩ' hΩ hN hT2 (hsub hUb).1 (hTb ▸ (hsub hUb).2)).1
      have hLinj : Set.InjOn L ηb' := fun U₁ h₁ U₂ h₂ h => by
        rw [← hLmap U₁ h₁, ← hLmap U₂ h₂, h]
      have hsubL : L '' ηb' ⊆ {U | U ∈ USet Ω ∧ U ≤ (T : Subgroup G)} := by
        rintro _ ⟨Ub, hUb, rfl⟩
        obtain ⟨-, M', -, -, hUS⟩ := lift_USet hΩ' hΩ hN hT2 (hsub hUb).1 (hTb ▸ (hsub hUb).2)
        exact ⟨hUS, inf_le_left⟩
      have hdistL : InDistinctMembers Ω (L '' ηb') := by
        rintro _ ⟨Ub₁, h₁, rfl⟩ _ ⟨Ub₂, h₂, rfl⟩ hne J hJ ⟨hJ1, hJ2⟩
        have hne' : Ub₁ ≠ Ub₂ := fun h => hne (by rw [h])
        refine hdist Ub₁ h₁ Ub₂ h₂ hne' (J.map π) (map_mem_quotFamily hJ) ⟨?_, ?_⟩
        · rw [← hLmap Ub₁ h₁]; exact Subgroup.map_mono hJ1
        · rw [← hLmap Ub₂ h₂]; exact Subgroup.map_mono hJ2
      have hmax := hη.2.2 (L '' ηb') hsubL hdistL
      rw [hLinj.ncard_image] at hmax
      rw [hηb, hinj.ncard_image]
      exact hmax
  refine ⟨ηb, ⟨Tb, hηb_set, ?_⟩, ?_⟩
  · rintro sb hsb _ ⟨U, hU, rfl⟩
    rw [hTb] at hsb
    obtain ⟨s, hs, rfl⟩ := hsb
    refine ⟨conjSub s U, hinv s hs U hU, ?_⟩
    exact image_conj (T : Subgroup G) U
  · rw [hηb, Subgroup.map_iSup]
    simp only [Subgroup.map_iSup, iSup_image]

end OddW

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
