module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

theorem kg_congr_conj {G H : Type} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  apply MulEquiv.ext
  intro x
  change e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem kg_symm_apply {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (σ' : MulAut K')
    (k : K) : (MulAut.congr e).symm σ' k = e.symm (σ' (e k)) := by
  obtain ⟨g, rfl⟩ : ∃ g : MulAut K, σ' = MulAut.congr e g :=
    ⟨(MulAut.congr e).symm σ', ((MulAut.congr e).apply_symm_apply σ').symm⟩
  rw [MulEquiv.symm_apply_apply]
  change g k = e.symm (e (g (e.symm (e k))))
  simp only [MulEquiv.symm_apply_apply]

theorem kg_fix_eq {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (σ' : MulAut K') :
    {k : K | (MulAut.congr e).symm σ' k = k} = e.symm '' {k' : K' | σ' k' = k'} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_image, kg_symm_apply]
  constructor
  · intro hk
    exact ⟨e k, e.symm_apply_eq.mp hk, e.symm_apply_apply k⟩
  · rintro ⟨k', hk', rfl⟩
    rw [e.apply_symm_apply, hk']

theorem kg_normalizer_map {G H : Type} [Group G] [Group H] (φ : G ≃* H) (S : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    φ g ∈ Subgroup.normalizer ((S.map φ.toMonoidHom : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have key : φ.symm (φ g * x * (φ g)⁻¹) = g * φ.symm x * g⁻¹ := by
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [key]
  exact hg (φ.symm x)

theorem kgConcl_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {p : ℕ}
    (h : KGConcl K' p) : KGConcl K p := by
  intro S B hS hSnc hSI hB hBN
  have hS' : IsPGroup 2 ↥(S.map (MulAut.congr e).toMonoidHom) := hS.map (MulAut.congr e).toMonoidHom
  have hB' : IsPGroup p ↥(B.map (MulAut.congr e).toMonoidHom) := hB.map (MulAut.congr e).toMonoidHom
  have hSnc' : ¬ IsCyclic ↥(S.map (MulAut.congr e).toMonoidHom) := by
    intro hc
    apply hSnc
    let ι := Subgroup.equivMapOfInjective S (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    exact isCyclic_of_surjective ι.symm ι.symm.surjective
  have hSI' : S.map (MulAut.congr e).toMonoidHom ⊓
      (MulAut.conj : K' →* MulAut K').range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨s, hs, rfl⟩, y, hy⟩
    have hs' : s = MulAut.conj (e.symm y) := by
      apply (MulAut.congr e).injective
      rw [kg_congr_conj, MulEquiv.apply_symm_apply]
      exact hy.symm
    have hmem : s ∈ S ⊓ (MulAut.conj : K →* MulAut K).range := ⟨hs, e.symm y, hs'.symm⟩
    rw [hSI, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot, hmem, map_one]
  have hBN' : B.map (MulAut.congr e).toMonoidHom ≤
      Subgroup.normalizer ((S.map (MulAut.congr e).toMonoidHom : Subgroup (MulAut K')) :
        Set (MulAut K')) := by
    rintro _ ⟨b, hb, rfl⟩
    exact kg_normalizer_map (MulAut.congr e) S (hBN hb)
  obtain ⟨σ₁', σ₂', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    h (S.map (MulAut.congr e).toMonoidHom) (B.map (MulAut.congr e).toMonoidHom) hS' hSnc' hSI'
      hB' hBN'
  refine ⟨(MulAut.congr e).symm σ₁', (MulAut.congr e).symm σ₂', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map_equiv.mp h1
  · exact Subgroup.mem_map_equiv.mp h2
  · intro hc
    apply h3
    have := congrArg (MulAut.congr e) hc
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · intro hc
    apply h4
    have := congrArg (MulAut.congr e) hc
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · intro τ hτ
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h5 _ (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hτ)
  · intro τ hτ
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h6 _ (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hτ)
  · intro τ hτ
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h7 _ (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hτ)
  · intro τ hτ
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h8 _ (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hτ)
  · have hA : {k : K | (MulAut.congr e).symm σ₁' k = k} ∪
        {k : K | (MulAut.congr e).symm σ₂' k = k} =
        e.symm '' ({k' : K' | σ₁' k' = k'} ∪ {k' : K' | σ₂' k' = k'}) := by
      rw [kg_fix_eq e σ₁', kg_fix_eq e σ₂', Set.image_union]
    have hm : Subgroup.closure (e.symm '' ({k' : K' | σ₁' k' = k'} ∪ {k' : K' | σ₂' k' = k'})) =
        (Subgroup.closure ({k' : K' | σ₁' k' = k'} ∪ {k' : K' | σ₂' k' = k'})).map
          e.symm.toMonoidHom :=
      (MonoidHom.map_closure e.symm.toMonoidHom _).symm
    rw [hA, hm, h9, eq_top_iff]
    intro x _
    exact Subgroup.mem_map.mpr ⟨e x, Subgroup.mem_top _, e.symm_apply_apply x⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut
