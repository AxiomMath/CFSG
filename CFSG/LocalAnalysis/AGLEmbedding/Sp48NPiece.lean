module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NDefs
public import CFSG.LocalAnalysis.AGLEmbedding.G28Data
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Piece

variable {G : Type} [Group G] [Finite G] {H M : Subgroup G}

theorem exists_perfect_lift {p : ℕ} {Y : Subgroup G}
    {V₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hVY : V₀ ≤ (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hV₀ : ⁅V₀, V₀⁆ = V₀) :
    ∃ V : Subgroup G, V ≤ Y ∧ ⁅V, V⁆ = V ∧
      (V.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = V₀ := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set Q₀ := Y.subgroupOf H ⊓ V₀.comap π with hQ₀
  have hQmap : Q₀.map π = V₀ := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := hVY hv
      exact ⟨y, ⟨hy, hv⟩, rfl⟩
  obtain ⟨P', hP'Q, hP'P, hP'map⟩ := exists_perfect_le_map_eq' π hQmap hV₀
  refine ⟨P'.map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨p', hp', rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hP'Q hp').1
  · rw [← Subgroup.map_commutator, hP'P]
  · have hsub : (P'.map H.subtype).subgroupOf H = P' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hsub, hP'map]

theorem exists_sp48NPiece {T K A₀ V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hS : Sp48NInSitu T (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      K A₀ V₀) :
    ∃ V : Subgroup G, (V.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      V₀ ∧ Sp48NPiece (H ⊓ M) (GLBPrimeCore 3 H) V := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  obtain ⟨V, hVK, hVV, hVmap⟩ := exists_perfect_lift (p := 3) (Y := H ⊓ M) hS.V_le hS.V_perfect
  have hVH : V ≤ H := hVK.trans inf_le_left
  refine ⟨V, hVmap, hVV, hVK, ?_, ?_, ?_, ?_⟩
  ·
    intro hVN
    have hbot : V₀ = ⊥ := by
      rw [← hVmap, eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_bot.mpr ((mem_glbPrimeCore_iff_mk_eq_one (p := 3) v).mp
        (hVN (Subgroup.mem_subgroupOf.mp hv)))
    have h1 : T ⊓ K ≤ ⊥ := hbot ▸ hS.TK_le_V
    have h2 := hS.card_TK
    rw [le_bot_iff.mp h1, Subgroup.card_bot] at h2
    norm_num at h2
  ·
    intro k hk
    rw [sup_glbPrimeCore_eq_preimage hVH hVmap]
    refine mem_normalizer_comap_map hk.1 (hS.V_normal ?_)
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
  ·
    intro W hWK hWn
    have hWH : W ≤ H := hWK.trans inf_le_left
    rcases hS.minimal ((W.subgroupOf H).map π) (Subgroup.map_mono (Subgroup.comap_mono hWK))
      (map_mk_le_normalizer_map_mk hWn) with h1 | h1
    · exact Or.inl (le_glbPrimeCore_of_map_eq_bot hWH h1)
    · exact Or.inr (le_sup_glbPrimeCore_of_map_le hVH (hVmap ▸ h1))
  ·
    intro g hgK hgV
    have hgH : g ∈ H := hgK.1
    have hgC : π ⟨g, hgH⟩ ∈ ((H ⊓ M).subgroupOf H).map π ⊓
        Subgroup.centralizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      refine ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hgK), ?_⟩
      show π ⟨g, hgH⟩ ∈ Subgroup.centralizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3))
      rw [Subgroup.mem_centralizer_iff, ← hVmap]
      rintro _ ⟨v, hv, rfl⟩
      have h1 := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) (⟨g, hgH⟩ * v * ⟨g, hgH⟩⁻¹ * v⁻¹)).mp
        (by simpa using hgV v (Subgroup.mem_subgroupOf.mp hv))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 := mul_inv_eq_one.mp h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [hS.V_centralizer, Subgroup.mem_bot] at hgC
    exact (mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⟨g, hgH⟩).mpr hgC

theorem map_conj_le_sup_of_map {W W' : Subgroup G} (hWH : W ≤ H) (t : H)
    {W₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hW : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = W₀)
    (hle : W₀.map (MulAut.conj (QuotientGroup.mk' (primeComplementCore (G := H) 3) t)).toMonoidHom
      ≤ (W'.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))) :
    W.map (MulAut.conj (t : G)).toMonoidHom ≤ W' ⊔ GLBPrimeCore 3 H := by
  rintro _ ⟨w, hw, rfl⟩
  have hwH : w ∈ H := hWH hw
  have hx : ((MulAut.conj (t : G)).toMonoidHom w) =
      ((t * ⟨w, hwH⟩ * t⁻¹ : H) : G) := by simp
  rw [hx]
  refine le_sup_glbPrimeCore_of_map_le (Y := Subgroup.zpowers ((t * ⟨w, hwH⟩ * t⁻¹ : H) : G))
    (X := W') (Subgroup.zpowers_le.mpr (t * ⟨w, hwH⟩ * t⁻¹).2) ?_ (Subgroup.mem_zpowers _)
  rw [map_zpowers_subgroupOf (t * ⟨w, hwH⟩ * t⁻¹).2, Subgroup.zpowers_le]
  apply hle
  refine ⟨QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨w, hwH⟩, ?_, ?_⟩
  · rw [← hW]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl

theorem sp48NFactors_of {T K A₀ V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hS : Sp48NInSitu T (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      K A₀ V₀) {R V : Subgroup G} (hRH : R ≤ H)
    (hT : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = T)
    (hVK : V ≤ H ⊓ M)
    (hVmap : (V.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = V₀) :
    Sp48NFactors (H ⊓ M) (GLBPrimeCore 3 H) R V := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  obtain ⟨V₁, V₂, h12, hcomm, hp1, hp2, ⟨d₁, hd₁, ⟨e₁⟩⟩, ⟨d₂, hd₂, ⟨e₂⟩⟩, hT1, hT2, τb, hτb,
    hτ12, hτ21⟩ := hS.factors
  have hVH : V ≤ H := hVK.trans inf_le_left
  have h1V : V₁ ≤ (V.subgroupOf H).map π := hVmap ▸ (le_sup_left.trans h12.le)
  have h2V : V₂ ≤ (V.subgroupOf H).map π := hVmap ▸ (le_sup_right.trans h12.le)
  obtain ⟨W₁, hW₁V, hW₁W₁, hW₁map⟩ := exists_perfect_lift (p := 3) h1V hp1
  obtain ⟨W₂, hW₂V, hW₂W₂, hW₂map⟩ := exists_perfect_lift (p := 3) h2V hp2
  have hW₁H : W₁ ≤ H := hW₁V.trans hVH
  have hW₂H : W₂ ≤ H := hW₂V.trans hVH
  have honto : ∀ (W : Subgroup G) (hWH : W ≤ H) (V' : Subgroup (H ⧸ primeComplementCore (G := H) 3))
      (d : TauCeti.ValidLieTypeIndex), (W.subgroupOf H).map π = V' → (V' ≃* CatGroup d) →
      ∃ ψ : W →* CatGroup d, Function.Surjective ψ ∧ ∀ x : W, ψ x = 1 → (x : G) ∈
        GLBPrimeCore 3 H := by
    intro W hWH V' d hWmap e
    have hθmem : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ V' := fun w => by
      rw [← hWmap]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr w.2)
    let θ : W →* V' := (π.comp (Subgroup.inclusion hWH)).codRestrict V' hθmem
    have hθ : Function.Surjective θ := by
      intro w
      have hw : (w : H ⧸ primeComplementCore (G := H) 3) ∈ (W.subgroupOf H).map π := hWmap ▸ w.2
      obtain ⟨v, hv, hvw⟩ := hw
      exact ⟨⟨v, Subgroup.mem_subgroupOf.mp hv⟩, Subtype.ext hvw⟩
    refine ⟨e.toMonoidHom.comp θ, e.surjective.comp hθ, fun x hx => ?_⟩
    have hx1 : θ x = 1 := e.injective (by simpa using hx)
    have hx2 : π (Subgroup.inclusion hWH x) = 1 := congrArg Subtype.val hx1
    exact (mem_glbPrimeCore_iff_mk_eq_one (p := 3) (Subgroup.inclusion hWH x)).mpr hx2
  obtain ⟨ψ₁, hψ₁, hk₁⟩ := honto W₁ hW₁H V₁ d₁ hW₁map e₁
  obtain ⟨ψ₂, hψ₂, hk₂⟩ := honto W₂ hW₂H V₂ d₂ hW₂map e₂
  have hnorm : ∀ (W : Subgroup G) (hWH : W ≤ H)
      (V' : Subgroup (H ⧸ primeComplementCore (G := H) 3)), (W.subgroupOf H).map π = V' →
      T ≤ Subgroup.normalizer (V' : Set _) →
      R ≤ Subgroup.normalizer ((W ⊔ GLBPrimeCore 3 H : Subgroup G) : Set G) := by
    intro W hWH V' hWmap hTV r hr
    rw [sup_glbPrimeCore_eq_preimage hWH hWmap]
    refine mem_normalizer_comap_map (hRH hr) (hTV ?_)
    rw [← hT]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr)
  obtain ⟨t, ht, rfl⟩ := hτb
  have htK : (t : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp ht
  refine ⟨W₁, W₂, hW₁V, hW₂V, hW₁W₁, hW₂W₂, ?_, ?_, ⟨d₁, ψ₁, hd₁, hψ₁, hk₁⟩,
    ⟨d₂, ψ₂, hd₂, hψ₂, hk₂⟩, hnorm W₁ hW₁H V₁ hW₁map hT1, hnorm W₂ hW₂H V₂ hW₂map hT2,
    t, htK, map_conj_le_sup_of_map hW₁H t hW₁map (hτ12.le.trans hW₂map.ge),
    map_conj_le_sup_of_map hW₂H t hW₂map (hτ21.le.trans hW₁map.ge)⟩
  ·
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hc : ⁅π ⟨a, hW₁H ha⟩, π ⟨b, hW₂H hb⟩⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator
        (hW₁map ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha :
          (⟨a, hW₁H ha⟩ : H) ∈ W₁.subgroupOf H) : π ⟨a, hW₁H ha⟩ ∈ V₁)
        (hW₂map ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb :
          (⟨b, hW₂H hb⟩ : H) ∈ W₂.subgroupOf H) : π ⟨b, hW₂H hb⟩ ∈ V₂)
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    have := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⁅(⟨a, hW₁H ha⟩ : H), ⟨b, hW₂H hb⟩⁆).mpr
      (by rw [map_commutatorElement]; exact hc)
    simpa [commutatorElement_def] using this
  ·
    refine le_sup_glbPrimeCore_of_map_le hVH ?_
    rw [hVmap, ← h12, ← hW₁map, ← hW₂map]
    exact sup_le (Subgroup.map_mono (Subgroup.comap_mono le_sup_left))
      (Subgroup.map_mono (Subgroup.comap_mono le_sup_right))

end Piece

end CFSG.AGLEmbedding
