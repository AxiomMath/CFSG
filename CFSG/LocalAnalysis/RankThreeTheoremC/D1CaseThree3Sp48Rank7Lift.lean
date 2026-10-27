module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev imH (H A : Subgroup G) : Subgroup (H ⧸ primeComplementCore (G := H) 3) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))

theorem exists_mulEquiv_sup_prod {X : Type*} [Group X] {V₁ V₂ : Subgroup X}
    (hs : IsSimpleGroup V₁) (hp : ⁅V₁, V₁⁆ = V₁) (hcomm : ⁅V₁, V₂⁆ = ⊥) :
    Nonempty (↥(V₁ ⊔ V₂) ≃* V₁ × V₂) := by
  have hc : ∀ a ∈ V₁, ∀ b ∈ V₂, Commute a b := fun a ha b hb => by
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hbot : V₁ ⊓ V₂ = ⊥ := by
    have hN : ((V₁ ⊓ V₂).subgroupOf V₁).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn2 : (n : X) ∈ V₂ := (Subgroup.mem_subgroupOf.mp hn).2
      have hcg : Commute (g : X) n := (hc g g.2 n hn2).symm.symm
      rw [Subgroup.mem_subgroupOf]
      have : (g : X) * n * (g : X)⁻¹ = n := by
        rw [hcg.eq, mul_assoc, mul_inv_cancel, mul_one]
      change (g : X) * (n : X) * (g : X)⁻¹ ∈ V₁ ⊓ V₂
      rw [this]
      exact Subgroup.mem_subgroupOf.mp hn
    rcases hs.eq_bot_or_eq_top_of_normal ((V₁ ⊓ V₂).subgroupOf V₁) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hx1 : x ∈ V₁ := hx.1
      have : (⟨x, hx1⟩ : V₁) ∈ (V₁ ⊓ V₂).subgroupOf V₁ := hx
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      have hle : V₁ ≤ V₂ := fun x hx => by
        have : (⟨x, hx⟩ : V₁) ∈ (V₁ ⊓ V₂).subgroupOf V₁ := by rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).2
      have h1 : ⁅V₁, V₁⁆ ≤ ⊥ := hcomm ▸ Subgroup.commutator_mono le_rfl hle
      rw [hp] at h1
      obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
      have ha : (a : X) = 1 := Subgroup.mem_bot.mp (h1 a.2)
      have hb : (b : X) = 1 := Subgroup.mem_bot.mp (h1 b.2)
      exact hab (Subtype.ext (ha.trans hb.symm))
  let θ : V₁ × V₂ →* X := V₁.subtype.noncommCoprod V₂.subtype fun a b => hc a a.2 b b.2
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : X) * b = 1 := hab
    have hb : (b : X) = (a : X)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    have hmem : (a : X) ∈ V₁ ⊓ V₂ := ⟨a.2, by
      have : (a : X)⁻¹ ∈ V₂ := hb ▸ b.2
      simpa using V₂.inv_mem this⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have ha1 : a = 1 := Subtype.ext hmem
    have hb1 : b = 1 := Subtype.ext (by rw [hb, hmem, inv_one]; rfl)
    rw [ha1, hb1]
    rfl
  have hrange : θ.range = V₁ ⊔ V₂ := by
    have := MonoidHom.noncommCoprod_range V₁.subtype V₂.subtype fun a b => hc a a.2 b b.2
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at this
  exact ⟨((MonoidHom.ofInjective hθ).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem exists_preimage_normal {H A : Subgroup G} (hAH : A ≤ H)
    {W : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hWA : W ≤ imH H A)
    (hn : imH H A ≤ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) 3))) :
    ∃ T : Subgroup G, T ≤ A ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      ∃ ρ : T →* W, Function.Surjective ρ := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set T₀ : Subgroup H := A.subgroupOf H ⊓ W.comap π with hT₀
  refine ⟨T₀.map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨h, ⟨hA, -⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hA
  · refine le_normalizer_of_forall_map_conj_le fun n hnA => ?_
    rintro _ ⟨t, ⟨h, ⟨hhA, hhW⟩, rfl⟩, rfl⟩
    have hnH : n ∈ H := hAH hnA
    have h1 : π ⟨n, hnH⟩ ∈ imH H A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hnA)
    refine ⟨⟨n, hnH⟩ * h * ⟨n, hnH⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
    · show _ ∈ A.subgroupOf H
      rw [Subgroup.mem_subgroupOf]
      exact A.mul_mem (A.mul_mem hnA (Subgroup.mem_subgroupOf.mp hhA)) (A.inv_mem hnA)
    · change π (⟨n, hnH⟩ * h * ⟨n, hnH⟩⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hn h1) (π h)).mp hhW
  · let ρ₀ : T₀ →* W := (π.comp T₀.subtype).codRestrict W fun x => x.2.2
    have hρ₀ : Function.Surjective ρ₀ := by
      rintro ⟨w, hw⟩
      obtain ⟨a, ha, haw⟩ := hWA hw
      exact ⟨⟨a, ha, by show π a ∈ W; rw [haw]; exact hw⟩, Subtype.ext haw⟩
    let e₀ : T₀ ≃* T₀.map H.subtype := Subgroup.equivMapOfInjective T₀ H.subtype H.subtype_injective
    refine ⟨ρ₀.comp e₀.symm.toMonoidHom, hρ₀.comp e₀.symm.surjective⟩

theorem hasL28Quot_of_normal {H S L : Subgroup G}
    (hAH : Subgroup.normalizer (S : Set G) ⊓ L ≤ H)
    {W : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hWA : W ≤ imH H (Subgroup.normalizer (S : Set G) ⊓ L))
    (hn : imH H (Subgroup.normalizer (S : Set G) ⊓ L) ≤
      Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) 3)))
    (hc : IsCaseTwoGroup 3 W) : HasL28Quot S L := by
  obtain ⟨T, hTA, hTn, ρ, hρ⟩ := exists_preimage_normal hAH hWA hn
  obtain ⟨d, hd, ⟨e⟩⟩ := hc
  exact ⟨T, hTA, hTn, d, e.toMonoidHom.comp ρ, hd, e.surjective.comp hρ⟩

theorem hasL28Quot2_of_normal {H S L : Subgroup G}
    (hAH : Subgroup.normalizer (S : Set G) ⊓ L ≤ H)
    {W₁ W₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hW₁ : W₁ ≤ imH H (Subgroup.normalizer (S : Set G) ⊓ L))
    (hW₂ : W₂ ≤ imH H (Subgroup.normalizer (S : Set G) ⊓ L))
    (hn : imH H (Subgroup.normalizer (S : Set G) ⊓ L) ≤
      Subgroup.normalizer ((W₁ ⊔ W₂ : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) 3)))
    (hp₁ : ⁅W₁, W₁⁆ = W₁) (hcomm : ⁅W₁, W₂⁆ = ⊥)
    (hc₁ : IsCaseTwoGroup 3 W₁) (hc₂ : IsCaseTwoGroup 3 W₂) : HasL28Quot2 S L := by
  obtain ⟨T, hTA, hTn, ρ, hρ⟩ := exists_preimage_normal hAH (sup_le hW₁ hW₂) hn
  obtain ⟨d₁, hd₁, ⟨e₁⟩⟩ := hc₁
  obtain ⟨d₂, hd₂, ⟨e₂⟩⟩ := hc₂
  have hs₁ : IsSimpleGroup W₁ := isSimpleGroup_of_isCaseTwoGroup_three ⟨d₁, hd₁, ⟨e₁⟩⟩
  obtain ⟨θ⟩ := exists_mulEquiv_sup_prod hs₁ hp₁ hcomm
  let Φ : ↥(W₁ ⊔ W₂) ≃* CatGroup d₁ × CatGroup d₂ := θ.trans (MulEquiv.prodCongr e₁ e₂)
  exact ⟨T, hTA, hTn, d₁, d₂, Φ.toMonoidHom.comp ρ, hd₁, hd₂, Φ.surjective.comp hρ⟩

theorem HasL28Quot2.hasL28Quot {S L : Subgroup G} (h : HasL28Quot2 S L) : HasL28Quot S L := by
  obtain ⟨T, hTN, hNT, d₁, d₂, ψ, hd₁, hd₂, hψ⟩ := h
  refine ⟨T, hTN, hNT, d₁, (MonoidHom.fst _ _).comp ψ, hd₁, fun x => ?_⟩
  obtain ⟨y, hy⟩ := hψ (x, 1)
  exact ⟨y, congrArg Prod.fst hy⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
