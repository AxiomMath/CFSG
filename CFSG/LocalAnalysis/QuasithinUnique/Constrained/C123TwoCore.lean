module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Core

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G] [Finite G] {T Y L : Subgroup G} {M : Type} [CommGroup M]
  {φ : ↥(blockU L) ≃* M} {π : ↥Y →* A7} {ρ : A7 →* MulAut M}

theorem coreW (m : Main T Y L) (D : ModData T Y L φ π ρ)
    {W : Subgroup G} (hWV : Y ⊓ Subgroup.centralizer (VZ T Y : Set G) ≤ W)
    (hWB : Y ⊓ Subgroup.normalizer (baum T : Set G) ≤ W)
    (hWZ : Y ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ W) : Y ≤ W := by
  have hH := m.hyp
  obtain ⟨A₁, hA₁, hA₁c⟩ := exists_offender m
  obtain ⟨hKk, hK4⟩ := D.klein A₁ hA₁ hA₁c
  have hT8 := card_img_T hH D.surj
  have hS : img π (baum T) = img π A₁ := img_baum m D hA₁ hA₁c
  have hKT : img π A₁ ≤ img π T := img_mono hA₁.1
  have hKc : Nat.card (img π A₁) = 4 := hKk.card
  have hconj := conj_mem_of_card hT8 hKc hKT
  have hDc : ∀ d : G, d ∈ Y → (∀ v ∈ VZ T Y, v * d = d * v) → d ∈ W := fun d hd hc =>
    hWV ⟨hd, Subgroup.mem_centralizer_iff.2 hc⟩
  let Kt : Subgroup G := ((img π A₁).comap π).map Y.subtype
  have hKt : ∀ y : G, y ∈ Kt ↔ ∃ hy : y ∈ Y, π ⟨y, hy⟩ ∈ img π A₁ := by
    intro y
    simp only [Kt, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hy, hx⟩
      exact ⟨⟨y, hy⟩, hx, rfl⟩
  have hKtY : Kt ≤ Y := fun k hk => ((hKt k).1 hk).1
  have hnormKt : ∀ (y : G) (hy : y ∈ Y), π ⟨y, hy⟩ ∈ Subgroup.normalizer (img π A₁ : Set A7) →
      y ∈ Subgroup.normalizer (Kt : Set G) := by
    intro y hy hn k
    show k ∈ Kt ↔ y * k * y⁻¹ ∈ Kt
    rw [hKt, hKt]
    have hmem := Subgroup.mem_normalizer_iff.1 hn
    constructor
    · rintro ⟨hk, hkK⟩
      have hykY : y * k * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy hk) (Y.inv_mem hy)
      refine ⟨hykY, ?_⟩
      have e : π ⟨y * k * y⁻¹, hykY⟩ = π ⟨y, hy⟩ * π ⟨k, hk⟩ * (π ⟨y, hy⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [e]
      exact (hmem _).1 hkK
    · rintro ⟨hykY, hykK⟩
      have hk : k ∈ Y := by
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hykY) hy
        simpa [mul_assoc] using this
      refine ⟨hk, ?_⟩
      have e : π ⟨y * k * y⁻¹, hykY⟩ = π ⟨y, hy⟩ * π ⟨k, hk⟩ * (π ⟨y, hy⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [e] at hykK
      exact (hmem _).2 hykK
  have hTn : ∀ (t : G) (ht : t ∈ T), π ⟨t, hH.TY ht⟩ ∈ Subgroup.normalizer (img π A₁ : Set A7) := by
    intro t ht
    have hmem : π ⟨t, hH.TY ht⟩ ∈ img π T := mem_img_of_mem (hH.TY ht) ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj x hx _ hmem, fun hx => ?_⟩
    have := hconj _ hx _ (Subgroup.inv_mem _ hmem)
    simpa [mul_assoc] using this
  let H₁ : Subgroup G := Y ⊓ Subgroup.normalizer (Kt : Set G)
  have hTH₁ : T ≤ H₁ := fun t ht => ⟨hH.TY ht, hnormKt t (hH.TY ht) (hTn t ht)⟩
  have hKtH₁ : Kt ≤ H₁ := fun k hk => ⟨hKtY hk, Subgroup.le_normalizer hk⟩
  have hH₁n : H₁ ≤ Subgroup.normalizer (Kt : Set G) := inf_le_right
  have hTsyl₁ : IsSylowTwoOf T H₁ := by
    refine ⟨hTH₁, hH.sylow.2.1, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex T H₁ Y hTH₁ inf_le_left
    exact fun hd => hH.sylow.2.2 (hd.trans (Dvd.intro _ h1))
  have hRsyl : IsSylowTwoOf (T ⊓ Kt) Kt := A4.isSylowTwoOf_inf_normal hTsyl₁ hKtH₁ hH₁n
  have hS_le_R : baum T ≤ T ⊓ Kt := by
    refine le_inf (C1GN.baum_le T) fun s hs => ?_
    rw [hKt]
    have hsY : s ∈ Y := hH.TY (C1GN.baum_le T hs)
    refine ⟨hsY, ?_⟩
    rw [← hS]
    exact mem_img_of_mem hsY hs
  have hbaumR : baum T = baum (T ⊓ Kt) := baum_eq_of_le hS_le_R inf_le_left
  have hfrat := exists_mul_of_sylow hKtH₁ hH₁n (inf_le_right : T ⊓ Kt ≤ Kt)
    (hH.sylow.2.1.to_le inf_le_left) hRsyl.2.2
  have hfratY : ∀ (y : G) (hy : y ∈ Y),
      π ⟨y, hy⟩ ∈ Subgroup.normalizer (img π A₁ : Set A7) → y ∈ W := by
    intro y hy hyn
    obtain ⟨n, hn, c, hc, hnc⟩ := hfrat y ⟨hy, hnormKt y hy hyn⟩
    have hnS : n ∈ Subgroup.normalizer (baum T : Set G) := by
      rw [hbaumR]
      exact normalizer_le_normalizer_baum _ hn.2
    have hn' : n ∈ W := hWB ⟨hn.1.1, hnS⟩
    obtain ⟨hcY, hcK⟩ := (hKt c).1 hc
    rw [← hS] at hcK
    obtain ⟨s, hsS, hsc⟩ := mem_img.1 hcK
    have hker : π (⟨c, hcY⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, hsc, mul_inv_cancel]
    have hd := D.ker _ hker
    have hdY : c * (s : G)⁻¹ ∈ Y := Y.mul_mem hcY (Y.inv_mem s.2)
    have hd' : c * (s : G)⁻¹ ∈ W := hDc _ hdY (fun v hv => Subgroup.mem_centralizer_iff.1 hd v hv)
    have hs' : (s : G) ∈ W := hWB ⟨s.2, Subgroup.le_normalizer hsS⟩
    have e : c = (c * (s : G)⁻¹) * s := by group
    rw [hnc, e]
    exact W.mul_mem hn' (W.mul_mem hd' hs')
  let Γ : Subgroup A7 := img π W
  have hNΓ : Subgroup.normalizer (img π A₁ : Set A7) ≤ Γ := by
    intro x hx
    obtain ⟨y, rfl⟩ := D.surj x
    exact mem_img.2 ⟨y, hfratY y y.2 hx, rfl⟩
  obtain ⟨y₀, hy₀Y, -, hy₀c, hy₀o⟩ := exists_seven m D
  have hy₀W : y₀ ∈ W := hWZ ⟨hy₀Y, Subgroup.mem_centralizer_iff.2 fun z hz => hy₀c z hz⟩
  have h7 : 7 ∣ Nat.card Γ := by
    have hx : π ⟨y₀, hy₀Y⟩ ∈ Γ := mem_img_of_mem hy₀Y hy₀W
    have := Subgroup.orderOf_dvd_natCard Γ hx
    rwa [hy₀o] at this
  have h72 : 72 ∣ Nat.card Γ := by
    have h1 := Subgroup.card_dvd_of_le hNΓ
    have h2 : Nat.card (Subgroup.normalizer (img π A₁ : Set A7)) = 72 := hKk.card_normalizer
    rwa [h2] at h1
  have hΓtop : Γ = ⊤ := eq_top_of_dvd h7 h72
  intro y hy
  have hmem : π ⟨y, hy⟩ ∈ Γ := by rw [hΓtop]; trivial
  obtain ⟨g, hgc, hg⟩ := mem_img.1 hmem
  have hker : π (⟨y, hy⟩ * g⁻¹) = 1 := by rw [map_mul, map_inv, hg, mul_inv_cancel]
  have hd := D.ker _ hker
  have hdY : y * (g : G)⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem g.2)
  have hd' : y * (g : G)⁻¹ ∈ W := hDc _ hdY (fun v hv => Subgroup.mem_centralizer_iff.1 hd v hv)
  have e : y = (y * (g : G)⁻¹) * g := by group
  rw [e]
  exact W.mul_mem hd' hgc

end CFSG.QuasithinUnique.L246.C123
