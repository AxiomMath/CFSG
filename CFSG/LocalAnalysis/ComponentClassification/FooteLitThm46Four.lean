module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Pair
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Inputs

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem MulAut.congr_conj {X Y : Type*} [Group X] [Group Y] (ε : X ≃* Y) (x : X) :
    MulAut.congr ε (MulAut.conj x) = MulAut.conj (ε x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem eq_one_of_mem_of_odd {P O : Subgroup G} (hP : IsPGroup 2 P) (hO : Odd (Nat.card O))
    {x : G} (hxP : x ∈ P) (hxO : x ∈ O) : x = 1 := by
  have h1 := eq_bot_of_le_two_group_of_le_odd hP hO (zpowers_le.mpr hxP) (zpowers_le.mpr hxO)
  rw [zpowers_eq_bot] at h1
  exact h1

theorem exists_card_eight_le_coreActionKernel (h : FooteSec4 G L) (hE8 : FooteL2FourgroupE8)
    {M₁ M₂ : Subgroup G} (hM₁ : IsFooteM L M₁) (hM₂ : IsFooteM L M₂)
    (hc : ⁅M₁, M₂⁆ ≤ oddCoreIn M₁) (hM₂C : M₂ ≤ coreActionKernel M₁) {F₁ : Subgroup G}
    (hF₁2 : ∀ x ∈ F₁, x ^ 2 = 1) (hF₁8 : Nat.card F₁ = 8)
    (hF₁ : F₁ ≤ coreActionKernel M₁ ⊓ normalizer (M₂ : Set G)) :
    (∀ P : Sylow 2 (L ⧸ Open.fusionZStar L),
      ∃ x ∈ (P : Subgroup (L ⧸ Open.fusionZStar L)),
        ∃ y ∈ (P : Subgroup (L ⧸ Open.fusionZStar L)), x * y ≠ y * x) ∧
    (∀ P : Subgroup G, IsSylowOf 2 P M₂ → ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) ∧
    ∀ W : Subgroup G, IsKleinFour W → W ≤ M₂ →
      ∃ F : Subgroup G, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 ∧ W ≤ F ∧
        F ≤ coreActionKernel M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ε⟩⟩ := hM₂.quotient h
  set S := L ⧸ Open.fusionZStar L with hS
  set N := normalizer (M₂ : Set G) with hN
  set Φ : ↥N →* MulAut S := (MulAut.congr ε).toMonoidHom.comp (GSThmB.oddBarConj M₂) with hΦ
  have hodd := odd_card_coreActionKernel_inf h hM₁ hM₂ hc
  have hker : ∀ x : N, Φ x = 1 → (x : G) ∈ coreActionKernel M₂ := by
    intro x hx
    apply GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one
    have h1 : (MulAut.congr ε) (GSThmB.oddBarConj M₂ x) = 1 := hx
    rwa [map_eq_one_iff _ (MulAut.congr ε).injective] at h1
  have hΦM : ∀ (m : G) (hm : m ∈ M₂) (hmN : m ∈ N),
      Φ ⟨m, hmN⟩ = MulAut.conj (ε ((⟨m, hm⟩ : M₂) : M₂ ⧸ pPrimeCore 2 M₂)) := by
    intro m hm hmN
    rw [hΦ, MonoidHom.comp_apply,
      show (⟨m, hmN⟩ : N) = ⟨((⟨m, hm⟩ : M₂) : G), hmN⟩ from rfl,
      oddBarConj_eq_conj' (⟨m, hm⟩ : M₂) hmN]
    exact MulAut.congr_conj ε _
  have hF₁N : F₁ ≤ N := hF₁.trans inf_le_right
  set E := (F₁.subgroupOf N).map Φ with hEdef
  have hinjF : ∀ x ∈ F₁.subgroupOf N, Φ x = 1 → x = 1 := by
    intro x hx hΦx
    apply Subtype.ext
    have hxC₂ := hker x hΦx
    have hxC₁ := (hF₁ hx).1
    have hx2 := hF₁2 _ hx
    have hFp : IsPGroup 2 F₁ := IsPGroup.of_card (n := 3) (by rw [hF₁8]; norm_num)
    exact eq_one_of_mem_of_odd hFp hodd hx (mem_inf.mpr ⟨hxC₁, hxC₂⟩)
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← sq, show x ^ 2 = 1 from Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hF₁2 _ hx), map_one]
  have hE8' : Nat.card E = 8 := by
    rw [hEdef, ← hF₁8]
    have hinj : Function.Injective (Φ.comp (F₁.subgroupOf N).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      exact Subtype.ext (hinjF x x.2 hx)
    have hrange : (Φ.comp (F₁.subgroupOf N).subtype).range = (F₁.subgroupOf N).map Φ := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (subgroupOfEquivOfLe hF₁N).toEquiv
  obtain ⟨hnab, hfour⟩ := hE8 S h.footeFamilyType E hE2 hE8'
  set f : M₂ →* S := ε.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 M₂)) with hf
  have hfs : Function.Surjective f := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  refine ⟨hnab, fun P hP => ?_, fun W hW hWM => ?_⟩
  ·
    obtain ⟨Q, rfl⟩ := hP
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab (Q.mapSurjective hfs)
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    refine ⟨x', ⟨x', hx', rfl⟩, y', ⟨y', hy', rfl⟩, fun h1 => hxy ?_⟩
    have h2 : x' * y' = y' * x' := Subtype.ext h1
    rw [← map_mul, h2, map_mul]
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW.card_four]; norm_num)
  have hinjW : Function.Injective (f.comp (W.subgroupOf M₂).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ ε.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    apply Subtype.ext
    apply Subtype.ext
    exact eq_one_of_mem_of_odd hWp (odd_card_oddCoreIn M₂) x.2 ⟨_, hx, rfl⟩
  set V := (W.subgroupOf M₂).map f with hVdef
  have hV : IsKleinFour V := by
    refine isKleinFour_of_card_eq_four ?_ ?_
    · have hrangeW : (f.comp (W.subgroupOf M₂).subtype).range = V := by
        rw [MonoidHom.range_comp, range_subtype]
      rw [← hrangeW, ← Nat.card_congr (MonoidHom.ofInjective hinjW).toEquiv, ← hW.card_four]
      exact Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv
    · rintro _ ⟨x, hx, rfl⟩
      have hx2 : x ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact sq_eq_one_of_isKleinFour hW hx)
      rw [← map_pow, hx2, map_one]
  obtain ⟨F', hF'le, hF'2, hF'8, hVF'⟩ := hfour V hV
  have hM₂N : M₂ ≤ N := le_normalizer
  set Y := F₁.subgroupOf N ⊔ M₂.subgroupOf N with hY
  have hInn : (M₂.subgroupOf N).map Φ = (MulAut.conj : S →* MulAut S).range := by
    apply le_antisymm
    · rintro _ ⟨⟨m, hmN⟩, hm, rfl⟩
      exact ⟨_, (hΦM m hm hmN).symm⟩
    · rintro _ ⟨s, rfl⟩
      obtain ⟨⟨m, hm⟩, hms⟩ := hfs s
      refine ⟨⟨m, hM₂N hm⟩, hm, ?_⟩
      rw [hΦM m hm (hM₂N hm), ← hms]
      rfl
  have hYmap : Y.map Φ = E ⊔ (MulAut.conj : S →* MulAut S).range := by
    rw [hY, Subgroup.map_sup, hInn]
  set P := Y ⊓ F'.comap Φ with hPdef
  have hPmap : P.map Φ = F' := by
    apply le_antisymm
    · exact (map_mono inf_le_right).trans (map_comap_le Φ F')
    · intro x hx
      have hxY : x ∈ Y.map Φ := hYmap ▸ hF'le hx
      obtain ⟨y, hyY, rfl⟩ := mem_map.mp hxY
      exact ⟨y, mem_inf.mpr ⟨hyY, hx⟩, rfl⟩
  have hYC : ∀ y ∈ Y, (y : G) ∈ coreActionKernel M₁ := by
    intro y hy
    have h1 : Y ≤ (coreActionKernel M₁).subgroupOf N :=
      sup_le (fun x hx => (hF₁ hx).1) (fun x hx => hM₂C hx)
    exact h1 hy
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 P
  have hRp : IsPGroup 2 R := hR.isPGroup
  have hRker : ∀ r ∈ R, Φ r = 1 → r = 1 := by
    intro r hr hΦr
    apply Subtype.ext
    exact eq_one_of_mem_of_odd (hRp.map N.subtype) hodd ⟨r, hr, rfl⟩
      (mem_inf.mpr ⟨hYC r (mem_inf.mp (hR.le hr)).1, hker r hΦr⟩)
  have hinjR : Function.Injective (Φ.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subtype.ext (hRker x x.2 hx)
  have hrangeR : (Φ.comp R.subtype).range = R.map Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  have hRcard : Nat.card R = Nat.card (R.map Φ) := by
    rw [← hrangeR]
    exact Nat.card_congr (MonoidHom.ofInjective hinjR).toEquiv
  have hRF : R.map Φ ≤ F' := (map_mono hR.le).trans hPmap.le
  have h8 : 8 ∣ Nat.card P := by
    rw [← hF'8, ← hPmap]
    exact card_map_dvd P Φ
  have hR8 : Nat.card R = 8 := by
    apply le_antisymm
    · rw [hRcard, ← hF'8]
      exact Subgroup.card_le_of_le hRF
    · rw [hR.card_eq]
      have h1 : 3 ≤ (Nat.card P).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
          (by norm_num; exact h8)
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (Nat.card P).factorization 2 := Nat.pow_le_pow_right (by norm_num) h1
  have hR2 : ∀ r ∈ R, r ^ 2 = 1 := by
    intro r hr
    have h1 : Φ r ∈ F' := hRF ⟨r, hr, rfl⟩
    apply hRker (r ^ 2) (pow_mem hr 2)
    rw [map_pow, sq, hF'2 _ h1]
  have hWN : W ≤ N := hWM.trans hM₂N
  have hWP : W.subgroupOf N ≤ P := by
    intro x hx
    have hxM : (x : G) ∈ M₂ := hWM hx
    refine mem_inf.mpr ⟨mem_sup_right (show x ∈ M₂.subgroupOf N from hxM), ?_⟩
    show Φ x ∈ F'
    have h1 : Φ x = MulAut.conj (ε ((⟨x, hxM⟩ : M₂) : M₂ ⧸ pPrimeCore 2 M₂)) := hΦM x hxM x.2
    rw [h1]
    exact hVF' ⟨f ⟨x, hxM⟩, ⟨⟨x, hxM⟩, hx, rfl⟩, rfl⟩
  obtain ⟨k, hkP, hk⟩ := exists_conj_le_of_isSylowOf hR hWP hWp.comap_subtype
  have hRC : R.map N.subtype ≤ coreActionKernel M₁ := by
    rintro _ ⟨r, hr, rfl⟩
    exact hYC r (mem_inf.mp (hR.le hr)).1
  have hkC : ((k : G))⁻¹ ∈ coreActionKernel M₁ := inv_mem (hYC k (mem_inf.mp hkP).1)
  refine ⟨conjugate (R.map N.subtype) (k : G)⁻¹, sq_eq_one_of_mem_conjugate ?_ _, ?_, ?_,
    conjugate_le_of_mem hRC hkC⟩
  · rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hR2 r hr, map_one]
  · rw [card_conjugate_eq_card, Subgroup.card_map_of_injective N.subtype_injective, hR8]
  · intro w hw
    rw [mem_conjugate_iff, inv_inv]
    have h1 := hk ⟨w, hWN hw⟩ hw
    exact ⟨_, h1, rfl⟩

theorem normalizer_le_normalizer_of_le (h : FooteSec4 G L) {M₁ M₂ : Subgroup G}
    (hM₁ : IsFooteM L M₁)
    (hfour : ∀ W : Subgroup G, IsKleinFour W → W ≤ M₂ →
      ∃ F : Subgroup G, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 ∧ W ≤ F ∧
        F ≤ coreActionKernel M₁)
    {U W₀ : Subgroup G} (hUM : U ≤ M₂) (hW₀ : IsKleinFour W₀) (hW₀U : W₀ ≤ U) :
    normalizer (U : Set G) ≤ normalizer (M₁ : Set G) := by
  have hLW : ∀ W : Subgroup G, IsKleinFour W → W ≤ M₂ → footeME L W = M₁ := by
    intro W hW hWM
    obtain ⟨F, hF2, hF8, hWF, hFC⟩ := hfour W hW hWM
    exact (foote_lemma_4_5_ii h hM₁ hF2 hF8 hFC).2 W hW hWF
  intro g hg
  have hW₁ : IsKleinFour (conjugate W₀ g) :=
    isKleinFour_of_card_eq_four (by rw [card_conjugate_eq_card, hW₀.card_four])
      (sq_eq_one_of_mem_conjugate (fun x hx => sq_eq_one_of_isKleinFour hW₀ hx) g)
  have hW₁U : conjugate W₀ g ≤ U := by
    rw [← conjugate_eq_of_mem_normalizer hg]
    exact map_mono hW₀U
  apply mem_normalizer_of_conjugate_eq
  rw [← hLW W₀ hW₀ (hW₀U.trans hUM), ← footeME_conjugate h.huniq,
    hLW _ hW₁ (hW₁U.trans hUM), hLW W₀ hW₀ (hW₀U.trans hUM)]

theorem normalizer_le_normalizer_of_four (h : FooteSec4 G L) {M₁ M₂ : Subgroup G}
    (hM₁ : IsFooteM L M₁) (hM₂ : IsFooteM L M₂) (h21 : M₂ ≤ normalizer (M₁ : Set G))
    (hfour : ∀ W : Subgroup G, IsKleinFour W → W ≤ M₂ →
      ∃ F : Subgroup G, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 ∧ W ≤ F ∧
        F ≤ coreActionKernel M₁) :
    normalizer (M₂ : Set G) ≤ normalizer (M₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_isSylowOf 2 M₂
  obtain ⟨W₀, hW₀, hW₀M⟩ := hM₂.exists_isKleinFour h
  have hW₀p : IsPGroup 2 W₀ := IsPGroup.of_card (n := 2) (by rw [hW₀.card_four]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hU hW₀M hW₀p
  have hW₁ : IsKleinFour (conjugate W₀ k) :=
    isKleinFour_of_card_eq_four (by rw [card_conjugate_eq_card, hW₀.card_four])
      (sq_eq_one_of_mem_conjugate (fun x hx => sq_eq_one_of_isKleinFour hW₀ hx) k)
  have hNU := normalizer_le_normalizer_of_le h hM₁ hfour hU.le hW₁ (conjugate_le_of_forall hk)
  intro g hg
  have hUg : IsSylowOf 2 (conjugate U g) M₂ := by
    refine isSylowOf_of_card ?_ ?_
    · rw [← conjugate_eq_of_mem_normalizer hg]
      exact map_mono hU.le
    · rw [card_conjugate_eq_card, hU.card_eq]
  obtain ⟨m, hm, hmU⟩ := hU.exists_mem_conj hUg
  have hgm : g * m ∈ normalizer (U : Set G) := by
    apply mem_normalizer_of_conjugate_eq
    rw [← UnbalancedLayer.conjugate_conjugate]
    ext x
    rw [mem_conjugate_iff, hmU]
    constructor
    · intro hx
      rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at hx
    · intro hx
      rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group]
  have h1 := hNU hgm
  have h2 : g = g * m * m⁻¹ := by group
  rw [h2]
  exact mul_mem h1 (inv_mem (h21 hm))

end CFSG.ComponentClassification.FooteLit
