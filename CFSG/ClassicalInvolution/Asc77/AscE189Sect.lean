module

public import CFSG.ClassicalInvolution.Asc77.AscE184Sub

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E189Sect : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ n : ℕ, CITBelowU p f n →
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
      ∀ Λ : Set (Subgroup Y), HypOmegaMod p f Λ → (⨆ L ∈ Λ, L) = ⊤ → (∀ L ∈ Λ, AEmpty Λ L) →
        ∀ K ∈ Λ, ∀ J ∈ Λ, ∀ z t : Y, IsUniqueInvolution K z → IsUniqueInvolution J t →
          z * t = t * z → conjSub t K ≠ K →
            (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ K ∧
                IsSylow2In R₂ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧
                  u * u = 1 ∧ x * u * x⁻¹ = z * t) ∨
            (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
                ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧
                  Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w)

@[expose] def E189SectJoin : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ n : ℕ, CITBelowU p f n →
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
      ∀ Λ : Set (Subgroup Y), HypOmegaMod p f Λ → (⨆ L ∈ Λ, L) = ⊤ → (∀ L ∈ Λ, AEmpty Λ L) →
        ∀ K ∈ Λ, ∀ J ∈ Λ, ∀ z t : Y, IsUniqueInvolution K z → IsUniqueInvolution J t →
          z * t = t * z → conjSub t K ≠ K →
            (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ u x : Y, u ∈ K ⊔ K'' ∧ u ≠ 1 ∧ u * u = 1 ∧
                x * u * x⁻¹ = z * t) ∨
            (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
                ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧
                  Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w)

theorem E189Sect.toJoin (h : E189Sect p f) : E189SectJoin p f := by
  intro hp hq n hbelow Y _ _ hcard Λ hΛ hgen hA K hK J hJ z t hz ht hzt hne
  rcases h hp hq n hbelow Y hcard Λ hΛ hgen hA K hK J hJ z t hz ht hzt hne with
    ⟨K'', hK'', hne', R₁, R₂, hR₁, hR₂, -, u, x, hu, hu1, hu2, hux⟩ | h2
  · exact Or.inl ⟨K'', hK'', hne', u, x, sup_le_sup hR₁.1 hR₂.1 hu, hu1, hu2, hux⟩
  · exact Or.inr h2

variable {p f}

section Apply

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] in
theorem map_mem_twinSet_restrict {Y K : Subgroup G} (hKY : K ≤ Y) {K'' : Subgroup Y}
    (h : K'' ∈ twinSet (restrictFamily Ω Y) (K.subgroupOf Y)) :
    K''.map Y.subtype ∈ twinSet Ω K := by
  obtain ⟨hK'', z₀, hz₀, hz₀'⟩ := h
  have hK₂ : K''.map Y.subtype ∈ Ω := mem_restrictFamily_iff.mp hK''
  refine ⟨hK₂, (z₀ : G), isUniqueInvolution_of_subgroupOf hz₀ hKY, ?_⟩
  exact isUniqueInvolution_of_subgroupOf (K := K''.map Y.subtype)
    (by rwa [subgroupOf_map_subtype']) (Subgroup.map_subtype_le K'')

omit [Fact p.Prime] in
theorem map_ne_of_ne_subgroupOf {Y K : Subgroup G} {K'' : Subgroup Y}
    (h : K'' ≠ K.subgroupOf Y) : K''.map Y.subtype ≠ K := by
  intro h'
  apply h
  rw [← subgroupOf_map_subtype' K'', h']

variable [Finite G]

theorem e189_sect_apply (hsect : E189Sect p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hbelow : CITBelowU p f n) (hΩ : HypOmegaMod p f Ω) (hAΩ : ∀ L ∈ Ω, AEmpty Ω L)
    {H K J : Subgroup G} (hHn : Nat.card H < n) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKH : K ≤ H)
    (hJH : J ≤ H) {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    (∃ K'' ∈ twinSet Ω K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ K ∧ R₂ ∈ RSet Ω ∧
        R₂ ≤ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : G, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧
          x * u * x⁻¹ = z * t) ∨
    (∃ x ∈ H, ∃ M' ∈ twinSet Ω (conjSub x K), M' ≠ conjSub x K ∧
        ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ conjSub x K ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ M' ∧
          Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w) := by
  classical
  set S₀ : Set (Subgroup G) := {L | L ∈ Ω ∧ L ≤ H} with hS₀
  set Y : Subgroup G := ⨆ L ∈ S₀, L with hYdef
  have hYH : Y ≤ H := iSup₂_le fun L hL => hL.2
  have hSY : ∀ L ∈ S₀, L ≤ Y := fun L hL =>
    le_iSup₂ (f := fun L (_ : L ∈ S₀) => L) L hL
  have hKY : K ≤ Y := hSY K ⟨hK, hKH⟩
  have hJY : J ≤ Y := hSY J ⟨hJ, hJH⟩
  have htY : t ∈ Y := hJY ht.mem
  have hzY : z ∈ Y := hKY hz.mem
  have hcard : Nat.card ↥Y < n := lt_of_le_of_lt (Subgroup.card_le_of_le hYH) hHn
  have hΛ : HypOmegaMod p f (restrictFamily Ω Y) := hΩ.restrict Y
  have hgen : (⨆ L ∈ restrictFamily Ω Y, L) = ⊤ := by
    have h1 : (⨆ L' ∈ restrictFamily Ω Y, L').map Y.subtype = Y := by
      apply le_antisymm (Subgroup.map_subtype_le _)
      refine iSup₂_le fun L hL => ?_
      have hLY := hSY L hL
      have hLmem : L.subgroupOf Y ∈ restrictFamily Ω Y :=
        subgroupOf_mem_restrictFamily hL.1 hLY
      calc L = (L.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hLY).symm
        _ ≤ _ := Subgroup.map_mono
            (le_iSup₂ (f := fun L' (_ : L' ∈ restrictFamily Ω Y) => L') _ hLmem)
    have h2 : (⊤ : Subgroup Y).map Y.subtype = Y := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective Y.subtype_injective (h1.trans h2.symm)
  have hAΛ : ∀ L' ∈ restrictFamily Ω Y, AEmpty (restrictFamily Ω Y) L' := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    exact AEmpty.restrict hp hΩ hLY (hAΩ L hL)
  have hKΛ := subgroupOf_mem_restrictFamily hK hKY
  have hJΛ := subgroupOf_mem_restrictFamily hJ hJY
  have hz' := isUniqueInvolution_subgroupOf hz hKY
  have ht' := isUniqueInvolution_subgroupOf ht hJY
  have hzt' : (⟨z, hzY⟩ : Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨z, hzY⟩ := Subtype.ext hzt
  have hne' : conjSub (⟨t, htY⟩ : Y) (K.subgroupOf Y) ≠ K.subgroupOf Y := by
    intro h
    apply hne
    rw [conjSub_subgroupOf] at h
    have hle : conjSub t K ≤ Y := by
      have := conjSub_mono (n := t) hKY
      rwa [conjSub_eq_self_of_mem htY] at this
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hKY] at this
  rcases hsect hp hq n hbelow ↥Y hcard _ hΛ hgen hAΛ _ hKΛ _ hJΛ _ _ hz' ht' hzt' hne' with
    ⟨K'', hK''tw, hK''ne, R₁, R₂, hR₁, hR₂, hRc, u, x, hu, hu1, hu2, hux⟩ |
      ⟨x, M', hM'tw, hM'ne, R₁, R₂, hR₁, hR₂, hRc, hcomm⟩
  · left
    have hRK : R₁.map Y.subtype ≤ K := by
      have := Subgroup.map_mono (f := Y.subtype) hR₁.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
    refine ⟨K''.map Y.subtype, map_mem_twinSet_restrict hKY hK''tw,
      map_ne_of_ne_subgroupOf hK''ne, R₁.map Y.subtype, R₂.map Y.subtype,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hKΛ hR₁), hRK,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hK''tw.1 hR₂), Subgroup.map_mono hR₂.1, ?_,
      (u : G), (x : G), ?_, fun h => hu1 (Subtype.ext h), congrArg Subtype.val hu2,
      by simpa using congrArg Subtype.val hux⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hRc a ha b hb)
    · have := Subgroup.mem_map_of_mem Y.subtype hu
      rwa [Subgroup.map_sup] at this
  · right
    have hMY : conjSub (x : G) K ≤ Y := by
      have := conjSub_mono (n := (x : G)) hKY
      rwa [conjSub_eq_self_of_mem x.2] at this
    have hxK : (conjSub (x : G) K).subgroupOf Y ∈ restrictFamily Ω Y :=
      subgroupOf_mem_restrictFamily (hΩ.conjInvariant (x : G) K hK) hMY
    rw [conjSub_subgroupOf] at hM'tw hM'ne hR₁
    have hM₂Y : M'.map Y.subtype ≤ Y := Subgroup.map_subtype_le M'
    refine ⟨(x : G), hYH x.2, M'.map Y.subtype, map_mem_twinSet_restrict hMY hM'tw,
      map_ne_of_ne_subgroupOf hM'ne, R₁.map Y.subtype, R₂.map Y.subtype,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hxK hR₁), ?_,
      map_mem_RSet_restrict (mem_RSet_of_isSylow2In hM'tw.1 hR₂), Subgroup.map_mono hR₂.1, ?_,
      fun w hw => ?_⟩
    · have := Subgroup.map_mono (f := Y.subtype) hR₁.1
      rwa [Subgroup.map_subgroupOf_eq_of_le hMY] at this
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hRc a ha b hb)
    · rw [← Subgroup.map_sup] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      simpa using congrArg Subtype.val (hcomm w' hw')

theorem e189_sect_apply_join (hsect : E189Sect p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hbelow : CITBelowU p f n) (hΩ : HypOmegaMod p f Ω) (hAΩ : ∀ L ∈ Ω, AEmpty Ω L)
    {H K J : Subgroup G} (hHn : Nat.card H < n) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKH : K ≤ H)
    (hJH : J ≤ H) {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    (∃ K'' ∈ twinSet Ω K, K'' ≠ K ∧ ∃ u x : G, u ∈ K ⊔ K'' ∧ u ≠ 1 ∧ u * u = 1 ∧
        x * u * x⁻¹ = z * t) ∨
    (∃ x ∈ H, ∃ M' ∈ twinSet Ω (conjSub x K), M' ≠ conjSub x K ∧
        ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ conjSub x K ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ M' ∧
          Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w) := by
  rcases e189_sect_apply hsect hp hq hbelow hΩ hAΩ hHn hK hJ hKH hJH hz ht hzt hne with
    ⟨K'', hK'', hne', R₁, R₂, -, hR₁, -, hR₂, -, u, x, hu, hu1, hu2, hux⟩ | h2
  · exact Or.inl ⟨K'', hK'', hne', u, x, sup_le_sup hR₁ hR₂ hu, hu1, hu2, hux⟩
  · exact Or.inr h2

end Apply

end CFSG.ClassicalInvolution.Asc77
