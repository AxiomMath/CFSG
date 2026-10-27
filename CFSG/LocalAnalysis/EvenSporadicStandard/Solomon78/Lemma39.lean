module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

abbrev conjHom (g : G) : G →* G := (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem conjHom_apply (g x : G) : conjHom g x = g * x * g⁻¹ := rfl

omit [Finite G] in
theorem conjHom_injective (g : G) : Function.Injective (conjHom g) := (MulAut.conj g).injective

omit [Finite G] in
theorem map_conj_mem_components (K : Subgroup G) (x g : G) {N : Subgroup G}
    (hN : N ≤ centralizer ({x} : Set G) ∧
      (N.subgroupOf (centralizer ({x} : Set G))).Normal ∧ Nonempty (N ≃* K)) :
    N.map (conjHom g) ≤ centralizer ({g * x * g⁻¹} : Set G) ∧
      ((N.map (conjHom g)).subgroupOf (centralizer ({g * x * g⁻¹} : Set G))).Normal ∧
        Nonempty (N.map (conjHom g) ≃* K) := by
  obtain ⟨hle, hnorm, ⟨e⟩⟩ := hN
  refine ⟨?_, ?_, ⟨(N.equivMapOfInjective (conjHom g) (conjHom_injective g)).symm.trans e⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hy' : y * x = x * y := mem_centralizer_singleton_iff.1 (hle hy)
    show g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hy']
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · refine ⟨fun n hn c => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨n₀, hn₀, hn₀e⟩ := hn
    have hcx : g⁻¹ * (c : G) * g ∈ centralizer ({x} : Set G) := by
      refine mem_centralizer_singleton_iff.2 ?_
      have hc : (c : G) * (g * x * g⁻¹) = g * x * g⁻¹ * (c : G) :=
        mem_centralizer_singleton_iff.1 c.2
      calc g⁻¹ * (c : G) * g * x = g⁻¹ * ((c : G) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (c : G)) * g := by rw [hc]
        _ = x * (g⁻¹ * (c : G) * g) := by group
    have h1 := hnorm.conj_mem ⟨n₀, hle hn₀⟩ (mem_subgroupOf.2 hn₀) ⟨g⁻¹ * (c : G) * g, hcx⟩
    rw [mem_subgroupOf] at h1
    refine ⟨(g⁻¹ * (c : G) * g) * n₀ * (g⁻¹ * (c : G) * g)⁻¹, h1, ?_⟩
    show g * ((g⁻¹ * (c : G) * g) * n₀ * (g⁻¹ * (c : G) * g)⁻¹) * g⁻¹ =
      (c : G) * (n : G) * (c : G)⁻¹
    rw [← hn₀e]
    show _ = (c : G) * (g * n₀ * g⁻¹) * (c : G)⁻¹
    group

omit [Finite G] in
theorem componentProduct_conj (K : Subgroup G) (x g : G) :
    componentProduct K (g * x * g⁻¹) = (componentProduct K x).map (conjHom g) := by
  apply le_antisymm
  · refine sSup_le fun N' hN' => ?_
    have hmem := map_conj_mem_components K (g * x * g⁻¹) g⁻¹ hN'
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at hmem
    have h1 : N'.map (conjHom g⁻¹) ≤ componentProduct K x := le_sSup hmem
    have h2 : N' ≤ (N'.map (conjHom g⁻¹)).map (conjHom g) := by
      intro y hy
      refine ⟨g⁻¹ * y * g, ⟨y, hy, by rw [conjHom_apply, inv_inv]⟩, ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
    exact h2.trans (Subgroup.map_mono h1)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (map_conj_mem_components K x g hN)

omit [Finite G] in
theorem mem_center_map_iff {K : Subgroup G} {x : G} :
    x ∈ (center K).map K.subtype ↔ x ∈ K ∧ ∀ k ∈ K, x * k = k * x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun k hk => congrArg Subtype.val (mem_center_iff.1 hz ⟨k, hk⟩).symm⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.2 fun k => Subtype.ext (hc k k.2).symm, rfl⟩

omit [Finite G] in
theorem conj_inv_mem_of_map_eq {K : Subgroup G} {g : G} (hK : K.map (conjHom g) = K) {k : G}
    (hk : k ∈ K) : g⁻¹ * k * g ∈ K := by
  have : k ∈ K.map (conjHom g) := by rw [hK]; exact hk
  obtain ⟨k₀, hk₀, rfl⟩ := this
  have e : g⁻¹ * (g * k₀ * g⁻¹) * g = k₀ := by group
  rw [conjHom_apply, e]
  exact hk₀

omit [Finite G] in
theorem conj_mem_of_map_eq {K : Subgroup G} {g : G} (hK : K.map (conjHom g) = K) {k : G}
    (hk : k ∈ K) : g * k * g⁻¹ ∈ K := by
  have : g * k * g⁻¹ ∈ K.map (conjHom g) := Subgroup.mem_map_of_mem (conjHom g) hk
  rwa [hK] at this

omit [Finite G] in
theorem vCandidates_conj {K : Subgroup G} {u g : G} (hK : K.map (conjHom g) = K)
    (hu : g * u * g⁻¹ = u) {v : G} (hv : v ∈ vCandidates K u) : g * v * g⁻¹ ∈ vCandidates K u := by
  obtain ⟨hvK, hvZ, hv2⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · have : (K ⊔ zpowers u).map (conjHom g) = K ⊔ zpowers u := by
      rw [Subgroup.map_sup, hK, MonoidHom.map_zpowers, conjHom_apply, hu]
    exact this ▸ Subgroup.mem_map_of_mem (conjHom g) hvK
  · intro hz
    rw [mem_center_map_iff] at hz hvZ
    refine hvZ ⟨?_, fun k hk => ?_⟩
    · have := conj_inv_mem_of_map_eq hK hz.1
      have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
      rwa [e] at this
    · have h1 := hz.2 (g * k * g⁻¹) (conj_mem_of_map_eq hK hk)
      have : g * (v * k) * g⁻¹ = g * (k * v) * g⁻¹ := by
        calc g * (v * k) * g⁻¹ = g * v * g⁻¹ * (g * k * g⁻¹) := by group
          _ = g * k * g⁻¹ * (g * v * g⁻¹) := h1
          _ = g * (k * v) * g⁻¹ := by group
      have := mul_left_cancel (mul_right_cancel this)
      exact this
  · have := orderOf_injective (conjHom g) (conjHom_injective g) v
    rw [conjHom_apply] at this
    rw [this, hv2]

omit [Finite G] in
theorem twoAdic_inf_centralizer_conj {K : Subgroup G} {g : G} (hK : K.map (conjHom g) = K)
    (v : G) :
    twoAdic (K ⊓ centralizer ({g * v * g⁻¹} : Set G)) =
      twoAdic (K ⊓ centralizer ({v} : Set G)) := by
  have hc : (centralizer ({v} : Set G)).map (conjHom g) = centralizer ({g * v * g⁻¹} : Set G) := by
    ext y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have h1 : y₀ * v = v * y₀ := mem_centralizer_singleton_iff.1 hy₀
      show g * y₀ * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * y₀ * g⁻¹)
      calc g * y₀ * g⁻¹ * (g * v * g⁻¹) = g * (y₀ * v) * g⁻¹ := by group
        _ = g * (v * y₀) * g⁻¹ := by rw [h1]
        _ = g * v * g⁻¹ * (g * y₀ * g⁻¹) := by group
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · refine mem_centralizer_singleton_iff.2 ?_
        have h1 : y * (g * v * g⁻¹) = g * v * g⁻¹ * y := mem_centralizer_singleton_iff.1 hy
        calc g⁻¹ * y * g * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * v * g⁻¹ * y) * g := by rw [h1]
          _ = v * (g⁻¹ * y * g) := by group
      · show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hmap : (K ⊓ centralizer ({v} : Set G)).map (conjHom g) =
      K ⊓ centralizer ({g * v * g⁻¹} : Set G) := by
    rw [Subgroup.map_inf _ _ (conjHom g) (conjHom_injective g), hK, hc]
  have hcard : Nat.card ((K ⊓ centralizer ({v} : Set G)).map (conjHom g)) =
      Nat.card (K ⊓ centralizer ({v} : Set G) : Subgroup G) :=
    Subgroup.card_map_of_injective (conjHom_injective g)
  unfold twoAdic
  rw [← hmap, hcard]

omit [Finite G] in
theorem vMaximal_conj {K : Subgroup G} {u g : G} (hK : K.map (conjHom g) = K)
    (hu : g * u * g⁻¹ = u) {v : G} (hv : v ∈ vMaximal K u) : g * v * g⁻¹ ∈ vMaximal K u := by
  refine ⟨vCandidates_conj hK hu hv.1, fun v' hv' => ?_⟩
  rw [twoAdic_inf_centralizer_conj hK]
  exact hv.2 v' hv'

@[expose] def Sol78Fusion39 (L K : Subgroup G) (u : G) : Prop :=
  ∀ v ∈ vMaximal K u, ∀ g ∈ centralizer ({u} : Set G),
    ∃ c ∈ L ⊓ centralizer ({u} : Set G), g * v * g⁻¹ = c * v * c⁻¹

@[expose] def Sol78Generate (L K : Subgroup G) (u : G) : Prop :=
  ∀ l ∈ L, l * u * l⁻¹ ∈ vPairs L K u → K ⊔ K.map (conjHom l) = L


theorem SolomonSetting.toHyp (S : SolomonSetting G L K t u) (hne : (vPairs L K u).Nonempty)
    (hfus : Sol78Fusion39 L K u) (hgen : Sol78Generate L K u) : SolomonHyp G L K t u := by
  have hK : ∀ g ∈ centralizer ({u} : Set G), g * u * g⁻¹ = u ∧ K.map (conjHom g) = K := by
    intro g hg
    have hug : g * u * g⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 hg
      rw [this]
      group
    refine ⟨hug, ?_⟩
    have h := componentProduct_conj K u g
    rw [hug, ← S.hyp35] at h
    exact h.symm
  have h1 : ∀ g ∈ centralizer ({u} : Set G), ∀ w ∈ vPairs L K u, g * w * g⁻¹ ∈ vPairs L K u := by
    intro g hg w hw
    obtain ⟨v, hv, rfl, l, hl, hlw⟩ := hw
    obtain ⟨hug, hKg⟩ := hK g hg
    obtain ⟨c, hc, hcv⟩ := hfus v hv g hg
    have hcu : c * u * c⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 hc.2
      rw [this]
      group
    have hgv : g * (u * v) * g⁻¹ = u * (g * v * g⁻¹) := by
      calc g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
        _ = u * (g * v * g⁻¹) := by rw [hug]
    refine ⟨g * v * g⁻¹, vMaximal_conj hKg hug hv, hgv, c * l, mul_mem hc.1 hl, ?_⟩
    calc c * l * u * (c * l)⁻¹ = c * (l * u * l⁻¹) * c⁻¹ := by group
      _ = c * (u * v) * c⁻¹ := by rw [hlw]
      _ = (c * u * c⁻¹) * (c * v * c⁻¹) := by group
      _ = u * (c * v * c⁻¹) := by rw [hcu]
      _ = u * (g * v * g⁻¹) := by rw [hcv]
      _ = g * (u * v) * g⁻¹ := hgv.symm
  refine ⟨S, h1, ?_⟩
  intro g hg
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hug, hKg⟩ := hK g hg
  have hw' := h1 g hg w hw
  have hw0 := hw
  obtain ⟨-, -, -, l, hl, hlw⟩ := hw
  obtain ⟨-, -, -, l', hl', hlw'⟩ := hw'
  have hL1 := hgen l hl (by rw [hlw]; exact hw0)
  have hL2 := hgen l' hl' (by rw [hlw']; exact h1 g hg w hw0)
  have hcp1 : componentProduct K w = K.map (conjHom l) := by
    rw [← hlw, componentProduct_conj K u l, ← S.hyp35]
  have hcp2 : componentProduct K (g * w * g⁻¹) = K.map (conjHom l') := by
    rw [← hlw', componentProduct_conj K u l', ← S.hyp35]
  have e : (K.map (conjHom l)).map (conjHom g) = K.map (conjHom l') := by
    rw [← hcp1, ← componentProduct_conj, hcp2]
  have hL : L.map (conjHom g) = L := by
    calc L.map (conjHom g) = (K ⊔ K.map (conjHom l)).map (conjHom g) := by rw [hL1]
      _ = K.map (conjHom g) ⊔ (K.map (conjHom l)).map (conjHom g) := Subgroup.map_sup _ _ _
      _ = K ⊔ K.map (conjHom l') := by rw [hKg, e]
      _ = L := hL2
  refine mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · have : g * h * g⁻¹ ∈ L.map (conjHom g) := Subgroup.mem_map_of_mem (conjHom g) hh
    rwa [hL] at this
  · have : g * h * g⁻¹ ∈ L.map (conjHom g) := by rwa [hL]
    obtain ⟨h₀, hh₀, he⟩ := this
    have : h₀ = h := conjHom_injective g (by simpa [conjHom_apply] using he)
    exact this ▸ hh₀

end CFSG.EvenSporadicStandard.Solomon78
