module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8ParabolicSplit

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem kFactOmega8ParabolicLines_proved : KFactOmega8ParabolicLines := by
  intro X _ _ Lb P hΩ hP hB hperf hr E hEP _ hE9
  have hel := Lie.omega8_parabolic_elemAbelian hΩ hP hB hperf hr
  obtain ⟨hPL, T₀, hT₀, hN⟩ := hP
  obtain ⟨T, hT⟩ := Lie.exists_sylow_of_isSylowTwoOf hT₀
  have hT₀L : T₀ ≤ Lb := hT₀.1
  have hNJ : Subgroup.normalizer ((T : Subgroup ↥Lb) : Set ↥Lb) ≤ P.subgroupOf Lb := by
    intro y hy
    rw [hT, mem_normalizer_iff_map, Subgroup.map_subgroupOf_eq_of_le hT₀L] at hy
    exact Subgroup.mem_subgroupOf.mpr (hN ⟨y.2, hy⟩)
  obtain ⟨⟨-, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := Lie.statedClassicalModel_of_isOmegaEightPlus hΩ
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have := Lie.finite_spinFour (F := F)
  have h := borelQuotient_spinPlus Lie.three_le_four e
  obtain ⟨π', hπ', hker, hTπ⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient (plusDatum 4 F Lie.three_le_four) (weylD F Lie.three_le_four)
      (fun k => (torusD F Lie.three_le_four k).range) π' (Nat.card F - 1) :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hTπ] at hNπ
  have hBP : (borel (plusDatum 4 F Lie.three_le_four)
      (fun k => (torusD F Lie.three_le_four k).range)).map π' ≤ P.subgroupOf Lb := hNπ ▸ hNJ
  have hinj : Function.Injective π' := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, eq_bot_iff]
    intro z hz
    have := h.ker_pow z hz
    rw [hF2] at this
    simpa using this
  set φ : ↥(spinGroup (quadPlus 4 F)) →* X := Lb.subtype.comp π' with hφ
  have hφinj : Function.Injective φ := Lb.subtype_injective.comp hinj
  have hrange : ∀ x ∈ Lb, ∃ k, φ k = x := fun x hx => by
    obtain ⟨k, hk⟩ := hπ' ⟨x, hx⟩
    exact ⟨k, by rw [hφ, MonoidHom.comp_apply, hk]; rfl⟩
  set A := P.comap φ with hA
  have hBA : borel (plusDatum 4 F Lie.three_le_four)
      (fun k => (torusD F Lie.three_le_four k).range) ≤ A := fun b hb =>
    Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mp (hBP ⟨b, hb, rfl⟩))
  have hperfK : ∀ V : Subgroup ↥(spinGroup (quadPlus 4 F)), V ≤ A → ⁅V, V⁆ = V →
      ¬ 3 ∣ Nat.card V := by
    intro V hVA hV h3
    apply hperf (V.map φ) (Subgroup.map_le_iff_le_comap.mpr hVA)
      (by rw [← Subgroup.map_commutator, hV])
    rwa [Subgroup.card_map_of_injective hφinj]
  have h3K : ∀ V : Subgroup ↥(spinGroup (quadPlus 4 F)), V ≤ A → IsPGroup 3 V →
      Nat.card V ≤ 9 := by
    intro V hVA hV
    have := (hel (V.map φ) (Subgroup.map_le_iff_le_comap.mpr hVA) (hV.map φ)).2
    rwa [Subgroup.card_map_of_injective hφinj] at this
  have hEr : E ≤ φ.range := fun x hx => by
    obtain ⟨k, hk⟩ := hrange x (hPL (hEP hx))
    exact ⟨k, hk⟩
  have hmapE : (E.comap φ).map φ = E := Subgroup.map_comap_eq_self hEr
  have hE' : Nat.card (E.comap φ) = 9 := by
    have := (Subgroup.card_map_of_injective hφinj : Nat.card ((E.comap φ).map φ) = _)
    rw [hmapE, hE9] at this
    exact this.symm
  have hEA : E.comap φ ≤ A := Subgroup.comap_mono hEP
  obtain ⟨E₁, hE₁, hc₁, hn₁⟩ := Lie.spin_lines_core hF2 hBA hperfK h3K hEA hE'
  refine ⟨E₁.map φ, (Subgroup.map_mono hE₁).trans (Subgroup.map_comap_le φ E), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hφinj, hc₁]
  · rintro x ⟨hxP, hxN⟩
    obtain ⟨k, rfl⟩ := hrange x (hPL hxP)
    have hkA : k ∈ A := hxP
    have hkN : k ∈ Subgroup.normalizer ((E.comap φ : Subgroup _) : Set _) :=
      Subgroup.le_normalizer_comap φ
        (show k ∈ (Subgroup.normalizer (E : Set X)).comap φ from hxN)
    exact Subgroup.le_normalizer_map φ ⟨k, hn₁ ⟨hkA, hkN⟩, rfl⟩

end CFSG.AGLEmbeddingD2.McLaughlin
