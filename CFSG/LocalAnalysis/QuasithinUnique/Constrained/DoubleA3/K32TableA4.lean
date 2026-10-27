module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32K
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

section A4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsA4Block.le_normalizer' {L U : Subgroup G} (h : IsA4Block L U) :
    L ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  rw [hLc]
  exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hcN)

theorem k32_le_of_normal_ne_bot {L U N₀ : Subgroup G} (hA : IsA4Block L U) (hN₀L : N₀ ≤ L)
    (hLN : L ≤ Subgroup.normalizer (N₀ : Set G)) (hne : N₀ ≠ ⊥) : U ≤ N₀ := by
  obtain ⟨v, hvN, hv1⟩ : ∃ v ∈ N₀, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_bot_iff.mpr fun v hv => Subgroup.mem_bot.mpr (hcon v hv))
  by_cases hvU : v ∈ U
  · exact hA.le_of_mem hLN hvN hvU hv1
  · obtain ⟨u, huU, hvu⟩ : ∃ u ∈ U, v * u ≠ u * v := by
      by_contra hcon
      push Not at hcon
      exact hvU (hA.mem_of_centralizes (hN₀L hvN) fun u hu => hcon u hu)
    have hvL : v ∈ L := hN₀L hvN
    have huL : u ∈ L := hA.le huU
    have hw1 : v * u * v⁻¹ * u⁻¹ ≠ 1 := by
      intro h
      apply hvu
      have : v * u * v⁻¹ = u := by
        calc v * u * v⁻¹ = (v * u * v⁻¹ * u⁻¹) * u := by group
          _ = u := by rw [h]; group
      calc v * u = (v * u * v⁻¹) * v := by group
        _ = u * v := by rw [this]
    have hwU : v * u * v⁻¹ * u⁻¹ ∈ U := by
      refine U.mul_mem ?_ (U.inv_mem huU)
      exact (Subgroup.mem_normalizer_iff.mp (hA.le_normalizer' hvL) u).mp huU
    have hwN : v * u * v⁻¹ * u⁻¹ ∈ N₀ := by
      have h1 : u * v⁻¹ * u⁻¹ ∈ N₀ := by
        have := (Subgroup.mem_normalizer_iff.mp (hLN huL) v⁻¹).mp (N₀.inv_mem hvN)
        simpa using this
      have e : v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
      rw [e]
      exact N₀.mul_mem hvN h1
    exact hA.le_of_mem hLN hwN hwU hw1

theorem k32_eq_of_relIndex_le_two {L M₀ : Subgroup G} (hA : IsA4Block L (blockU L))
    (hML : M₀ ≤ L) (hLN : L ≤ Subgroup.normalizer (M₀ : Set G)) (hidx : M₀.relIndex L ≤ 2) :
    M₀ = L := by
  by_contra hne
  have hrel0 : M₀.relIndex L ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel1 : M₀.relIndex L ≠ 1 := fun h => hne (le_antisymm hML (Subgroup.relIndex_eq_one.mp h))
  have hrel2 : M₀.relIndex L = 2 := by omega
  have hcard : Nat.card L = Nat.card M₀ * 2 := by
    rw [C5.card_eq_card_mul_relIndex hML, hrel2]
  have hM6 : Nat.card M₀ = 6 := by
    have := hA.card_L
    omega
  have hUL : blockU L ≤ L := hA.le
  have hUN : blockU L ≤ Subgroup.normalizer (M₀ : Set G) := hUL.trans hLN
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hUN
  rw [hA.card_U, hM6] at hmul
  have hsup : Nat.card ↥(blockU L ⊔ M₀) ≤ 12 := by
    have := Subgroup.card_le_of_le (sup_le hUL hML : blockU L ⊔ M₀ ≤ L)
    rw [hA.card_L] at this
    exact this
  have hinf : 2 ≤ Nat.card ↥(blockU L ⊓ M₀) := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < Nat.card ↥(blockU L ⊓ M₀) := Nat.card_pos
    have h1 : Nat.card ↥(blockU L ⊓ M₀) = 1 := by omega
    rw [h1] at hmul
    omega
  obtain ⟨u, huU, huM, hu1⟩ : ∃ u ∈ blockU L, u ∈ M₀ ∧ u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : blockU L ⊓ M₀ = ⊥ := eq_bot_iff.mpr fun u hu =>
      Subgroup.mem_bot.mpr (by by_contra h; exact absurd (hcon u hu.1 hu.2) h)
    rw [hbot, Subgroup.card_bot] at hinf
    omega
  have hUM : blockU L ≤ M₀ := hA.le_of_mem hLN huM huU hu1
  have hdvd := Subgroup.card_dvd_of_le hUM
  rw [hA.card_U, hM6] at hdvd
  omega

theorem k32_z₁_not_central {T M H S L K : Subgroup G} {s x z₁ z₂ : G}
    (ctx : K32Ctx T M H S L s x z₁ z₂ K) : ¬ ∀ k ∈ K, k * z₁ = z₁ * k := by
  intro hcon
  have hKz : K ≤ centralizerElem z₂ := ctx.comp.1
  have hKzz : K ≤ Subgroup.centralizer ((Subgroup.zpowers (z₁ * z₂) : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h1 : a * z₁ = z₁ * a := hcon a ha
    have h2 : a * z₂ = z₂ * a := Subgroup.mem_centralizer_singleton_iff.mp (hKz ha)
    have h3 : (z₁ * z₂) * a = a * (z₁ * z₂) := by
      calc (z₁ * z₂) * a = z₁ * (z₂ * a) := by group
        _ = z₁ * (a * z₂) := by rw [h2]
        _ = (z₁ * a) * z₂ := by group
        _ = (a * z₁) * z₂ := by rw [h1]
        _ = a * (z₁ * z₂) := by group
    exact ((Commute.zpow_left (show Commute (z₁ * z₂) a from h3) n).eq)
  have hbot : ⁅K, Subgroup.zpowers (z₁ * z₂)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKzz
  have hKbot : K = ⊥ := by rw [← ctx.comm]; exact hbot
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn ctx.comp
  exact (Subgroup.nontrivial_iff_ne_bot K).mp (CFSG.LocalCores.isQuasisimple_nontrivial hq) hKbot

end A4

end CFSG.QuasithinUnique.DoubleA3
