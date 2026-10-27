module

public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.EqualDegreeDifferenceSaturatesAntirealBlocks
import CFSG.FeitThompson.Representations.CoherentImageAntirealBlockSelection
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate

namespace UniformDegreeCoherence

section Span
variable {L : Type*} [One L] {S : Set (L → ℂ)} {χ₀ : L → ℂ} {d : ℂ}

theorem exists_int_apply_one_div (hd : d ≠ 0) (hdeg : ∀ χ ∈ S, χ 1 = d) :
    ∀ f ∈ Submodule.span ℤ S, ∃ m : ℤ, f 1 / d = (m : ℂ) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact ⟨1, by rw [hdeg x hx, div_self hd, Int.cast_one]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by rw [Pi.add_apply, add_div, ha, hb, Int.cast_add]⟩
  | smul a x _ ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨a * m, by rw [Pi.smul_apply, zsmul_eq_mul, mul_div_assoc, hm, Int.cast_mul]⟩

theorem sub_smul_mem_span_sub (hd : d ≠ 0) (hdeg : ∀ χ ∈ S, χ 1 = d) :
    ∀ f ∈ Submodule.span ℤ S,
      f - (f 1 / d) • χ₀ ∈ Submodule.span ℤ ((fun χ => χ₀ - χ) '' S) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
      rw [hdeg x hx, div_self hd, one_smul, show x - χ₀ = -(χ₀ - x) by ring]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero => simp
  | add x y _ _ ihx ihy =>
      rw [show (x + y) - ((x + y) 1 / d) • χ₀
          = (x - (x 1 / d) • χ₀) + (y - (y 1 / d) • χ₀) by
        rw [Pi.add_apply, add_div, add_smul]; ring]
      exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
      rw [show (a • x) - ((a • x) 1 / d) • χ₀ = a • (x - (x 1 / d) • χ₀) by
        rw [smul_sub]
        congr 1
        rw [Pi.smul_apply, zsmul_eq_mul, mul_div_assoc,
          ← Int.cast_smul_eq_zsmul ℂ a ((x 1 / d) • χ₀), smul_smul]]
      exact Submodule.smul_of_tower_mem _ a ih

end Span

theorem conj_sub_mul_natCast {X : Type*} [Fintype X] {χ₀ g : X → ℂ} {n₀ : ℕ} {b : ℂ}
    (hb : conj b = b) :
    conj (b * (n₀ : ℂ) - cfInner g χ₀) = b * (n₀ : ℂ) - cfInner χ₀ g := by
  rw [map_sub, map_mul, hb, Complex.conj_natCast, conj_cfInner]

end UniformDegreeCoherence

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

theorem isCoherent_of_span_eq_bot {S : Set (L → ℂ)} (hS : Submodule.span ℤ S = ⊥)
    (τ : charSpanZero S →+ virtualChars G) : IsCoherent S τ := by
  have hbot : ∀ f : Submodule.span ℤ S, (f : L → ℂ) = 0 := by
    intro f
    have h : (f : L → ℂ) ∈ (⊥ : Submodule ℤ (L → ℂ)) := hS ▸ f.2
    simpa using h
  refine isCoherent_iff.2 ⟨0, ?_, ?_⟩
  · intro f h
    simp [hbot f, hbot h, cfInner_zero_left]
  · intro f
    have hf : f = 0 := Subtype.ext (hbot ⟨(f : L → ℂ), charSpanZero_le _ f.2⟩)
    simp [hf]

variable {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

namespace IsSubcoherent

open UniformDegreeCoherence

theorem cfInner_tau_tau (hc : IsSubcoherent S tau R) {f h : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    (hh : h ∈ intSpanZeroAtOne (S : Set (L → ℂ))) :
    cfInner (tau f) (tau h) = cfInner f h := by
  simp only [← charInner_eq_cfInner]
  exact hc.charInner_tau_tau f hf h hh

theorem cfInner_eq_zero_of_ne (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (hne : χ ≠ ψ) : cfInner χ ψ = 0 := by
  rw [← charInner_eq_cfInner]; exact hc.charInner_eq_zero χ hχ ψ hψ hne

theorem apply_one_ne_zero (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) : χ 1 ≠ 0 :=
  (hc.isCharacter χ hχ).apply_one_ne_zero (hc.ne_zero χ hχ)

theorem exists_pos_nat_cfInner_self (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    ∃ n : ℕ, 0 < n ∧ cfInner χ χ = (n : ℂ) := by
  obtain ⟨V, rfl⟩ := (hc.isCharacter χ hχ).exists_fdRep
  exact CoherentAntirealBlock.exists_pos_nat_cfInner_self (FDRep.character_mem_span_Irr V)
    (hc.ne_zero _ hχ)

theorem cfInner_sum_subset_self (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S)
    {E : Finset (G → ℂ)} (hE : E ⊆ R χ) :
    cfInner (∑ r ∈ E, r) (∑ r ∈ E, r) = (E.card : ℂ) := by
  rw [← charInner_eq_cfInner]
  exact charInner_sum_self_of_orthonormal E (fun r hr => hc.charInner_R_self χ hχ r (hE hr))
    (fun r hr s hs h => hc.charInner_R_of_ne χ hχ r (hE hr) s (hE hs) h)

theorem cfInner_sum_R_sum_subset (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S)
    {E : Finset (G → ℂ)} (hE : E ⊆ R χ) :
    cfInner (∑ r ∈ R χ, r) (∑ r ∈ E, r) = (E.card : ℂ) := by
  rw [cfInner_sum_right]
  have key : ∀ s ∈ E, cfInner (∑ r ∈ R χ, r) s = 1 := by
    intro s hs
    rw [cfInner_sum_left, Finset.sum_eq_single_of_mem s (hE hs)
      (fun r hr hrs => hc.cfInner_R_of_ne hχ r hr s (hE hs) hrs), hc.cfInner_R_self hχ s (hE hs)]
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem cfInner_sum_subset_sum_subset (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (h₁ : ψ ≠ χ) (h₂ : ψ ≠ star χ)
    {E F : Finset (G → ℂ)} (hE : E ⊆ R χ) (hF : F ⊆ R ψ) :
    cfInner (∑ r ∈ E, r) (∑ r ∈ F, r) = 0 := by
  rw [cfInner_sum_left]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [cfInner_sum_right]
  exact Finset.sum_eq_zero fun s hs => hc.cfInner_R_R hχ hψ h₁ h₂ r (hE hr) s (hF hs)

theorem sum_subset_mem_virtualChars (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S)
    {E : Finset (G → ℂ)} (hE : E ⊆ R χ) : (∑ r ∈ E, r) ∈ virtualChars G :=
  Submodule.sum_mem _ fun _ hr =>
    mem_virtualChars_of_mem_span_Irr (hc.R_subset_span_Irr hχ (hE hr))

theorem span_sub_le_intSpanZeroAtOne (hc : IsSubcoherent S tau R)
    (hdeg : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1) {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ S) :
    Submodule.span ℤ ((fun χ => χ₀ - χ) '' (S : Set (L → ℂ)))
      ≤ intSpanZeroAtOne (S : Set (L → ℂ)) := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨χ, hχ, rfl⟩
  exact hc.sub_mem_of_apply_one_eq hχ₀ hχ (hdeg χ₀ hχ₀ χ hχ)

theorem smul_sub_mem_intSpanZeroAtOne (hc : IsSubcoherent S tau R)
    (hdeg : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1) {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ S)
    {f : L → ℂ} (hf : f ∈ Submodule.span ℤ (S : Set (L → ℂ))) :
    (f 1 / χ₀ 1) • χ₀ - f ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := by
  have h := sub_smul_mem_span_sub (χ₀ := χ₀) (hc.apply_one_ne_zero hχ₀)
    (fun χ hχ => hdeg χ hχ χ₀ hχ₀) f hf
  rw [show (f 1 / χ₀ 1) • χ₀ - f = -(f - (f 1 / χ₀ 1) • χ₀) by ring]
  exact Submodule.neg_mem _ (hc.span_sub_le_intSpanZeroAtOne hdeg hχ₀ h)

theorem exists_pivot (hc : IsSubcoherent S tau R)
    (hdeg : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1) {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ S)
    {n₀ : ℕ} (hn₀ : cfInner χ₀ χ₀ = (n₀ : ℂ)) :
    ∃ E₀ ⊆ R χ₀, E₀.card = n₀ ∧ ∀ γ ∈ S,
      cfInner (tau (χ₀ - γ)) (∑ r ∈ E₀, r) = (n₀ : ℂ) - cfInner γ χ₀ := by
  classical
  have hsχ₀ : star χ₀ ∈ S := hc.star_mem χ₀ hχ₀
  have hn₀' : charInner χ₀ χ₀ = (n₀ : ℂ) := by rw [charInner_eq_cfInner]; exact hn₀
  have hcase₁ : ∀ E₀ ⊆ R χ₀, E₀.card = n₀ →
      cfInner (tau (χ₀ - χ₀)) (∑ r ∈ E₀, r) = (n₀ : ℂ) - cfInner χ₀ χ₀ := by
    intro E₀ _ _
    rw [sub_self, hc.tau_zero, cfInner_zero_left, hn₀, sub_self]
  have hcase₂ : ∀ E₀ ⊆ R χ₀, E₀.card = n₀ →
      cfInner (tau (χ₀ - star χ₀)) (∑ r ∈ E₀, r) = (n₀ : ℂ) - cfInner (star χ₀) χ₀ := by
    intro E₀ hE₀ hcard
    rw [hc.tau_sub_star χ₀ hχ₀, hc.cfInner_sum_R_sum_subset hχ₀ hE₀, hcard,
      hc.cfInner_eq_zero_of_ne hsχ₀ hχ₀ (hc.star_ne χ₀ hχ₀), sub_zero]
  by_cases hex : ∃ ψ ∈ S, ψ ≠ χ₀ ∧ ψ ≠ star χ₀
  ·
    obtain ⟨ψ, hψ, hψ₁, hψ₂⟩ := hex
    have hχ₀ψ : χ₀ ≠ ψ := Ne.symm hψ₁
    have hχ₀sψ : χ₀ ≠ star ψ := fun h => hψ₂ (by rw [h, star_star])
    obtain ⟨E, hE, F, hF, hEcard, -, hsplit, -, -⟩ :=
      hc.exists_subset_sum_sub_sum_eq_tau_sub hχ₀ hψ hψ₁ hψ₂ (hdeg χ₀ hχ₀ ψ hψ)
    have hEcard' : E.card = n₀ := by
      have h : ((E.card : ℕ) : ℂ) = ((n₀ : ℕ) : ℂ) := by rw [hEcard, hn₀']
      exact_mod_cast h
    refine ⟨E, hE, hEcard', ?_⟩
    have hEsum : (∑ r ∈ E, r) = tau (χ₀ - ψ) + ∑ r ∈ F, r := by rw [hsplit]; ring
    have hatψ : cfInner (tau (χ₀ - ψ)) (∑ r ∈ E, r) = (n₀ : ℂ) := by
      rw [hsplit, cfInner_sub_left, hc.cfInner_sum_subset_self hχ₀ hE, hEcard',
        hc.cfInner_sum_subset_sum_subset hψ hχ₀ hχ₀ψ hχ₀sψ hF hE, sub_zero]
    intro γ hγ
    by_cases hγ₁ : γ = χ₀
    · subst hγ₁; exact hcase₁ E hE hEcard'
    by_cases hγ₂ : γ = star χ₀
    · subst hγ₂; exact hcase₂ E hE hEcard'
    rw [hc.cfInner_eq_zero_of_ne hγ hχ₀ hγ₁, sub_zero]
    have hχ₀sγ : χ₀ ≠ star γ := fun h => hγ₂ (by rw [h, star_star])
    by_cases hγψ : γ = ψ
    · subst hγψ; exact hatψ
    by_cases hγsψ : γ = star ψ
    ·
      subst hγsψ
      rw [show χ₀ - star ψ = (χ₀ - ψ) + (ψ - star ψ) by ring,
        hc.map_add _ (hc.sub_mem_of_apply_one_eq hχ₀ hψ (hdeg χ₀ hχ₀ ψ hψ))
          _ (hc.sub_star_mem hψ), hc.tau_sub_star ψ hψ, cfInner_add_left, hatψ,
        hc.cfInner_sum_subset_sum_subset hψ hχ₀ hχ₀ψ hχ₀sψ (subset_refl _) hE, add_zero]
    ·
      obtain ⟨Eγ, hEγ, Fγ, hFγ, -, -, hsplitγ, -, -⟩ :=
        hc.exists_subset_sum_sub_sum_eq_tau_sub hχ₀ hγ hγ₁ hγ₂ (hdeg χ₀ hχ₀ γ hγ)
      have hisom : cfInner (tau (χ₀ - γ)) (tau (χ₀ - ψ)) = (n₀ : ℂ) := by
        rw [hc.cfInner_tau_tau (hc.sub_mem_of_apply_one_eq hχ₀ hγ (hdeg χ₀ hχ₀ γ hγ))
          (hc.sub_mem_of_apply_one_eq hχ₀ hψ (hdeg χ₀ hχ₀ ψ hψ))]
        simp only [cfInner_sub_left, cfInner_sub_right]
        rw [hn₀, hc.cfInner_eq_zero_of_ne hχ₀ hψ hχ₀ψ, hc.cfInner_eq_zero_of_ne hγ hχ₀ hγ₁,
          hc.cfInner_eq_zero_of_ne hγ hψ hγψ]
        ring
      have hcross : cfInner (tau (χ₀ - γ)) (∑ r ∈ F, r) = 0 := by
        rw [hsplitγ, cfInner_sub_left,
          hc.cfInner_sum_subset_sum_subset hχ₀ hψ hψ₁ hψ₂ hEγ hF,
          hc.cfInner_sum_subset_sum_subset hγ hψ (Ne.symm hγψ)
            (fun h => hγsψ (by rw [h, star_star])) hFγ hF, sub_zero]
      rw [hEsum, cfInner_add_right, hisom, hcross, add_zero]
  ·
    have hcard_R : (R χ₀).card = 2 * n₀ := by
      have h := hc.card_R hχ₀
      rw [hn₀'] at h
      have h2 : ((R χ₀).card : ℂ) = ((2 * n₀ : ℕ) : ℂ) := by push_cast; rw [h]
      exact_mod_cast h2
    obtain ⟨E₀, hE₀, hE₀card⟩ := Finset.exists_subset_card_eq (s := R χ₀) (n := n₀) (by omega)
    refine ⟨E₀, hE₀, hE₀card, fun γ hγ => ?_⟩
    by_cases hγ₁ : γ = χ₀
    · subst hγ₁; exact hcase₁ E₀ hE₀ hE₀card
    by_cases hγ₂ : γ = star χ₀
    · subst hγ₂; exact hcase₂ E₀ hE₀ hE₀card
    · exact absurd ⟨γ, hγ, hγ₁, hγ₂⟩ hex

theorem cfInner_tau_smul_sub (hc : IsSubcoherent S tau R)
    (hdeg : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1) {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ S)
    {n₀ : ℕ} (X : G → ℂ)
    (hpivot : ∀ γ ∈ S, cfInner (tau (χ₀ - γ)) X = (n₀ : ℂ) - cfInner γ χ₀) :
    ∀ f ∈ Submodule.span ℤ (S : Set (L → ℂ)),
      cfInner (tau ((f 1 / χ₀ 1) • χ₀ - f)) X = (f 1 / χ₀ 1) * (n₀ : ℂ) - cfInner f χ₀ := by
  have hd : χ₀ 1 ≠ 0 := hc.apply_one_ne_zero hχ₀
  have hmem := fun f hf => hc.smul_sub_mem_intSpanZeroAtOne (χ₀ := χ₀) hdeg hχ₀ (f := f) hf
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
      rw [hdeg x hx χ₀ hχ₀, div_self hd, one_smul, one_mul]
      exact hpivot x hx
  | zero => simp [hc.tau_zero, cfInner_zero_left]
  | add x y hx hy ihx ihy =>
      rw [show ((x + y) 1 / χ₀ 1) • χ₀ - (x + y)
          = ((x 1 / χ₀ 1) • χ₀ - x) + ((y 1 / χ₀ 1) • χ₀ - y) by
        funext t
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_div]
        ring,
        hc.map_add _ (hmem x hx) _ (hmem y hy), cfInner_add_left, ihx, ihy,
        Pi.add_apply, add_div, cfInner_add_left]
      ring
  | smul a x hx ih =>
      rw [show ((a • x) 1 / χ₀ 1) • χ₀ - (a • x) = a • ((x 1 / χ₀ 1) • χ₀ - x) by
        rw [smul_sub]
        congr 1
        rw [Pi.smul_apply, zsmul_eq_mul, mul_div_assoc,
          ← Int.cast_smul_eq_zsmul ℂ a ((x 1 / χ₀ 1) • χ₀), smul_smul],
        hc.map_zsmul a (hmem x hx), cfInner_zsmul_left, ih,
        Pi.smul_apply, zsmul_eq_mul, cfInner_zsmul_left, mul_div_assoc]
      ring

theorem cfInner_smul_sub_tau_smul_sub (hc : IsSubcoherent S tau R) {χ₀ : L → ℂ}
    {n₀ : ℕ} (hn₀ : cfInner χ₀ χ₀ = (n₀ : ℂ)) {X : G → ℂ} (hXX : cfInner X X = (n₀ : ℂ))
    {f g : L → ℂ} {a b : ℂ} (hb : conj b = b)
    (hA : a • χ₀ - f ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    (hB : b • χ₀ - g ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    (hpA : cfInner (tau (a • χ₀ - f)) X = a * (n₀ : ℂ) - cfInner f χ₀)
    (hpB : cfInner (tau (b • χ₀ - g)) X = b * (n₀ : ℂ) - cfInner g χ₀) :
    cfInner (a • X - tau (a • χ₀ - f)) (b • X - tau (b • χ₀ - g)) = cfInner f g := by
  have hXB : cfInner X (tau (b • χ₀ - g)) = b * (n₀ : ℂ) - cfInner χ₀ g := by
    rw [← conj_cfInner (tau (b • χ₀ - g)) X, hpB, conj_sub_mul_natCast hb]
  have hAB : cfInner (tau (a • χ₀ - f)) (tau (b • χ₀ - g))
      = a * b * (n₀ : ℂ) - a * cfInner χ₀ g - b * cfInner f χ₀ + cfInner f g := by
    rw [hc.cfInner_tau_tau hA hB]
    simp only [cfInner_sub_left, cfInner_sub_right, cfInner_smul_left, cfInner_smul_right, hb, hn₀]
    ring
  simp only [cfInner_sub_left, cfInner_sub_right, cfInner_smul_left, cfInner_smul_right, hb]
  rw [hXX, hXB, hpA, hAB]
  ring

theorem exists_isCoherentWith_sum_sub_tau_sub (hc : IsSubcoherent S tau R)
    (τS : charSpanZero (S : Set (L → ℂ)) →+ virtualChars G)
    (hτS : ∀ f : charSpanZero (S : Set (L → ℂ)), (τS f : G → ℂ) = tau (f : L → ℂ))
    (hdeg : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1) {χ₀ : L → ℂ} (hχ₀ : χ₀ ∈ S) :
    ∃ n₀ : ℕ, cfInner χ₀ χ₀ = (n₀ : ℂ) ∧ ∃ E₀ ⊆ R χ₀, E₀.card = n₀ ∧
      ∃ ν : Submodule.span ℤ (S : Set (L → ℂ)) →+ virtualChars G,
        IsCoherentWith (S : Set (L → ℂ)) τS ν ∧
        ∀ χ ∈ S, ∀ hχ : χ ∈ Submodule.span ℤ (S : Set (L → ℂ)),
          (ν ⟨χ, hχ⟩ : G → ℂ) = (∑ r ∈ E₀, r) - tau (χ₀ - χ) := by
  classical
  obtain ⟨n₀, -, hn₀⟩ := hc.exists_pos_nat_cfInner_self hχ₀
  obtain ⟨E₀, hE₀, hE₀card, hpivot⟩ := hc.exists_pivot hdeg hχ₀ hn₀
  refine ⟨n₀, hn₀, E₀, hE₀, hE₀card, ?_⟩
  set d : ℂ := χ₀ 1 with hdd
  have hd : d ≠ 0 := hc.apply_one_ne_zero hχ₀
  set X : G → ℂ := ∑ r ∈ E₀, r with hXdef
  have hXX : cfInner X X = (n₀ : ℂ) := by
    rw [hXdef, hc.cfInner_sum_subset_self hχ₀ hE₀, hE₀card]
  have hXmem : X ∈ virtualChars G := hc.sum_subset_mem_virtualChars hχ₀ hE₀
  have hmem : ∀ f ∈ Submodule.span ℤ (S : Set (L → ℂ)),
      (f 1 / d) • χ₀ - f ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    fun f hf => hc.smul_sub_mem_intSpanZeroAtOne hdeg hχ₀ hf
  have hint : ∀ f ∈ Submodule.span ℤ (S : Set (L → ℂ)), ∃ m : ℤ, f 1 / d = (m : ℂ) :=
    exists_int_apply_one_div hd fun χ hχ => hdeg χ hχ χ₀ hχ₀
  have hpivot' := hc.cfInner_tau_smul_sub hdeg hχ₀ X hpivot
  have hmemν : ∀ f : Submodule.span ℤ (S : Set (L → ℂ)),
      (((f : L → ℂ) 1 / d) • X - tau (((f : L → ℂ) 1 / d) • χ₀ - (f : L → ℂ)))
        ∈ virtualChars G := by
    intro f
    refine Submodule.sub_mem _ ?_ ?_
    · obtain ⟨m, hm⟩ := hint _ f.2
      rw [hm, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_of_tower_mem _ m hXmem
    · exact mem_virtualChars_of_mem_span_Irr (hc.tau_mem_span_Irr (hmem _ f.2))
  have hadd : ∀ f g : Submodule.span ℤ (S : Set (L → ℂ)),
      (((f + g : Submodule.span ℤ (S : Set (L → ℂ))) : L → ℂ) 1 / d) • X
          - tau ((((f + g : Submodule.span ℤ (S : Set (L → ℂ))) : L → ℂ) 1 / d) • χ₀
            - ((f + g : Submodule.span ℤ (S : Set (L → ℂ))) : L → ℂ))
        = (((f : L → ℂ) 1 / d) • X - tau (((f : L → ℂ) 1 / d) • χ₀ - (f : L → ℂ)))
          + (((g : L → ℂ) 1 / d) • X - tau (((g : L → ℂ) 1 / d) • χ₀ - (g : L → ℂ))) := by
    intro f g
    push_cast
    rw [show (((f : L → ℂ) + (g : L → ℂ)) 1 / d) • χ₀ - ((f : L → ℂ) + (g : L → ℂ))
        = (((f : L → ℂ) 1 / d) • χ₀ - (f : L → ℂ))
          + (((g : L → ℂ) 1 / d) • χ₀ - (g : L → ℂ)) by
      funext t
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_div]
      ring,
      hc.map_add _ (hmem _ f.2) _ (hmem _ g.2)]
    simp only [Pi.add_apply, add_div, add_smul]
    abel
  refine ⟨AddMonoidHom.mk' (fun f => ⟨_, hmemν f⟩) fun f g => Subtype.ext (hadd f g), ?_, ?_⟩
  refine ⟨?_, ?_⟩
  ·
    intro f g
    obtain ⟨mg, hmg⟩ := hint _ g.2
    exact hc.cfInner_smul_sub_tau_smul_sub hn₀ hXX (by rw [hmg]; simp)
      (hmem _ f.2) (hmem _ g.2) (hpivot' _ f.2) (hpivot' _ g.2)
  ·
    intro f
    refine Subtype.ext ?_
    rw [hτS f]
    have h0 : (f : L → ℂ) 1 = 0 := charSpanZero_apply_one f
    have hfmem : (f : L → ℂ) ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
      mem_intSpanZeroAtOne.2 ⟨charSpanZero_le _ f.2, h0⟩
    change ((f : L → ℂ) 1 / d) • X - tau (((f : L → ℂ) 1 / d) • χ₀ - (f : L → ℂ))
      = tau (f : L → ℂ)
    rw [h0, zero_div, zero_smul, zero_smul, zero_sub, zero_sub, hc.map_neg hfmem, neg_neg]
  ·
    intro χ hχ hχspan
    change ((χ : L → ℂ) 1 / d) • X - tau (((χ : L → ℂ) 1 / d) • χ₀ - χ) = X - tau (χ₀ - χ)
    rw [hdeg χ hχ χ₀ hχ₀, hdd, div_self hd, one_smul, one_smul]

theorem isCoherent_of_uniform_degree (hc : IsSubcoherent S tau R)
    (τS : charSpanZero (S : Set (L → ℂ)) →+ virtualChars G)
    (hτS : ∀ f : charSpanZero (S : Set (L → ℂ)), (τS f : G → ℂ) = tau (f : L → ℂ))
    (hdeg : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1) :
    IsCoherent (S : Set (L → ℂ)) τS := by
  rcases Finset.eq_empty_or_nonempty S with rfl | ⟨χ₀, hχ₀⟩
  · exact isCoherent_of_span_eq_bot (by rw [Finset.coe_empty, Submodule.span_empty]) τS
  · obtain ⟨-, -, -, -, -, ν, hν, -⟩ :=
      hc.exists_isCoherentWith_sum_sub_tau_sub τS hτS hdeg hχ₀
    exact hν.isCoherent

end IsSubcoherent

end CFSG.FeitThompson
