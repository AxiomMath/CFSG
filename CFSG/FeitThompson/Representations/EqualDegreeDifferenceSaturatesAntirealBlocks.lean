module

public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.IntegralOrthonormalBlockProjection
import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open CategoryTheory

theorem charInner_eq_cfInner {X : Type*} [Fintype X] (f h : X → ℂ) :
    charInner f h = cfInner f h := by
  rw [charInner_def, cfInner_def, Nat.card_eq_fintype_card]

theorem isIrreducible_of_simple {G : Type*} [Group G] [Finite G] (V : FDRep ℂ G) [Simple V] :
    Representation.IsIrreducible V.ρ := by
  have : Fintype G := Fintype.ofFinite G
  have hcard : ((Nat.card G : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Invertible ((Nat.card G : ℂ)) := invertibleOfNonzero hcard
  have h := FDRep.char_orthonormal V V
  rw [if_pos ⟨Iso.refl V⟩] at h
  have hch : Representation.character (V.ρ) = V.character := rfl
  rw [isIrreducible_iff_cfInner_self_eq_one, cfInner_def, hch]
  have hinv : ∀ g : G, (starRingEnd ℂ) (V.character g) = V.character g⁻¹ := fun g => by
    rw [← hch, Representation.character_inv (V.ρ) (isOfFinOrder_of_finite g)]
  simp only [hinv]
  exact h

theorem virtualCharSpan_le_span_Irr (G : Type*) [Group G] [Finite G] :
    virtualCharSpan G ≤ Submodule.span ℤ (Irr G) :=
  virtualCharSpan_le fun V hV =>
    Submodule.subset_span (character_mem_Irr V (@isIrreducible_of_simple _ _ _ V hV))

variable {G : Type*} [Group G] [Fintype G]

omit [Group G] in
theorem exists_subset_sum_eq_of_cfInner_eq_zero_or_one {B : Finset (G → ℂ)} {d : G → ℂ} {c : ℂ}
    (h01 : ∀ r ∈ B, cfInner d r = 0 ∨ cfInner d r = 1)
    (hsum : ∑ r ∈ B, cfInner d r = c) :
    ∃ E ⊆ B, (E.card : ℂ) = c ∧ ∑ r ∈ B, cfInner d r • r = ∑ r ∈ E, r := by
  classical
  refine ⟨B.filter fun r => cfInner d r = 1, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [← hsum, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun r hr => ?_
    rcases h01 r hr with h | h <;> simp [h]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r hr => ?_
    rcases h01 r hr with h | h <;> simp [h]

variable {L : Type*} [Group L] [Fintype L]
variable {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

namespace IsSubcoherent

theorem sub_mem_of_apply_one_eq (_hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (hdeg : χ 1 = ψ 1) :
    χ - ψ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
  mem_intSpanZeroAtOne.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
    (Submodule.subset_span hψ), by simp [hdeg]⟩

theorem cfInner_tau_sub_self (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (hne : ψ ≠ χ) (hdeg : χ 1 = ψ 1) :
    cfInner (tau (χ - ψ)) (tau (χ - ψ)) = cfInner χ χ + cfInner ψ ψ := by
  have hmem := hc.sub_mem_of_apply_one_eq hχ hψ hdeg
  rw [← charInner_eq_cfInner, hc.charInner_tau_tau _ hmem _ hmem,
    charInner_sub_left, charInner_sub_right, charInner_sub_right,
    hc.charInner_eq_zero χ hχ ψ hψ (Ne.symm hne), hc.charInner_eq_zero ψ hψ χ hχ hne,
    charInner_eq_cfInner, charInner_eq_cfInner]
  ring

theorem sum_cfInner_tau_sub_R (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (hne : ψ ≠ χ) (hne' : ψ ≠ star χ) (hdeg : χ 1 = ψ 1) :
    ∑ r ∈ R χ, cfInner (tau (χ - ψ)) r = cfInner χ χ := by
  have hmem := hc.sub_mem_of_apply_one_eq hχ hψ hdeg
  have hsχ : star χ ∈ S := hc.star_mem χ hχ
  rw [← cfInner_sum_right, ← hc.tau_sub_star χ hχ, ← charInner_eq_cfInner,
    hc.charInner_tau_tau _ hmem _ (hc.sub_star_mem hχ),
    charInner_sub_left, charInner_sub_right, charInner_sub_right,
    hc.charInner_eq_zero χ hχ _ hsχ (Ne.symm (hc.star_ne χ hχ)),
    hc.charInner_eq_zero ψ hψ χ hχ hne, hc.charInner_eq_zero ψ hψ _ hsχ hne',
    charInner_eq_cfInner]
  ring

theorem tau_mem_span_Irr (hc : IsSubcoherent S tau R) {f : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ))) : tau f ∈ Submodule.span ℤ (Irr G) :=
  virtualCharSpan_le_span_Irr G (hc.tau_mem f hf)

theorem R_subset_span_Irr (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    ↑(R χ) ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) :=
  fun _ hr => virtualCharSpan_le_span_Irr G (hc.R_subset χ hχ _ hr)

theorem cfInner_R_self (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    ∀ r ∈ R χ, cfInner r r = 1 := fun r hr => by
  rw [← charInner_eq_cfInner]; exact hc.charInner_R_self χ hχ r hr

theorem cfInner_R_of_ne (hc : IsSubcoherent S tau R) {χ : L → ℂ} (hχ : χ ∈ S) :
    ∀ r ∈ R χ, ∀ s ∈ R χ, r ≠ s → cfInner r s = 0 := fun r hr s hs hne => by
  rw [← charInner_eq_cfInner]; exact hc.charInner_R_of_ne χ hχ r hr s hs hne

theorem cfInner_R_R (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ} (hχ : χ ∈ S) (hψ : ψ ∈ S)
    (h₁ : ψ ≠ χ) (h₂ : ψ ≠ star χ) : ∀ r ∈ R χ, ∀ s ∈ R ψ, cfInner r s = 0 :=
  fun r hr s hs => by
  rw [← charInner_eq_cfInner]; exact hc.charInner_R_R χ hχ ψ hψ h₁ h₂ r hr s hs

open IntegralBlockProjection in
theorem coeff_eq_zero_or_one_and_tau_sub_eq (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (h₁ : ψ ≠ χ) (h₂ : ψ ≠ star χ) (hdeg : χ 1 = ψ 1) :
    (∀ r ∈ R χ, cfInner (tau (χ - ψ)) r = 0 ∨ cfInner (tau (χ - ψ)) r = 1) ∧
      (∀ s ∈ R ψ, cfInner (-tau (χ - ψ)) s = 0 ∨ cfInner (-tau (χ - ψ)) s = 1) ∧
      tau (χ - ψ) = ∑ r ∈ R χ, cfInner (tau (χ - ψ)) r • r
        - ∑ s ∈ R ψ, cfInner (-tau (χ - ψ)) s • s := by
  classical
  set d := tau (χ - ψ) with hd
  have hmem := hc.sub_mem_of_apply_one_eq hχ hψ hdeg
  have hdspan : d ∈ Submodule.span ℤ (Irr G) := hc.tau_mem_span_Irr hmem
  have h₁' : χ ≠ ψ := Ne.symm h₁
  have h₂' : χ ≠ star ψ := fun h => h₂ (by rw [h, star_star])
  have hcross : ∀ r ∈ R χ, ∀ s ∈ R ψ, cfInner r s = 0 := hc.cfInner_R_R hχ hψ h₁ h₂
  have hcross' : ∀ s ∈ R ψ, ∀ r ∈ R χ, cfInner s r = 0 := hc.cfInner_R_R hψ hχ h₁' h₂'
  have hnegd : tau (ψ - χ) = -d := by
    have h := hc.map_neg hmem
    rwa [neg_sub] at h
  set T : Finset (G → ℂ) := R χ ∪ (R ψ).image (fun s => -s) with hT
  have hdisj : Disjoint (R χ) ((R ψ).image (fun s => -s)) := by
    refine Finset.disjoint_left.2 fun r hr hr' => ?_
    obtain ⟨s, hs, hrs⟩ := Finset.mem_image.1 hr'
    have h0 : cfInner r s = 0 := hcross r hr s hs
    rw [← hrs, cfInner_neg_left, hc.cfInner_R_self hψ s hs] at h0
    exact one_ne_zero (neg_eq_zero.1 h0)
  have hmemT : ∀ r ∈ T, r ∈ R χ ∨ ∃ s ∈ R ψ, r = -s := by
    intro r hr
    rcases Finset.mem_union.1 hr with h | h
    · exact Or.inl h
    · obtain ⟨s, hs, hrs⟩ := Finset.mem_image.1 h
      exact Or.inr ⟨s, hs, hrs.symm⟩
  have hT_one : ∀ r ∈ T, cfInner r r = 1 := by
    intro r hr
    rcases hmemT r hr with h | ⟨s, hs, rfl⟩
    · exact hc.cfInner_R_self hχ r h
    · rw [cfInner_neg_left, cfInner_neg_right, neg_neg, hc.cfInner_R_self hψ s hs]
  have hT_zero : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → cfInner r s = 0 := by
    intro r hr s hs hne
    rcases hmemT r hr with hr' | ⟨r', hr', rfl⟩ <;> rcases hmemT s hs with hs' | ⟨s', hs', rfl⟩
    · exact hc.cfInner_R_of_ne hχ r hr' s hs' hne
    · rw [cfInner_neg_right, hcross r hr' s' hs', neg_zero]
    · rw [cfInner_neg_left, hcross' r' hr' s hs', neg_zero]
    · rw [cfInner_neg_left, cfInner_neg_right, neg_neg,
        hc.cfInner_R_of_ne hψ r' hr' s' hs' (fun h => hne (by rw [h]))]
  have hT_span : ↑T ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) := by
    intro r hr
    rcases hmemT r hr with h | ⟨s, hs, rfl⟩
    · exact hc.R_subset_span_Irr hχ h
    · exact Submodule.neg_mem _ (hc.R_subset_span_Irr hψ hs)
  have hsumχ : ∑ r ∈ R χ, cfInner d r = cfInner χ χ :=
    hc.sum_cfInner_tau_sub_R hχ hψ h₁ h₂ hdeg
  have hsumψ : ∑ s ∈ R ψ, cfInner (-d) s = cfInner ψ ψ := by
    rw [← hnegd]; exact hc.sum_cfInner_tau_sub_R hψ hχ h₁' h₂' hdeg.symm
  have hsumT : ∑ r ∈ T, cfInner d r = cfInner χ χ + cfInner ψ ψ := by
    rw [hT, Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => neg_injective h),
      hsumχ, ← hsumψ]
    exact congrArg _ (Finset.sum_congr rfl fun s _ => by
      rw [cfInner_neg_right, cfInner_neg_left])
  have hdd : cfInner d d = cfInner χ χ + cfInner ψ ψ :=
    hc.cfInner_tau_sub_self hχ hψ h₁ hdeg
  obtain ⟨a, ha⟩ := exists_int_cfInner_forall_mem hT_span hdspan
  have hn : cfInner d d = ((∑ r ∈ T, a r : ℤ) : ℂ) := by
    rw [hdd, ← hsumT, sum_cfInner_eq_intCast ha]
  obtain ⟨h01, hdP⟩ := eq_sum_cfInner_smul_of_cfInner_self_eq hT_one hT_zero ha hn
  have h01' : ∀ r ∈ T, cfInner d r = 0 ∨ cfInner d r = 1 := by
    intro r hr
    rcases h01 r hr with h | h
    · exact Or.inl (by rw [ha r hr, h, Int.cast_zero])
    · exact Or.inr (by rw [ha r hr, h, Int.cast_one])
  have hstep : ∀ s : G → ℂ, cfInner d (-s) • (-s) = -(cfInner (-d) s • s) := fun s => by
    rw [cfInner_neg_right, cfInner_neg_left]; module
  refine ⟨fun r hr => h01' r (Finset.mem_union_left _ hr), fun s hs => ?_, ?_⟩
  · have h := h01' (-s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))
    rwa [cfInner_neg_right, ← cfInner_neg_left] at h
  · calc d = ∑ r ∈ T, cfInner d r • r := hdP
      _ = ∑ r ∈ R χ, cfInner d r • r + ∑ s ∈ R ψ, cfInner d (-s) • (-s) := by
          rw [hT, Finset.sum_union hdisj,
            Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
      _ = ∑ r ∈ R χ, cfInner d r • r - ∑ s ∈ R ψ, cfInner (-d) s • s := by
          rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
          exact congrArg _ (Finset.sum_congr rfl fun s _ => hstep s)

theorem exists_subset_sum_sub_sum_eq_tau_sub (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (h₁ : ψ ≠ χ) (h₂ : ψ ≠ star χ) (hdeg : χ 1 = ψ 1) :
    ∃ E ⊆ R χ, ∃ F ⊆ R ψ,
      (E.card : ℂ) = charInner χ χ ∧ (F.card : ℂ) = charInner ψ ψ ∧
      tau (χ - ψ) = ∑ r ∈ E, r - ∑ r ∈ F, r ∧
      ∑ r ∈ E, r = ∑ r ∈ R χ, charInner (tau (χ - ψ)) r • r ∧
      ∑ r ∈ F, r = ∑ r ∈ R ψ, charInner (-tau (χ - ψ)) r • r := by
  have h₁' : χ ≠ ψ := Ne.symm h₁
  have h₂' : χ ≠ star ψ := fun h => h₂ (by rw [h, star_star])
  obtain ⟨hχ01, hψ01, hsplit⟩ :=
    hc.coeff_eq_zero_or_one_and_tau_sub_eq hχ hψ h₁ h₂ hdeg
  obtain ⟨E, hE, hEcard, hEsum⟩ := exists_subset_sum_eq_of_cfInner_eq_zero_or_one hχ01
    (hc.sum_cfInner_tau_sub_R hχ hψ h₁ h₂ hdeg)
  have hneg : tau (ψ - χ) = -tau (χ - ψ) := by
    have h' := hc.map_neg (hc.sub_mem_of_apply_one_eq hχ hψ hdeg)
    rwa [neg_sub] at h'
  have hsumψ : ∑ s ∈ R ψ, cfInner (-tau (χ - ψ)) s = cfInner ψ ψ := by
    rw [← hneg]; exact hc.sum_cfInner_tau_sub_R hψ hχ h₁' h₂' hdeg.symm
  obtain ⟨F, hF, hFcard, hFsum⟩ :=
    exists_subset_sum_eq_of_cfInner_eq_zero_or_one hψ01 hsumψ
  refine ⟨E, hE, F, hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEcard, charInner_eq_cfInner]
  · rw [hFcard, charInner_eq_cfInner]
  · rw [← hEsum, ← hFsum]; exact hsplit
  · simp only [charInner_eq_cfInner]; exact hEsum.symm
  · simp only [charInner_eq_cfInner]; exact hFsum.symm

theorem eq_of_sum_sub_sum_eq (hc : IsSubcoherent S tau R) {χ ψ : L → ℂ}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) (h₁ : ψ ≠ χ) (h₂ : ψ ≠ star χ)
    {E E' F F' : Finset (G → ℂ)} (hE : E ⊆ R χ) (hE' : E' ⊆ R χ) (hF : F ⊆ R ψ) (hF' : F' ⊆ R ψ)
    (h : ∑ r ∈ E, r - ∑ r ∈ F, r = ∑ r ∈ E', r - ∑ r ∈ F', r) : E = E' ∧ F = F' := by
  classical
  have h₁' : χ ≠ ψ := Ne.symm h₁
  have h₂' : χ ≠ star ψ := fun hh => h₂ (by rw [hh, star_star])
  have key : ∀ {α : L → ℂ}, α ∈ S → ∀ {A : Finset (G → ℂ)}, A ⊆ R α → ∀ r ∈ R α,
      cfInner (∑ s ∈ A, s) r = if r ∈ A then 1 else 0 := by
    intro α hα A hA r hr
    rw [cfInner_sum_left]
    by_cases hrA : r ∈ A
    · rw [if_pos hrA, Finset.sum_eq_single_of_mem r hrA
        fun s hs hsr => hc.cfInner_R_of_ne hα s (hA hs) r hr hsr, hc.cfInner_R_self hα r hr]
    · rw [if_neg hrA]
      exact Finset.sum_eq_zero fun s hs =>
        hc.cfInner_R_of_ne hα s (hA hs) r hr fun hsr => hrA (hsr ▸ hs)
  have crossχ : ∀ {A : Finset (G → ℂ)}, A ⊆ R ψ → ∀ r ∈ R χ, cfInner (∑ s ∈ A, s) r = 0 := by
    intro A hA r hr
    rw [cfInner_sum_left]
    exact Finset.sum_eq_zero fun s hs => hc.cfInner_R_R hψ hχ h₁' h₂' s (hA hs) r hr
  have crossψ : ∀ {A : Finset (G → ℂ)}, A ⊆ R χ → ∀ r ∈ R ψ, cfInner (∑ s ∈ A, s) r = 0 := by
    intro A hA r hr
    rw [cfInner_sum_left]
    exact Finset.sum_eq_zero fun s hs => hc.cfInner_R_R hχ hψ h₁ h₂ s (hA hs) r hr
  constructor
  · refine Finset.ext fun r => ?_
    by_cases hr : r ∈ R χ
    · have hh := congrArg (fun f => cfInner f r) h
      simp only [cfInner_sub_left, key hχ hE r hr, key hχ hE' r hr, crossχ hF r hr,
        crossχ hF' r hr, sub_zero] at hh
      constructor
      · intro hmem
        by_contra hmem'
        rw [if_pos hmem, if_neg hmem'] at hh
        exact one_ne_zero hh
      · intro hmem'
        by_contra hmem
        rw [if_neg hmem, if_pos hmem'] at hh
        exact zero_ne_one hh
    · exact ⟨fun hmem => absurd (hE hmem) hr, fun hmem => absurd (hE' hmem) hr⟩
  · refine Finset.ext fun r => ?_
    by_cases hr : r ∈ R ψ
    · have hh := congrArg (fun f => cfInner f r) h
      simp only [cfInner_sub_left, key hψ hF r hr, key hψ hF' r hr, crossψ hE r hr,
        crossψ hE' r hr, zero_sub, neg_inj] at hh
      constructor
      · intro hmem
        by_contra hmem'
        rw [if_pos hmem, if_neg hmem'] at hh
        exact one_ne_zero hh
      · intro hmem'
        by_contra hmem
        rw [if_neg hmem, if_pos hmem'] at hh
        exact zero_ne_one hh
    · exact ⟨fun hmem => absurd (hF hmem) hr, fun hmem => absurd (hF' hmem) hr⟩

end IsSubcoherent

end CFSG.FeitThompson
