module

public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.IntegralOrthonormalBlockProjection
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CoherentAntirealBlock

open ComplexOrder IntegralBlockProjection

theorem charInner_eq_cfInner {X : Type*} [Fintype X] (f h : X → ℂ) :
    charInner f h = cfInner f h := by
  rw [charInner_def, cfInner_def, Nat.card_eq_fintype_card]

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S T : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
  {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G} {χ : L → ℂ}

omit [Group L] [Fintype L] in
theorem mem_span_of_mem (hχ : χ ∈ T) : χ ∈ Submodule.span ℤ (T : Set (L → ℂ)) :=
  Submodule.subset_span (Finset.mem_coe.2 hχ)

theorem exists_pos_nat_cfInner_self {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    (hf0 : f ≠ 0) : ∃ n : ℕ, 0 < n ∧ cfInner f f = (n : ℂ) := by
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hf hf
  have hne : cfInner f f ≠ 0 := fun h => hf0 (cfInner_self_eq_zero.1 h)
  have hnn : (0 : ℂ) ≤ cfInner f f := cfInner_self_nonneg f
  rw [hm] at hne hnn
  have h0 : (0 : ℤ) ≤ m := by exact_mod_cast hnn
  have hmne : m ≠ 0 := by simpa using hne
  refine ⟨m.toNat, by omega, ?_⟩
  rw [hm]
  congr 1
  omega

section Main

variable (hc : IsSubcoherent S tau R) (hTS : T ⊆ S) (hTstar : ∀ ψ ∈ T, star ψ ∈ T)
  (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
  (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
  (hRmem : ∀ r ∈ R χ, r ∈ Submodule.span ℤ (Irr G))
  (hνmem : ∀ f : Submodule.span ℤ (T : Set (L → ℂ)),
    (ν f : G → ℂ) ∈ Submodule.span ℤ (Irr G))
  (hχ : χ ∈ T)

include hc hTS hTstar hν hτT hχ in
theorem sub_eq_sum_R :
    (ν ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ)
      - (ν ⟨star χ, mem_span_of_mem (hTstar χ hχ)⟩ : G → ℂ) = ∑ r ∈ R χ, r := by
  have hmem : χ - star χ ∈ charSpanZero (T : Set (L → ℂ)) := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (mem_span_of_mem hχ)
      (mem_span_of_mem (hTstar χ hχ)), ?_⟩
    have h := (hc.isCharacter χ (hTS hχ)).star_apply_one
    simp [h]
  set f : charSpanZero (T : Set (L → ℂ)) := ⟨χ - star χ, hmem⟩ with hf
  have hincl : Submodule.inclusion (charSpanZero_le _) f
      = (⟨χ, mem_span_of_mem hχ⟩ : Submodule.span ℤ (T : Set (L → ℂ)))
        - ⟨star χ, mem_span_of_mem (hTstar χ hχ)⟩ := Subtype.ext (by simp [hf])
  have key := hν.eq_on_zero f
  rw [hincl, map_sub] at key
  have hcoe : ((ν ⟨χ, mem_span_of_mem hχ⟩
      - ν ⟨star χ, mem_span_of_mem (hTstar χ hχ)⟩ : virtualChars G) : G → ℂ)
      = (ν ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ)
        - (ν ⟨star χ, mem_span_of_mem (hTstar χ hχ)⟩ : G → ℂ) := by simp
  rw [← hcoe, key, hτT f, hf]
  exact hc.tau_sub_star χ (hTS hχ)

include hc hTS hν hχ in
theorem coe_image_ne_zero : (ν ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ) ≠ 0 := by
  intro h
  have h1 : ν ⟨χ, mem_span_of_mem hχ⟩ = 0 := Subtype.ext (by simpa using h)
  have h2 : (⟨χ, mem_span_of_mem hχ⟩ : Submodule.span ℤ (T : Set (L → ℂ))) = 0 :=
    hν.injective (by rw [h1, map_zero])
  have h3 : χ = 0 := by simpa using Subtype.ext_iff.1 h2
  exact hc.ne_zero χ (hTS hχ) h3

include hc hTS hν hνmem hχ in
theorem exists_pos_nat_cfInner_self_of_mem :
    ∃ n : ℕ, 0 < n ∧ cfInner χ χ = (n : ℂ) := by
  obtain ⟨n, hn0, hn⟩ := exists_pos_nat_cfInner_self (hνmem ⟨χ, mem_span_of_mem hχ⟩)
    (coe_image_ne_zero hc hTS hν hχ)
  refine ⟨n, hn0, ?_⟩
  rw [← hn]
  exact (hν.inner_eq ⟨χ, mem_span_of_mem hχ⟩ ⟨χ, mem_span_of_mem hχ⟩).symm

include hc hTS in
theorem card_R_eq_two_mul {n : ℕ} (hn : cfInner χ χ = (n : ℂ)) (hχ : χ ∈ T) :
    (R χ).card = 2 * n := by
  have h := hc.card_R (hTS hχ)
  rw [charInner_eq_cfInner, hn] at h
  exact_mod_cast h

include hc hTS hTstar hν hτT hRmem hνmem hχ in
theorem exists_subset_card_eq_and_eq_sum {n : ℕ} (hn : cfInner χ χ = (n : ℂ)) :
    ∃ E ⊆ R χ, E.card = n ∧
      (ν ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ) = ∑ r ∈ E, r ∧
      (ν ⟨star χ, mem_span_of_mem (hTstar χ hχ)⟩ : G → ℂ) = -∑ r ∈ R χ \ E, r := by
  classical
  set f : G → ℂ := (ν ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ) with hfdef
  set g : G → ℂ := (ν ⟨star χ, mem_span_of_mem (hTstar χ hχ)⟩ : G → ℂ) with hgdef
  have hfmem : f ∈ Submodule.span ℤ (Irr G) := hνmem _
  have hnf : cfInner f f = (n : ℂ) := by
    rw [hfdef, hν.inner_eq ⟨χ, mem_span_of_mem hχ⟩ ⟨χ, mem_span_of_mem hχ⟩]; exact hn
  have hone : ∀ r ∈ R χ, cfInner r r = 1 := fun r hr => by
    rw [← charInner_eq_cfInner]; exact hc.charInner_R_self χ (hTS hχ) r hr
  have hzero : ∀ r ∈ R χ, ∀ s ∈ R χ, r ≠ s → cfInner r s = 0 := fun r hr s hs hne => by
    rw [← charInner_eq_cfInner]; exact hc.charInner_R_of_ne χ (hTS hχ) r hr s hs hne
  have hblock : f - g = ∑ r ∈ R χ, r := sub_eq_sum_R hc hTS hTstar hν hτT hχ
  have horth : cfInner f g = 0 := by
    rw [hfdef, hgdef, hν.inner_eq, ← charInner_eq_cfInner]
    exact hc.charInner_eq_zero χ (hTS hχ) _ (hTS (hTstar χ hχ))
      (Ne.symm (hc.star_ne χ (hTS hχ)))
  obtain ⟨a, ha⟩ := exists_int_cfInner_forall_mem (R := R χ) (fun r hr => hRmem r hr) hfmem
  have hsum : ((∑ r ∈ R χ, a r : ℤ) : ℂ) = cfInner f f := by
    rw [← sum_cfInner_eq_intCast ha, ← cfInner_sum_right, ← hblock, cfInner_sub_right, horth,
      sub_zero]
  obtain ⟨h01, hfP⟩ := eq_sum_cfInner_smul_of_cfInner_self_eq hone hzero ha hsum.symm
  obtain ⟨E, hER, hEcard, hEsum⟩ := exists_subset_sum_cfInner_smul_eq ha h01
  have hfE : f = ∑ r ∈ E, r := by rw [hfP, hEsum]
  have hEn : E.card = n := by
    have h1 : ((E.card : ℤ) : ℂ) = ((n : ℕ) : ℂ) := by rw [hEcard, hsum, hnf]
    have h2 : (E.card : ℂ) = (n : ℂ) := by push_cast at h1 ⊢; exact h1
    exact Nat.cast_injective h2
  refine ⟨E, hER, hEn, hfE, ?_⟩
  have hsplit : ∑ r ∈ R χ \ E, r + ∑ r ∈ E, r = ∑ r ∈ R χ, r := Finset.sum_sdiff hER
  have hg : g = f - ∑ r ∈ R χ, r := by rw [← hblock]; ring
  rw [hg, hfE, ← hsplit]
  ring

include hc hTS hTstar hν hτT hRmem hνmem hχ in
theorem exists_pos_nat_card_R_and_subset :
    ∃ n : ℕ, 0 < n ∧ cfInner χ χ = (n : ℂ) ∧ (R χ).card = 2 * n ∧
      ∃ E ⊆ R χ, E.card = n ∧
        (ν ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ) = ∑ r ∈ E, r ∧
        (ν ⟨star χ, mem_span_of_mem (hTstar χ hχ)⟩ : G → ℂ) = -∑ r ∈ R χ \ E, r := by
  obtain ⟨n, hn0, hn⟩ := exists_pos_nat_cfInner_self_of_mem hc hTS hν hνmem hχ
  exact ⟨n, hn0, hn, card_R_eq_two_mul hc hTS hn hχ,
    exists_subset_card_eq_and_eq_sum hc hTS hTstar hν hτT hRmem hνmem hχ hn⟩

end Main

end CoherentAntirealBlock

end CFSG.FeitThompson
