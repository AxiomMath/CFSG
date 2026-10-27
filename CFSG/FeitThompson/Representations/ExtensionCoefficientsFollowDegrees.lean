module

public import CFSG.FeitThompson.Representations.IntegralRemainderOneCharacterExtension
public import CFSG.FeitThompson.Representations.CoherentFamilyCommonSignDegreeRatio
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FeitExtension

namespace OneCharExtension

variable {G : Type*} [Group G] [Fintype G] {L : Type*} [Group L] [Fintype L]
  {ι : Type*} [Fintype ι] {γ : ι → (L → ℂ)} {χ : L → ℂ} {d : ℤ} {k₀ : ι}
  (E : OneCharExtension G γ χ d k₀)

noncomputable def nuHom : Submodule.span ℤ (Set.range γ) →+ virtualChars G :=
  (Submodule.inclusion span_Irr_le_virtualChars).toAddMonoidHom.comp E.nu

noncomputable def tauHom : charSpanZero (Set.range γ) →+ virtualChars G :=
  ((Submodule.inclusion span_Irr_le_virtualChars).toAddMonoidHom.comp E.tau).comp
    (Submodule.inclusion (charSpanZero_mono (Set.subset_insert χ (Set.range γ)))).toAddMonoidHom

theorem coe_nuHom (f : Submodule.span ℤ (Set.range γ)) :
    ((E.nuHom f : virtualChars G) : G → ℂ) = (E.nu f : G → ℂ) := (rfl)

theorem coe_tauHom (f : charSpanZero (Set.range γ)) :
    ((E.tauHom f : virtualChars G) : G → ℂ)
      = (E.tau (Submodule.inclusion
          (charSpanZero_mono (Set.subset_insert χ (Set.range γ))) f) : G → ℂ) := (rfl)

theorem isCoherentWith_nuHom : IsCoherentWith (Set.range γ) E.tauHom E.nuHom where
  inner_eq f h := by rw [coe_nuHom, coe_nuHom]; exact E.nu_isometry f h
  eq_on_zero f := by
    apply Subtype.ext
    rw [coe_nuHom, coe_tauHom]
    exact congrArg (fun z : Submodule.span ℤ (Irr G) => (z : G → ℂ)) (E.nu_eq_tau f)

theorem tauHom_apply_one (f : charSpanZero (Set.range γ)) : (E.tauHom f : G → ℂ) 1 = 0 := by
  rw [coe_tauHom]; exact E.tau_apply_one _

include E in
theorem two_le_ncard_range : 2 ≤ (Set.range γ).ncard := by
  rw [Set.ncard_range_of_injective E.injective, Nat.card_eq_fintype_card]
  exact E.two_le_card

theorem nuImage_eq_coherentVal (j : ι) :
    E.nuImage j = coherentVal E.nuHom ⟨γ j, ⟨j, rfl⟩⟩ := by
  rw [nuImage_apply, coherentVal_apply, coe_nuHom]

include E in
theorem exists_degree (j : ι) : ∃ n : ℕ, 0 < n ∧ γ j 1 = (n : ℂ) := by
  obtain ⟨n, hn, hn1, -⟩ := Irr.exists_degree (E.mem_Irr j)
  exact ⟨n, hn, hn1⟩

include E in
theorem exists_degree_ratio :
    ∃ k : ℝ, k ≠ 0 ∧ ∀ j, E.nuImage j 1 = (k : ℂ) * γ j 1 := by
  obtain ⟨ε, hε, c, hc, η, -, -, hcoh, hdeg⟩ :=
    exists_sign_and_degree_ratio_of_isCoherentWith (S := Set.range γ)
      (fun _ hf => by obtain ⟨j, rfl⟩ := hf; exact E.mem_Irr j) E.two_le_ncard_range
      E.tauHom_apply_one E.isCoherentWith_nuHom
  obtain ⟨s, hs0, hsε⟩ : ∃ s : ℝ, s ≠ 0 ∧ (s : ℂ) = ε := by
    rcases hε with h | h
    · exact ⟨1, one_ne_zero, by simp [h]⟩
    · exact ⟨-1, by norm_num, by simp [h]⟩
  refine ⟨s * c, mul_ne_zero hs0 hc.ne', fun j => ?_⟩
  have h1 := hcoh ⟨γ j, ⟨j, rfl⟩⟩
  have h2 := hdeg ⟨γ j, ⟨j, rfl⟩⟩
  rw [nuImage_eq_coherentVal, h1]
  simp only [Pi.smul_apply, smul_eq_mul] at *
  rw [h2, ← hsε]
  push_cast
  ring

variable [DecidableEq ι]

theorem apply_one_mul_bCoeff (j : ι) :
    γ k₀ 1 * E.bCoeff j = γ j 1 * E.bCoeff k₀ := by
  obtain ⟨a, ha0, ha⟩ := E.exists_degree j
  obtain ⟨b, hb0, hb⟩ := E.exists_degree k₀
  have hmem : ((b : ℤ) • γ j - (a : ℤ) • γ k₀) ∈ charSpanZero (Set.range γ) := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k₀, rfl⟩)), ?_⟩
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, ha, hb, zsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  set f : charSpanZero (Set.range γ) := ⟨_, hmem⟩ with hf
  have hincl : Submodule.inclusion (charSpanZero_le (Set.range γ)) f
      = (b : ℤ) • (⟨γ j, Submodule.subset_span ⟨j, rfl⟩⟩ : Submodule.span ℤ (Set.range γ))
        - (a : ℤ) • ⟨γ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩ := Subtype.ext (by simp [hf])
  have hnu : (E.nu (Submodule.inclusion (charSpanZero_le (Set.range γ)) f) : G → ℂ)
      = (b : ℂ) • E.nuImage j - (a : ℂ) • E.nuImage k₀ := by
    rw [hincl, map_sub, map_zsmul, map_zsmul, Submodule.coe_sub]
    simp only [SetLike.val_smul, nuImage_apply, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  have hkey : cfInner E.alpha
        ((E.nu (Submodule.inclusion (charSpanZero_le (Set.range γ)) f) : G → ℂ))
      = cfInner (χ - (d : ℂ) • γ k₀) ((b : ℂ) • γ j - (a : ℂ) • γ k₀) := by
    rw [alpha_apply, E.nu_eq_tau f, E.tau_isometry]
    change cfInner (χ - (d : ℂ) • γ k₀) ((b : ℤ) • γ j - (a : ℤ) • γ k₀) = _
    simp only [← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  rw [hnu] at hkey
  have hne : ∀ j, χ ≠ γ j := fun j h => E.chi_notMem ⟨j, h.symm⟩
  rw [cfInner_sub_right, cfInner_smul_right, cfInner_smul_right, cfInner_sub_left,
    cfInner_sub_right, cfInner_sub_right, cfInner_smul_left, cfInner_smul_left,
    cfInner_smul_right, cfInner_smul_right, cfInner_smul_right, cfInner_smul_right,
    cfInner_eq_zero_of_mem_Irr E.chi_mem_Irr (E.mem_Irr j) (hne j),
    cfInner_eq_zero_of_mem_Irr E.chi_mem_Irr (E.mem_Irr k₀) (hne k₀),
    cfInner_eq_ite_of_mem_Irr (E.mem_Irr k₀) (E.mem_Irr j),
    cfInner_self_of_mem_Irr (E.mem_Irr k₀)] at hkey
  have hδ : (if γ k₀ = γ j then (1 : ℂ) else 0) = (if j = k₀ then 1 else 0) := by
    by_cases h : j = k₀
    · subst h; simp
    · rw [if_neg h, if_neg (fun he => h (E.injective he).symm)]
  rw [hδ] at hkey
  simp only [map_natCast] at hkey
  rw [ha, hb, E.bCoeff_apply j, E.bCoeff_apply k₀, if_pos rfl]
  linear_combination hkey

theorem exists_rat_bCoeff_ratio :
    ∃ t : ℚ, ∀ j, E.bCoeff j = (t : ℂ) * γ j 1 := by
  obtain ⟨b, hb0, hb⟩ := E.exists_degree k₀
  obtain ⟨m, hm⟩ := E.exists_int_bCoeff k₀
  have hbne : ((b : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hb0.ne'
  refine ⟨(m : ℚ) / (b : ℚ), fun j => ?_⟩
  have h := E.apply_one_mul_bCoeff j
  rw [hb, hm] at h
  have hcast : (((m : ℚ) / (b : ℚ) : ℚ) : ℂ) = (m : ℂ) / (b : ℂ) := by push_cast; ring
  rw [hcast]
  field_simp
  linear_combination h

theorem remainder_apply_one_of_ratios {k t : ℂ} (hk : ∀ j, E.nuImage j 1 = k * γ j 1)
    (ht : ∀ j, E.bCoeff j = t * γ j 1) :
    E.remainder 1 = k * ((d : ℂ) * γ k₀ 1 - t * degreeSqSum γ) := by
  have hterm : ∀ x : ι, t * γ x 1 * (k * γ x 1) = k * (t * γ x 1 ^ 2) := fun x => by ring
  rw [remainder_apply]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    E.alpha_apply_one, hk, ht, degreeSqSum_eq, Finset.mul_sum, zero_add]
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem exists_degree_ratio_and_bCoeff_ratio :
    ∃ k : ℝ, k ≠ 0 ∧ ∃ t : ℚ,
      (∀ j, E.nuImage j 1 = (k : ℂ) * γ j 1) ∧
      (∀ j, E.bCoeff j = (t : ℂ) * γ j 1) ∧
      E.remainder 1 = (k : ℂ) * ((d : ℂ) * γ k₀ 1 - (t : ℂ) * degreeSqSum γ) := by
  obtain ⟨k, hk0, hk⟩ := E.exists_degree_ratio
  obtain ⟨t, ht⟩ := E.exists_rat_bCoeff_ratio
  exact ⟨k, hk0, t, hk, ht, E.remainder_apply_one_of_ratios hk ht⟩

end OneCharExtension

end FeitExtension

end CFSG.FeitThompson
