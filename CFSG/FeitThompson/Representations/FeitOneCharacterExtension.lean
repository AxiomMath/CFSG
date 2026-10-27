module

public import CFSG.FeitThompson.Representations.IntegralRemainderOneCharacterExtension
import CFSG.FeitThompson.Representations.StrictDegreeSumCorrectionVanish
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FeitExtension

open scoped ComplexOrder ComplexConjugate

variable {L : Type*} [Group L] {ι : Type*} {γ : ι → (L → ℂ)} {χ : L → ℂ}

omit [Group L] in
theorem exists_sub_intCast_smul_mem_span {S : Set (L → ℂ)} {f : L → ℂ}
    (hf : f ∈ Submodule.span ℤ (insert χ S)) :
    ∃ n : ℤ, f - (n : ℂ) • χ ∈ Submodule.span ℤ S := by
  obtain ⟨a, z, hz, hfa⟩ := Submodule.mem_span_insert.1 hf
  refine ⟨a, ?_⟩
  rw [hfa, Int.cast_smul_eq_zsmul]
  simpa using hz

noncomputable def chiCoeff (f : Submodule.span ℤ (insert χ (Set.range γ))) : ℤ :=
  (exists_sub_intCast_smul_mem_span f.2).choose

omit [Group L] in
theorem sub_chiCoeff_smul_mem (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    (f : L → ℂ) - (chiCoeff f : ℂ) • χ ∈ Submodule.span ℤ (Set.range γ) :=
  (exists_sub_intCast_smul_mem_span f.2).choose_spec

noncomputable def zeroPart (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    Submodule.span ℤ (Set.range γ) :=
  ⟨(f : L → ℂ) - (chiCoeff f : ℂ) • χ, sub_chiCoeff_smul_mem f⟩

omit [Group L] in
@[simp] theorem coe_zeroPart (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    (zeroPart f : L → ℂ) = (f : L → ℂ) - (chiCoeff f : ℂ) • χ := (rfl)

omit [Group L] in
theorem coe_eq_zeroPart_add (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    (f : L → ℂ) = (zeroPart f : L → ℂ) + (chiCoeff f : ℂ) • χ := by
  rw [coe_zeroPart]; abel

@[simp] theorem coe_inclusion_charSpanZero (f : charSpanZero (insert χ (Set.range γ))) :
    ((Submodule.inclusion (charSpanZero_le (insert χ (Set.range γ))) f :
      Submodule.span ℤ (insert χ (Set.range γ))) : L → ℂ) = (f : L → ℂ) := (rfl)

namespace OneCharExtension

variable {G : Type*} [Group G] [Fintype G] [Fintype L] [Fintype ι] {d : ℤ} {k₀ : ι}
  (E : OneCharExtension G γ χ d k₀)

include E in
theorem cfInner_eq_zero_chi_of_mem_span_range {g : L → ℂ}
    (hg : g ∈ Submodule.span ℤ (Set.range γ)) : cfInner g χ = 0 := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact cfInner_eq_zero_of_mem_Irr (E.mem_Irr k) E.chi_mem_Irr fun h => E.chi_notMem ⟨k, h⟩
  | zero => exact cfInner_zero_left _
  | add x y _ _ hx hy => rw [cfInner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [← Int.cast_smul_eq_zsmul ℂ, cfInner_smul_left, hx, mul_zero]

include E in
theorem cfInner_chi_eq_zero_of_mem_span_range {g : L → ℂ}
    (hg : g ∈ Submodule.span ℤ (Set.range γ)) : cfInner χ g = 0 := by
  rw [← conj_cfInner, E.cfInner_eq_zero_chi_of_mem_span_range hg, map_zero]

include E in
theorem intCast_eq_cfInner_chi {f : L → ℂ} {n : ℤ}
    (h : f - (n : ℂ) • χ ∈ Submodule.span ℤ (Set.range γ)) : (n : ℂ) = cfInner f χ := by
  have h0 := E.cfInner_eq_zero_chi_of_mem_span_range h
  rw [cfInner_sub_left, cfInner_smul_left, cfInner_self_of_mem_Irr E.chi_mem_Irr] at h0
  linear_combination -h0

include E in
theorem chiCoeff_eq_cfInner (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    (chiCoeff f : ℂ) = cfInner (f : L → ℂ) χ :=
  E.intCast_eq_cfInner_chi (sub_chiCoeff_smul_mem f)

include E in
theorem chiCoeff_add (f g : Submodule.span ℤ (insert χ (Set.range γ))) :
    chiCoeff (f + g) = chiCoeff f + chiCoeff g := by
  have h : ((chiCoeff (f + g) : ℤ) : ℂ) = ((chiCoeff f + chiCoeff g : ℤ) : ℂ) := by
    push_cast
    rw [E.chiCoeff_eq_cfInner, E.chiCoeff_eq_cfInner, E.chiCoeff_eq_cfInner,
      show ((f + g : Submodule.span ℤ (insert χ (Set.range γ))) : L → ℂ)
        = (f : L → ℂ) + (g : L → ℂ) from rfl, cfInner_add_left]
  exact_mod_cast h

include E in
theorem zeroPart_add (f g : Submodule.span ℤ (insert χ (Set.range γ))) :
    zeroPart (f + g) = zeroPart f + zeroPart g := by
  apply Subtype.ext
  simp only [coe_zeroPart, Submodule.coe_add, E.chiCoeff_add, Int.cast_add, add_smul]
  abel

include E in
theorem chiCoeff_inclusion (h : Submodule.span ℤ (Set.range γ)) :
    chiCoeff (Submodule.inclusion
      (Submodule.span_mono (Set.subset_insert χ (Set.range γ))) h) = 0 := by
  have hz : ((chiCoeff (Submodule.inclusion
      (Submodule.span_mono (Set.subset_insert χ (Set.range γ))) h) : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
    rw [E.chiCoeff_eq_cfInner]
    exact_mod_cast E.cfInner_eq_zero_chi_of_mem_span_range h.2
  exact_mod_cast hz

include E in
theorem zeroPart_inclusion (h : Submodule.span ℤ (Set.range γ)) :
    zeroPart (Submodule.inclusion
      (Submodule.span_mono (Set.subset_insert χ (Set.range γ))) h) = h := by
  apply Subtype.ext
  rw [coe_zeroPart, E.chiCoeff_inclusion]
  simp

noncomputable def alphaMem : Submodule.span ℤ (Irr G) :=
  E.tau ⟨χ - (d : ℂ) • γ k₀, E.sub_smul_mem_charSpanZero⟩

theorem coe_alphaMem : (E.alphaMem : G → ℂ) = E.alpha := E.alpha_apply.symm

noncomputable def nuPsi : Submodule.span ℤ (Irr G) :=
  E.nu ⟨γ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩

theorem coe_nuPsi : (E.nuPsi : G → ℂ) = E.nuImage k₀ := (E.nuImage_apply k₀).symm

include E in
theorem exists_int_coeffs_nu (h : Submodule.span ℤ (Set.range γ)) :
    ∃ c : ι → ℤ, (h : L → ℂ) = ∑ k, (c k : ℂ) • γ k ∧
      (E.nu h : G → ℂ) = ∑ k, (c k : ℂ) • E.nuImage k := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun (R := ℤ) |>.1 h.2
  refine ⟨c, ?_, ?_⟩
  · rw [← hc]
    exact Finset.sum_congr rfl fun k _ => (Int.cast_smul_eq_zsmul ℂ (c k) (γ k)).symm
  · have hh : h = ∑ k, c k • (⟨γ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        Submodule.span ℤ (Set.range γ)) := by
      apply Subtype.ext
      push_cast
      rw [← hc]
    rw [hh, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    push_cast
    rw [nuImage_apply, Int.cast_smul_eq_zsmul]

include E in
theorem add_zsmul_mem_charSpanZero (f : charSpanZero (insert χ (Set.range γ))) :
    (zeroPart (Submodule.inclusion (charSpanZero_le _) f) : L → ℂ)
        + (chiCoeff (Submodule.inclusion (charSpanZero_le _) f) * d) • γ k₀
      ∈ charSpanZero (Set.range γ) := by
  refine mem_charSpanZero.2 ⟨Submodule.add_mem _ (zeroPart _).2
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k₀, rfl⟩)), ?_⟩
  have hf1 : (f : L → ℂ) 1 = 0 := charSpanZero_apply_one f
  rw [← Int.cast_smul_eq_zsmul ℂ]
  simp only [coe_zeroPart, coe_inclusion_charSpanZero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [hf1, E.chi_apply_one]
  push_cast
  ring

noncomputable def tauZeroPart (f : charSpanZero (insert χ (Set.range γ))) :
    charSpanZero (Set.range γ) :=
  ⟨_, E.add_zsmul_mem_charSpanZero f⟩

theorem coe_tauZeroPart (f : charSpanZero (insert χ (Set.range γ))) :
    (E.tauZeroPart f : L → ℂ)
      = (zeroPart (Submodule.inclusion (charSpanZero_le _) f) : L → ℂ)
        + (chiCoeff (Submodule.inclusion (charSpanZero_le _) f) * d) • γ k₀ := (rfl)

theorem eq_inclusion_tauZeroPart_add (f : charSpanZero (insert χ (Set.range γ))) :
    f = Submodule.inclusion (charSpanZero_mono (Set.subset_insert χ (Set.range γ)))
          (E.tauZeroPart f)
        + chiCoeff (Submodule.inclusion (charSpanZero_le _) f)
          • (⟨χ - (d : ℂ) • γ k₀, E.sub_smul_mem_charSpanZero⟩ :
              charSpanZero (insert χ (Set.range γ))) := by
  apply Subtype.ext
  rw [Submodule.coe_add, SetLike.val_smul]
  change (f : L → ℂ) = (E.tauZeroPart f : L → ℂ)
    + chiCoeff (Submodule.inclusion (charSpanZero_le _) f) • (χ - (d : ℂ) • γ k₀)
  rw [coe_tauZeroPart, coe_zeroPart, coe_inclusion_charSpanZero, ← Int.cast_smul_eq_zsmul ℂ,
    ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  module

theorem inclusion_tauZeroPart (f : charSpanZero (insert χ (Set.range γ))) :
    Submodule.inclusion (charSpanZero_le (Set.range γ)) (E.tauZeroPart f)
      = zeroPart (Submodule.inclusion (charSpanZero_le _) f)
        + (chiCoeff (Submodule.inclusion (charSpanZero_le _) f) * d)
          • (⟨γ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩ : Submodule.span ℤ (Set.range γ)) := by
  apply Subtype.ext
  rw [Submodule.coe_add, SetLike.val_smul]
  exact E.coe_tauZeroPart f

theorem tau_eq (f : charSpanZero (insert χ (Set.range γ))) :
    E.tau f = E.nu (zeroPart (Submodule.inclusion (charSpanZero_le _) f))
      + (chiCoeff (Submodule.inclusion (charSpanZero_le _) f) * d) • E.nuPsi
      + chiCoeff (Submodule.inclusion (charSpanZero_le _) f) • E.alphaMem := by
  conv_lhs => rw [E.eq_inclusion_tauZeroPart_add f]
  rw [map_add, map_zsmul, ← E.nu_eq_tau (E.tauZeroPart f), E.inclusion_tauZeroPart f,
    map_add, map_zsmul]
  rfl

noncomputable def tauVirt : charSpanZero (insert χ (Set.range γ)) →+ virtualChars G :=
  (Submodule.inclusion span_Irr_le_virtualChars).toAddMonoidHom.comp E.tau

theorem coe_tauVirt (f : charSpanZero (insert χ (Set.range γ))) :
    ((E.tauVirt f : virtualChars G) : G → ℂ) = (E.tau f : G → ℂ) := (rfl)

variable [DecidableEq ι]

include E in
theorem cfInner_remainder_nu (h : Submodule.span ℤ (Set.range γ)) :
    cfInner E.remainder (E.nu h : G → ℂ) = 0 := by
  obtain ⟨c, -, hc⟩ := E.exists_int_coeffs_nu h
  rw [hc, cfInner_right_sum_smul]
  exact Finset.sum_eq_zero fun k _ => by rw [E.cfInner_remainder_nuImage, mul_zero]

include E in
theorem cfInner_nu_remainder (h : Submodule.span ℤ (Set.range γ)) :
    cfInner (E.nu h : G → ℂ) E.remainder = 0 := by
  rw [← conj_cfInner, E.cfInner_remainder_nu, map_zero]

noncomputable def remainderMem : Submodule.span ℤ (Irr G) :=
  ⟨E.remainder, E.remainder_mem_span_Irr⟩

@[simp] theorem coe_remainderMem : (E.remainderMem : G → ℂ) = E.remainder := (rfl)

theorem remainderMem_eq (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) :
    E.remainderMem = E.alphaMem + d • E.nuPsi := by
  apply Subtype.ext
  rw [Submodule.coe_add, SetLike.val_smul, coe_remainderMem, coe_alphaMem, coe_nuPsi,
    ← Int.cast_smul_eq_zsmul ℂ]
  exact E.remainder_eq_of_lt_degreeSqSum hW

noncomputable def nuPlus :
    Submodule.span ℤ (insert χ (Set.range γ)) →+ Submodule.span ℤ (Irr G) :=
  AddMonoidHom.mk' (fun f => E.nu (zeroPart f) + chiCoeff f • E.remainderMem) fun f g => by
    rw [E.zeroPart_add, E.chiCoeff_add, map_add, add_smul]
    abel

theorem nuPlus_apply (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    E.nuPlus f = E.nu (zeroPart f) + chiCoeff f • E.remainderMem := (rfl)

theorem coe_nuPlus (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    (E.nuPlus f : G → ℂ)
      = (E.nu (zeroPart f) : G → ℂ) + (chiCoeff f : ℂ) • E.remainder := by
  rw [nuPlus_apply, Submodule.coe_add, SetLike.val_smul, coe_remainderMem,
    Int.cast_smul_eq_zsmul]

theorem nuPlus_inclusion (h : Submodule.span ℤ (Set.range γ)) :
    E.nuPlus (Submodule.inclusion
      (Submodule.span_mono (Set.subset_insert χ (Set.range γ))) h) = E.nu h := by
  rw [nuPlus_apply, E.chiCoeff_inclusion, E.zeroPart_inclusion, zero_smul, add_zero]

theorem nuPlus_chi :
    E.nuPlus ⟨χ, Submodule.subset_span (Set.mem_insert _ _)⟩ = E.remainderMem := by
  have hn : chiCoeff (⟨χ, Submodule.subset_span (Set.mem_insert χ (Set.range γ))⟩ :
      Submodule.span ℤ (insert χ (Set.range γ))) = 1 := by
    have h : ((chiCoeff (⟨χ, Submodule.subset_span (Set.mem_insert χ (Set.range γ))⟩ :
        Submodule.span ℤ (insert χ (Set.range γ))) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
      rw [E.chiCoeff_eq_cfInner]
      exact_mod_cast cfInner_self_of_mem_Irr E.chi_mem_Irr
    exact_mod_cast h
  have hz : zeroPart (⟨χ, Submodule.subset_span (Set.mem_insert χ (Set.range γ))⟩ :
      Submodule.span ℤ (insert χ (Set.range γ))) = 0 := by
    apply Subtype.ext
    rw [coe_zeroPart, hn]
    simp
  rw [nuPlus_apply, hn, hz, map_zero, one_smul, zero_add]

theorem nuPlus_isometry (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ)
    (f g : Submodule.span ℤ (insert χ (Set.range γ))) :
    cfInner (E.nuPlus f : G → ℂ) (E.nuPlus g : G → ℂ)
      = cfInner (f : L → ℂ) (g : L → ℂ) := by
  have hΔ : cfInner E.remainder E.remainder = 1 := E.cfInner_self_remainder_of_lt_degreeSqSum hW
  rw [coe_nuPlus, coe_nuPlus, cfInner_add_left, cfInner_add_right, cfInner_add_right,
    cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, cfInner_smul_left,
    E.cfInner_remainder_nu, E.cfInner_nu_remainder, hΔ, E.nu_isometry]
  rw [coe_eq_zeroPart_add f, coe_eq_zeroPart_add g, cfInner_add_left, cfInner_add_right,
    cfInner_add_right, cfInner_smul_left, cfInner_smul_right, cfInner_smul_right,
    cfInner_smul_left, E.cfInner_eq_zero_chi_of_mem_span_range (zeroPart f).2,
    E.cfInner_chi_eq_zero_of_mem_span_range (zeroPart g).2,
    cfInner_self_of_mem_Irr E.chi_mem_Irr]

theorem nuPlus_eq_tau (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ)
    (f : charSpanZero (insert χ (Set.range γ))) :
    E.nuPlus (Submodule.inclusion (charSpanZero_le _) f) = E.tau f := by
  rw [nuPlus_apply, E.tau_eq f, E.remainderMem_eq hW, smul_add, smul_smul, mul_comm]
  abel

theorem exists_addMonoidHom_isometry_extension (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) :
    ∃ νp : Submodule.span ℤ (insert χ (Set.range γ)) →+ Submodule.span ℤ (Irr G),
      (∀ f g, cfInner (νp f : G → ℂ) (νp g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ)) ∧
      (∀ f : charSpanZero (insert χ (Set.range γ)),
        νp (Submodule.inclusion (charSpanZero_le _) f) = E.tau f) ∧
      (∀ h : Submodule.span ℤ (Set.range γ),
        νp (Submodule.inclusion
          (Submodule.span_mono (Set.subset_insert χ (Set.range γ))) h) = E.nu h) :=
  ⟨E.nuPlus, E.nuPlus_isometry hW, E.nuPlus_eq_tau hW, E.nuPlus_inclusion⟩

noncomputable def nuPlusVirt :
    Submodule.span ℤ (insert χ (Set.range γ)) →+ virtualChars G :=
  (Submodule.inclusion span_Irr_le_virtualChars).toAddMonoidHom.comp E.nuPlus

theorem coe_nuPlusVirt (f : Submodule.span ℤ (insert χ (Set.range γ))) :
    ((E.nuPlusVirt f : virtualChars G) : G → ℂ) = (E.nuPlus f : G → ℂ) := (rfl)

theorem isCoherentWith_nuPlusVirt (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) :
    IsCoherentWith (insert χ (Set.range γ)) E.tauVirt E.nuPlusVirt where
  inner_eq f g := by rw [coe_nuPlusVirt, coe_nuPlusVirt]; exact E.nuPlus_isometry hW f g
  eq_on_zero f := by
    apply Subtype.ext
    rw [coe_nuPlusVirt, coe_tauVirt]
    exact congrArg (fun z : Submodule.span ℤ (Irr G) => (z : G → ℂ)) (E.nuPlus_eq_tau hW f)

theorem isCoherent_tauVirt_of_lt_degreeSqSum (hW : 2 * γ k₀ 1 * χ 1 < degreeSqSum γ) :
    IsCoherent (insert χ (Set.range γ)) E.tauVirt :=
  (E.isCoherentWith_nuPlusVirt hW).isCoherent

end OneCharExtension

end FeitExtension

end CFSG.FeitThompson
