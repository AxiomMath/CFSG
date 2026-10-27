module

import CFSG.FeitThompson.Representations.DisjointCoherentWeightedFamiliesOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeFamilyCoherence
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
public import CFSG.FeitThompson.Representations.CoherentImageAntirealBlockSelection
import CFSG.FeitThompson.Representations.IntegralOrthonormalBlockProjection
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars
import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence
import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace WeightedFeitExtension

open DisjointCoherentBlocks
open CoherentAntirealBlock
open IntegralBlockProjection
open ComplexConjugate
open scoped ComplexOrder

section Inner

variable {X : Type*} [Fintype X]

theorem cfInner_zsmul_right (k : ℤ) (f h : X → ℂ) :
    cfInner f (k • h) = (k : ℂ) * cfInner f h := by
  rw [← Int.cast_smul_eq_zsmul ℂ, cfInner_smul_right, map_intCast]

theorem exists_nonneg_real_cfInner_self (f : X → ℂ) :
    ∃ t : ℝ, 0 ≤ t ∧ cfInner f f = (t : ℂ) := by
  have h := cfInner_self_nonneg f
  exact ⟨(cfInner f f).re, (Complex.le_def.1 h).1, Complex.eq_re_of_ofReal_le h⟩

theorem cfInner_sum_sum_of_orthonormal {Rs : Finset (X → ℂ)}
    (hone : ∀ r ∈ Rs, cfInner r r = 1)
    (hzero : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → cfInner r s = 0)
    {E F : Finset (X → ℂ)} (hE : E ⊆ Rs) (hF : F ⊆ Rs) :
    cfInner (∑ r ∈ E, r) (∑ r ∈ F, r) = ((E ∩ F).card : ℂ) := by
  classical
  rw [cfInner_sum_left]
  have key : ∀ r ∈ E, cfInner r (∑ s ∈ F, s) = if r ∈ F then 1 else 0 := by
    intro r hr
    rw [cfInner_sum_right]
    by_cases h : r ∈ F
    · rw [Finset.sum_eq_single_of_mem r h fun s hs hsr => hzero r (hE hr) s (hF hs) (Ne.symm hsr),
        hone r (hE hr), if_pos h]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun s hs => hzero r (hE hr) s (hF hs) fun he => h (he ▸ hs)
  rw [Finset.sum_congr rfl key, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem cfInner_self_eq_sum_div_add {ι : Type*} {Tt : Finset ι} (v : ι → X → ℂ)
    (horth : ∀ i ∈ Tt, ∀ j ∈ Tt, i ≠ j → cfInner (v i) (v j) = 0) (f : X → ℂ) :
    cfInner f f
      = ∑ i ∈ Tt, cfInner f (v i) * conj (cfInner f (v i)) / cfInner (v i) (v i)
        + cfInner (f - ∑ i ∈ Tt, (cfInner f (v i) / cfInner (v i) (v i)) • v i)
            (f - ∑ i ∈ Tt, (cfInner f (v i) / cfInner (v i) (v i)) • v i) := by
  set N : ι → ℂ := fun i => cfInner (v i) (v i) with hN
  set P : X → ℂ := ∑ i ∈ Tt, (cfInner f (v i) / N i) • v i with hP
  set B : ℂ := ∑ i ∈ Tt, cfInner f (v i) * conj (cfInner f (v i)) / N i with hB
  have hNconj : ∀ i, conj (N i) = N i := fun i => conj_cfInner _ _
  have hfP : cfInner f P = B := by
    rw [hP, cfInner_sum_right, hB]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cfInner_smul_right]
    simp only [map_div₀, hNconj]
    rw [div_mul_eq_mul_div, mul_comm]
  have hPf : cfInner P f = B := by
    rw [← conj_cfInner, hfP, hB, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_div₀, hNconj, map_mul, Complex.conj_conj]
    ring
  have hPP : cfInner P P = B := by
    rw [hP, cfInner_sum_left, hB]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [cfInner_smul_left, cfInner_sum_right,
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
        rw [cfInner_smul_right, horth i hi j hj (Ne.symm hji), mul_zero]),
      cfInner_smul_right]
    simp only [map_div₀, hNconj]
    by_cases h : N i = 0
    · simp [h]
    · field_simp
      ring
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hfP, hPf, hPP]
  ring

end Inner

theorem eq_zero_of_sq_mul_add_le {l : ℤ} {c z D : ℂ} (hz : 0 ≤ z) (hD : 0 < D)
    (hcD : 2 * D < c) (hle : (l : ℂ) ^ 2 * c + z ≤ 2 * D * (l : ℂ)) : l = 0 ∧ z = 0 := by
  have hDpos : (0 : ℂ) < 2 * D := by positivity
  have hcpos : (0 : ℂ) < c := hDpos.trans hcD
  have hl : l = 0 := by
    rcases lt_trichotomy l 0 with hneg | hzero | hpos
    · exfalso
      have h1 : (l : ℂ) < 0 := by exact_mod_cast hneg
      have h2 : 2 * D * (l : ℂ) < 0 := mul_neg_of_pos_of_neg hDpos h1
      have h3 : (0 : ℂ) ≤ (l : ℂ) ^ 2 * c := by
        have hsq : (0 : ℂ) ≤ (l : ℂ) ^ 2 := by
          have : (0 : ℤ) ≤ l ^ 2 := sq_nonneg l
          exact_mod_cast this
        exact mul_nonneg hsq hcpos.le
      exact absurd (lt_of_le_of_lt (le_trans (add_nonneg h3 hz) hle) h2) (lt_irrefl 0)
    · exact hzero
    · exfalso
      have hl1 : (1 : ℂ) ≤ (l : ℂ) := by exact_mod_cast hpos
      have hlpos : (0 : ℂ) < (l : ℂ) := lt_of_lt_of_le zero_lt_one hl1
      have hsq : (l : ℂ) ≤ (l : ℂ) ^ 2 := by
        have : l ≤ l ^ 2 := by nlinarith
        exact_mod_cast this
      have h3 : 2 * D * (l : ℂ) < (l : ℂ) ^ 2 * c := by
        calc 2 * D * (l : ℂ) = (l : ℂ) * (2 * D) := by ring
        _ < (l : ℂ) * c := mul_lt_mul_of_pos_left hcD hlpos
        _ ≤ (l : ℂ) ^ 2 * c := mul_le_mul_of_nonneg_right hsq hcpos.le
      exact absurd (lt_of_lt_of_le h3 (le_trans (le_add_of_nonneg_right hz) hle)) (lt_irrefl _)
  refine ⟨hl, le_antisymm ?_ hz⟩
  rw [hl] at hle
  simpa using hle

section Free

variable {La : Type*} [Fintype La]

theorem linearIndependent_of_cfInner {U : Set (La → ℂ)}
    (h0 : ∀ f ∈ U, cfInner f f ≠ 0)
    (horth : ∀ f ∈ U, ∀ g ∈ U, f ≠ g → cfInner f g = 0) :
    LinearIndependent ℤ (fun f : U => (f : La → ℂ)) := by
  classical
  rw [linearIndependent_iff']
  intro t g hg j hj
  have key := congrArg (fun f => cfInner f ((j : La → ℂ))) hg
  simp only [cfInner_sum_left, cfInner_zsmul_left, cfInner_zero_left] at key
  have hij : ∀ i ∈ t, (g i : ℂ) * cfInner ((i : La → ℂ)) ((j : La → ℂ))
      = if i = j then (g i : ℂ) * cfInner ((j : La → ℂ)) ((j : La → ℂ)) else 0 := by
    intro i _
    by_cases h : i = j
    · simp [h]
    · rw [horth _ i.2 _ j.2 fun he => h (Subtype.ext he), mul_zero, if_neg h]
  rw [Finset.sum_congr rfl hij, Finset.sum_ite_eq' t j, if_pos hj] at key
  have hjj := h0 _ j.2
  have hg0 : (g j : ℂ) = 0 := (mul_eq_zero.1 key).resolve_right hjj
  exact_mod_cast hg0

noncomputable def orthSpanBasis {U : Set (La → ℂ)}
    (h0 : ∀ f ∈ U, cfInner f f ≠ 0)
    (horth : ∀ f ∈ U, ∀ g ∈ U, f ≠ g → cfInner f g = 0) :
    Module.Basis U ℤ (Submodule.span ℤ U) :=
  (Module.Basis.span (linearIndependent_of_cfInner h0 horth)).map
    (LinearEquiv.ofEq _ _ (by rw [Subtype.range_coe]))

@[simp] theorem orthSpanBasis_apply {U : Set (La → ℂ)}
    (h0 : ∀ f ∈ U, cfInner f f ≠ 0)
    (horth : ∀ f ∈ U, ∀ g ∈ U, f ≠ g → cfInner f g = 0) (f : U) :
    (orthSpanBasis h0 horth f : La → ℂ) = (f : La → ℂ) := by
  simp [orthSpanBasis, Module.Basis.span_apply]

theorem orthSpanBasis_eq {U : Set (La → ℂ)} (h0 : ∀ f ∈ U, cfInner f f ≠ 0)
    (horth : ∀ f ∈ U, ∀ g ∈ U, f ≠ g → cfInner f g = 0) (f : U) :
    orthSpanBasis h0 horth f = ⟨(f : La → ℂ), Submodule.subset_span f.2⟩ :=
  Subtype.ext (orthSpanBasis_apply h0 horth f)

variable {X : Type*} [Fintype X]

theorem cfInner_finsuppSum_finsuppSum_gram {ι : Type*} (v : ι → X → ℂ) (a c : ι →₀ ℤ) :
    cfInner (a.sum fun i n => (n : ℂ) • v i) (c.sum fun j m => (m : ℂ) • v j)
      = ∑ i ∈ a.support, ∑ j ∈ c.support, (a i : ℂ) * (c j : ℂ) * cfInner (v i) (v j) := by
  rw [Finsupp.sum, Finsupp.sum, cfInner_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cfInner_smul_left, cfInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cfInner_smul_right, map_intCast]
  ring

theorem cfInner_apply_apply_eq_of_gram {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis ι ℤ M) (u : ι → La → ℂ) (V : ι → X → ℂ)
    (ψm : M →ₗ[ℤ] (La → ℂ)) (hψ : ∀ i, ψm (b i) = u i)
    (φ : M →ₗ[ℤ] (X → ℂ)) (hφ : ∀ i, φ (b i) = V i)
    (hgram : ∀ i j, cfInner (V i) (V j) = cfInner (u i) (u j))
    (f g : M) : cfInner (φ f) (φ g) = cfInner (ψm f) (ψm g) := by
  rw [apply_eq_finsuppSum_smul b φ f, apply_eq_finsuppSum_smul b φ g,
    apply_eq_finsuppSum_smul b ψm f, apply_eq_finsuppSum_smul b ψm g]
  simp only [hφ, hψ]
  rw [cfInner_finsuppSum_finsuppSum_gram, cfInner_finsuppSum_finsuppSum_gram]
  simp only [hgram]

noncomputable def orthSpanExtend {U : Set (La → ℂ)} {p : Submodule ℤ (X → ℂ)}
    (h0 : ∀ f ∈ U, cfInner f f ≠ 0)
    (horth : ∀ f ∈ U, ∀ g ∈ U, f ≠ g → cfInner f g = 0) (V : U → p) :
    Submodule.span ℤ U →+ p :=
  ((orthSpanBasis h0 horth).constr ℤ V).toAddMonoidHom

@[simp] theorem orthSpanExtend_apply {U : Set (La → ℂ)} {p : Submodule ℤ (X → ℂ)}
    (h0 : ∀ f ∈ U, cfInner f f ≠ 0)
    (horth : ∀ f ∈ U, ∀ g ∈ U, f ≠ g → cfInner f g = 0) (V : U → p) (f : U) :
    orthSpanExtend h0 horth V ⟨(f : La → ℂ), Submodule.subset_span f.2⟩ = V f := by
  rw [← orthSpanBasis_eq h0 horth f]
  exact (orthSpanBasis h0 horth).constr_basis ℤ V f

theorem cfInner_orthSpanExtend {U : Set (La → ℂ)} {p : Submodule ℤ (X → ℂ)}
    (h0 : ∀ f ∈ U, cfInner f f ≠ 0)
    (horth : ∀ f ∈ U, ∀ g ∈ U, f ≠ g → cfInner f g = 0) (V : U → p)
    (hgram : ∀ i j : U, cfInner (V i : X → ℂ) (V j : X → ℂ)
      = cfInner (i : La → ℂ) (j : La → ℂ)) (f g : Submodule.span ℤ U) :
    cfInner (orthSpanExtend h0 horth V f : X → ℂ) (orthSpanExtend h0 horth V g : X → ℂ)
      = cfInner (f : La → ℂ) (g : La → ℂ) :=
  cfInner_apply_apply_eq_of_gram (orthSpanBasis h0 horth) (fun i => (i : La → ℂ))
    (fun i => (V i : X → ℂ)) (Submodule.span ℤ U).subtype (orthSpanBasis_apply h0 horth)
    (p.subtype.comp ((orthSpanBasis h0 horth).constr ℤ V))
    (fun i => by
      change ((p.subtype.comp ((orthSpanBasis h0 horth).constr ℤ V)) (orthSpanBasis h0 horth i)
        : X → ℂ) = _
      rw [LinearMap.comp_apply, (orthSpanBasis h0 horth).constr_basis]
      rfl) hgram f g

end Free

theorem mem_span_Irr_of_isCharacter {La : Type*} [Group La] [Finite La] {γ : La → ℂ}
    (hγ : IsCharacter La γ) : γ ∈ Submodule.span ℤ (Irr La) := by
  obtain ⟨V, rfl⟩ := isCharacter_iff.1 hγ
  exact FDRep.character_mem_span_Irr V

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S T : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  {χ ψ : L → ℂ}

theorem cfInner_eq_zero_of_ne (hc : IsSubcoherent S tau R) {γ δ : L → ℂ} (hγ : γ ∈ S)
    (hδ : δ ∈ S) (h : γ ≠ δ) : cfInner γ δ = 0 := by
  rw [← charInner_eq_cfInner]
  exact hc.charInner_eq_zero γ hγ δ hδ h

theorem exists_pos_nat_cfInner_self_of_mem (hc : IsSubcoherent S tau R) {γ : L → ℂ}
    (hγ : γ ∈ S) : ∃ n : ℕ, 0 < n ∧ cfInner γ γ = (n : ℂ) :=
  exists_pos_nat_cfInner_self (mem_span_Irr_of_isCharacter (hc.isCharacter γ hγ))
    (hc.ne_zero γ hγ)

theorem cfInner_self_ne_zero_of_mem (hc : IsSubcoherent S tau R) {γ : L → ℂ} (hγ : γ ∈ S) :
    cfInner γ γ ≠ 0 := by
  obtain ⟨n, hn0, hn⟩ := exists_pos_nat_cfInner_self_of_mem hc hγ
  rw [hn]
  exact_mod_cast hn0.ne'

theorem cfInner_tau_tau (hc : IsSubcoherent S tau R) {f h : L → ℂ}
    (hf : f ∈ intSpanZeroAtOne (S : Set (L → ℂ)))
    (hh : h ∈ intSpanZeroAtOne (S : Set (L → ℂ))) :
    cfInner (tau f) (tau h) = cfInner f h := by
  rw [← charInner_eq_cfInner, ← charInner_eq_cfInner]
  exact hc.charInner_tau_tau f hf h hh

theorem cfInner_R_self (hc : IsSubcoherent S tau R) (hχS : χ ∈ S) {r : G → ℂ} (hr : r ∈ R χ) :
    cfInner r r = 1 := by
  rw [← charInner_eq_cfInner]
  exact hc.charInner_R_self χ hχS r hr

theorem cfInner_R_of_ne (hc : IsSubcoherent S tau R) (hχS : χ ∈ S) {r s : G → ℂ} (hr : r ∈ R χ)
    (hs : s ∈ R χ) (h : r ≠ s) : cfInner r s = 0 := by
  rw [← charInner_eq_cfInner]
  exact hc.charInner_R_of_ne χ hχS r hr s hs h

theorem R_subset_span_Irr (hc : IsSubcoherent S tau R) (hχS : χ ∈ S) :
    ((R χ : Finset (G → ℂ)) : Set (G → ℂ)) ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) :=
  fun r hr => mem_span_Irr_of_mem_virtualCharSpan (hc.R_subset χ hχS r (Finset.mem_coe.1 hr))

theorem card_R_eq_two_mul' (hc : IsSubcoherent S tau R) (hχS : χ ∈ S) {nχ : ℕ}
    (hnχ : cfInner χ χ = (nχ : ℂ)) : (R χ).card = 2 * nχ := by
  have h := hc.card_R hχS
  rw [charInner_eq_cfInner, hnχ] at h
  have hcast : ((R χ).card : ℂ) = ((2 * nχ : ℕ) : ℂ) := by push_cast; rw [h]
  exact_mod_cast hcast

theorem cfInner_sum_sum_R (hc : IsSubcoherent S tau R) (hχS : χ ∈ S) {E F : Finset (G → ℂ)}
    (hE : E ⊆ R χ) (hF : F ⊆ R χ) :
    cfInner (∑ r ∈ E, r) (∑ r ∈ F, r) = (((E ∩ F : Finset (G → ℂ)).card : ℕ) : ℂ) := by
  classical
  exact cfInner_sum_sum_of_orthonormal (fun r hr => cfInner_R_self hc hχS hr)
    (fun r hr s hs h => cfInner_R_of_ne hc hχS hr hs h) hE hF

omit [Fintype L] in
theorem sub_nsmul_mem_intSpanZeroAtOne (hχS : χ ∈ S) (hψS : ψ ∈ S) {d : ℕ}
    (hdeg : χ 1 = (d : ℂ) * ψ 1) :
    χ - (d : ℤ) • ψ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := by
  refine mem_intSpanZeroAtOne.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχS)
    (Submodule.smul_mem _ _ (Submodule.subset_span hψS)), ?_⟩
  change χ 1 - ((d : ℤ) • ψ) 1 = 0
  simp [hdeg]

omit [Fintype L] in
theorem smul_sub_smul_mem_charSpanZero {γ : L → ℂ} {p g : ℕ} (hγT : γ ∈ T) (hψT : ψ ∈ T)
    (hp : ψ 1 = (p : ℂ)) (hg : γ 1 = (g : ℂ)) :
    (p : ℤ) • γ - (g : ℤ) • ψ ∈ charSpanZero (T : Set (L → ℂ)) := by
  refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _
    (Submodule.subset_span hγT)) (Submodule.smul_mem _ _ (Submodule.subset_span hψT)), ?_⟩
  change ((p : ℤ) • γ) 1 - ((g : ℤ) • ψ) 1 = 0
  simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast, hp, hg]
  ring

omit [Fintype L] [Group G] [Fintype G] in
theorem mem_intSpanZeroAtOne_of_mem_charSpanZero {U : Set (L → ℂ)}
    (hUS : U ⊆ (S : Set (L → ℂ))) {f : L → ℂ} (hf : f ∈ charSpanZero U) :
    f ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
  mem_intSpanZeroAtOne.2
    ⟨Submodule.span_mono hUS (mem_charSpanZero.1 hf).1, (mem_charSpanZero.1 hf).2⟩

noncomputable def subTauHom (hc : IsSubcoherent S tau R) {U : Set (L → ℂ)}
    (hUS : U ⊆ (S : Set (L → ℂ))) : charSpanZero U →+ virtualChars G where
  toFun f := ⟨tau (f : L → ℂ), mem_virtualChars_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualCharSpan
      (hc.tau_mem _ (mem_intSpanZeroAtOne_of_mem_charSpanZero hUS f.2)))⟩
  map_zero' := Subtype.ext (by simpa using hc.tau_zero)
  map_add' f g := Subtype.ext
    (hc.map_add _ (mem_intSpanZeroAtOne_of_mem_charSpanZero hUS f.2) _
      (mem_intSpanZeroAtOne_of_mem_charSpanZero hUS g.2))

@[simp] theorem subTauHom_apply (hc : IsSubcoherent S tau R) {U : Set (L → ℂ)}
    (hUS : U ⊆ (S : Set (L → ℂ))) (f : charSpanZero U) :
    (subTauHom hc hUS f : G → ℂ) = tau (f : L → ℂ) := (rfl)

section InsertPair

variable {La : Type*} {Ta : Finset (La → ℂ)} {a : La → ℂ} [Star (La → ℂ)]

def insertPair (a : La → ℂ) (Ta : Finset (La → ℂ)) : Set (La → ℂ) :=
  {a, star a} ∪ (Ta : Set (La → ℂ))

theorem mem_insertPair_iff {f : La → ℂ} :
    f ∈ insertPair a Ta ↔ f = a ∨ f = star a ∨ f ∈ Ta := by
  simp [insertPair, or_assoc]

theorem self_mem_insertPair : a ∈ insertPair a Ta := mem_insertPair_iff.2 (Or.inl rfl)

theorem star_self_mem_insertPair : star a ∈ insertPair a Ta :=
  mem_insertPair_iff.2 (Or.inr (Or.inl rfl))

theorem subset_insertPair : (Ta : Set (La → ℂ)) ⊆ insertPair a Ta :=
  fun _ hf => mem_insertPair_iff.2 (Or.inr (Or.inr hf))

theorem span_le_span_insertPair :
    Submodule.span ℤ (Ta : Set (La → ℂ)) ≤ Submodule.span ℤ (insertPair a Ta) :=
  Submodule.span_mono subset_insertPair

theorem self_mem_span_insertPair : a ∈ Submodule.span ℤ (insertPair a Ta) :=
  Submodule.subset_span self_mem_insertPair

theorem star_self_mem_span_insertPair : star a ∈ Submodule.span ℤ (insertPair a Ta) :=
  Submodule.subset_span star_self_mem_insertPair

theorem mem_of_mem_insertPair {f : La → ℂ} (hf : f ∈ insertPair a Ta) (h1 : f ≠ a)
    (h2 : f ≠ star a) : f ∈ Ta := by
  rcases mem_insertPair_iff.1 hf with h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h

theorem span_insertPair_eq :
    Submodule.span ℤ (insertPair a Ta)
      = Submodule.span ℤ ({a, star a} : Set (La → ℂ)) ⊔ Submodule.span ℤ (Ta : Set (La → ℂ)) := by
  rw [← Submodule.span_union]
  congr 1

end InsertPair

theorem insertPair_subset (hc : IsSubcoherent S tau R) (hTS : T ⊆ S) (hχS : χ ∈ S) :
    insertPair χ T ⊆ (S : Set (L → ℂ)) := by
  intro f hf
  rcases mem_insertPair_iff.1 hf with rfl | rfl | hf
  · exact hχS
  · exact hc.star_mem _ hχS
  · exact hTS hf

omit [Fintype L] [Group G] [Fintype G] in
theorem exists_decomp_charSpanZero_insertPair {d : ℕ}
    (hdeg : χ 1 = (d : ℂ) * ψ 1) (hχstar1 : (star χ) 1 = χ 1) (hψT : ψ ∈ T)
    {f : L → ℂ} (hf : f ∈ charSpanZero (insertPair χ T)) :
    ∃ (m m' : ℤ) (h : L → ℂ), h ∈ charSpanZero (T : Set (L → ℂ)) ∧
      f = m • (χ - (d : ℤ) • ψ) + m' • (χ - star χ) + h := by
  classical
  obtain ⟨hspan, hzero⟩ := mem_charSpanZero.1 hf
  rw [span_insertPair_eq, Submodule.mem_sup] at hspan
  obtain ⟨y, hy, z, hz, hyz⟩ := hspan
  obtain ⟨k, k', hk⟩ := Submodule.mem_span_pair.1 hy
  refine ⟨k + k', -k', z + (k + k') • ((d : ℤ) • ψ), ?_, ?_⟩
  · refine mem_charSpanZero.2 ⟨Submodule.add_mem _ hz (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.subset_span hψT))), ?_⟩
    have hz1 : z 1 = f 1 - (k • χ + k' • star χ) 1 := by rw [← hyz, ← hk]; simp
    change z 1 + ((k + k') • ((d : ℤ) • ψ)) 1 = 0
    rw [hz1, hzero]
    simp only [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, hχstar1, hdeg]
    push_cast
    ring
  · rw [← hyz, ← hk]
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]
    push_cast
    ring

theorem cfInner_tau_sub_apply (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
    {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
    (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    (hψT : ψ ∈ T) (hχS : χ ∈ S) (hχT : χ ∉ T) {d p gg : ℕ} (hp : ψ 1 = (p : ℂ))
    {γ : L → ℂ} (hγT : γ ∈ T) (hg : γ 1 = (gg : ℂ)) (hdeg : χ 1 = (d : ℂ) * ψ 1) :
    (p : ℂ) * cfInner (tau (χ - (d : ℤ) • ψ)) (ν ⟨γ, mem_span_of_mem hγT⟩ : G → ℂ)
      - (gg : ℂ) * cfInner (tau (χ - (d : ℤ) • ψ)) (ν ⟨ψ, mem_span_of_mem hψT⟩ : G → ℂ)
        = (d : ℂ) * gg * cfInner ψ ψ - (if γ = ψ then (d : ℂ) * p * cfInner ψ ψ else 0) := by
  classical
  have hψS : ψ ∈ S := hTS hψT
  have hγS : γ ∈ S := hTS hγT
  have hχγ : χ ≠ γ := fun h => hχT (h ▸ hγT)
  have hχψ : χ ≠ ψ := fun h => hχT (h ▸ hψT)
  have hAmem : χ - (d : ℤ) • ψ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    sub_nsmul_mem_intSpanZeroAtOne hχS hψS hdeg
  have hFz : (p : ℤ) • γ - (gg : ℤ) • ψ ∈ charSpanZero (T : Set (L → ℂ)) :=
    smul_sub_smul_mem_charSpanZero hγT hψT hp hg
  have hFS : (p : ℤ) • γ - (gg : ℤ) • ψ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    mem_intSpanZeroAtOne_of_mem_charSpanZero (by exact_mod_cast hTS) hFz
  have hνF : (ν ⟨(p : ℤ) • γ - (gg : ℤ) • ψ, charSpanZero_le _ hFz⟩ : G → ℂ)
      = tau ((p : ℤ) • γ - (gg : ℤ) • ψ) := by
    rw [show (⟨(p : ℤ) • γ - (gg : ℤ) • ψ, charSpanZero_le _ hFz⟩
        : Submodule.span ℤ (T : Set (L → ℂ)))
      = Submodule.inclusion (charSpanZero_le _) ⟨_, hFz⟩ from rfl, hν.eq_on_zero ⟨_, hFz⟩, hτT]
  have hνF2 : (ν ⟨(p : ℤ) • γ - (gg : ℤ) • ψ, charSpanZero_le _ hFz⟩ : G → ℂ)
      = (p : ℤ) • (ν ⟨γ, mem_span_of_mem hγT⟩ : G → ℂ)
        - (gg : ℤ) • (ν ⟨ψ, mem_span_of_mem hψT⟩ : G → ℂ) := by
    rw [show (⟨(p : ℤ) • γ - (gg : ℤ) • ψ, charSpanZero_le _ hFz⟩
        : Submodule.span ℤ (T : Set (L → ℂ)))
      = (p : ℤ) • ⟨γ, mem_span_of_mem hγT⟩ - (gg : ℤ) • ⟨ψ, mem_span_of_mem hψT⟩ from rfl,
      map_sub, map_zsmul, map_zsmul]
    rfl
  have key : cfInner (tau (χ - (d : ℤ) • ψ)) (tau ((p : ℤ) • γ - (gg : ℤ) • ψ))
      = cfInner (χ - (d : ℤ) • ψ) ((p : ℤ) • γ - (gg : ℤ) • ψ) :=
    cfInner_tau_tau hc hAmem hFS
  rw [← hνF, hνF2, cfInner_sub_right, cfInner_zsmul_right, cfInner_zsmul_right] at key
  push_cast at key
  rw [key, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_zsmul_left, cfInner_zsmul_left,
    cfInner_zsmul_right, cfInner_zsmul_right, cfInner_zsmul_right, cfInner_zsmul_right,
    cfInner_eq_zero_of_ne hc hχS hγS hχγ, cfInner_eq_zero_of_ne hc hχS hψS hχψ]
  by_cases hgp : γ = ψ
  · subst hgp
    rw [if_pos rfl]
    have hgpp : (gg : ℂ) = (p : ℂ) := by rw [← hg, hp]
    push_cast
    rw [hgpp]
    ring
  · rw [if_neg hgp, cfInner_eq_zero_of_ne hc hψS hγS (Ne.symm hgp)]
    push_cast
    ring

theorem exists_int_coeff_and_proj_sub_eq (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTstar : ∀ γ ∈ T, star γ ∈ T)
    {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
    {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
    (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    (hψT : ψ ∈ T) (hχS : χ ∈ S) (hχT : χ ∉ T) {d : ℕ} (hd : 1 ≤ d)
    (hdeg : χ 1 = (d : ℂ) * ψ 1)
    (hFeit : 2 * χ 1 * ψ 1 < ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ) :
    ∃ a : (G → ℂ) → ℤ, (∀ r ∈ R χ, cfInner (tau (χ - (d : ℤ) • ψ)) r = (a r : ℂ)) ∧
      (∀ r ∈ R χ, a r = 0 ∨ a r = 1) ∧
      (∑ r ∈ R χ, (a r : ℂ) • r) - tau (χ - (d : ℤ) • ψ)
        = (d : ℤ) • (ν ⟨ψ, mem_span_of_mem hψT⟩ : G → ℂ) := by
  classical
  have hψS : ψ ∈ S := hTS hψT
  have hstarχS : star χ ∈ S := hc.star_mem χ hχS
  have hstarχT : star χ ∉ T := fun h => hχT (by simpa using hTstar _ h)
  have hχstar : χ ≠ star χ := Ne.symm (hc.star_ne χ hχS)
  have hχψ : χ ≠ ψ := fun h => hχT (h ▸ hψT)
  have hψχ : ψ ≠ χ := Ne.symm hχψ
  have hψstar : ψ ≠ star χ := fun h => hstarχT (h ▸ hψT)
  obtain ⟨p, hp0, hp⟩ := (hc.isCharacter ψ hψS).exists_pos_nat_apply_one (hc.ne_zero ψ hψS)
  have hgex : ∀ γ ∈ S, ∃ m : ℕ, 0 < m ∧ γ 1 = (m : ℂ) := fun γ hγ =>
    (hc.isCharacter γ hγ).exists_pos_nat_apply_one (hc.ne_zero γ hγ)
  choose! g hg0 hg using hgex
  have hnex : ∀ γ ∈ S, ∃ m : ℕ, 0 < m ∧ cfInner γ γ = (m : ℂ) := fun γ hγ =>
    exists_pos_nat_cfInner_self_of_mem hc hγ
  choose! n hn0 hn using hnex
  have hpC : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp0.ne'
  have hgψ : g ψ = p := by
    have hgg := hg ψ hψS
    rw [hp] at hgg
    exact_mod_cast hgg.symm
  have hAmem : χ - (d : ℤ) • ψ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    sub_nsmul_mem_intSpanZeroAtOne hχS hψS hdeg
  set α : G → ℂ := tau (χ - (d : ℤ) • ψ) with halpha
  have hαmem : α ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualCharSpan (hc.tau_mem _ hAmem)
  obtain ⟨a, ha, horthY, hXX, hle, hspl, hiff⟩ :=
    exists_int_coeff_and_bounds (R_subset_span_Irr hc hχS)
      (fun r hr => cfInner_R_self hc hχS hr)
      (fun r hr s hs h => cfInner_R_of_ne hc hχS hr hs h) hαmem
  set Xv : G → ℂ := ∑ r ∈ R χ, cfInner α r • r with hXv
  set Y : G → ℂ := Xv - α with hY
  have hαsumR : cfInner α (∑ r ∈ R χ, r) = cfInner χ χ := by
    rw [halpha, ← hc.tau_sub_star χ hχS, cfInner_tau_tau hc hAmem (hc.sub_star_mem hχS),
      cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_zsmul_left,
      cfInner_zsmul_left, cfInner_eq_zero_of_ne hc hχS hstarχS hχstar,
      cfInner_eq_zero_of_ne hc hψS hχS hψχ, cfInner_eq_zero_of_ne hc hψS hstarχS hψstar]
    ring
  have hsuma : ((∑ r ∈ R χ, a r : ℤ) : ℂ) = (n χ : ℂ) := by
    rw [← sum_cfInner_eq_intCast ha, ← cfInner_sum_right, hαsumR, hn χ hχS]
  have hnormα : cfInner α α = (n χ : ℂ) + (d : ℂ) ^ 2 * (n ψ : ℂ) := by
    rw [halpha, cfInner_tau_tau hc hAmem hAmem, cfInner_sub_left, cfInner_sub_right,
      cfInner_sub_right, cfInner_zsmul_left, cfInner_zsmul_right, cfInner_zsmul_right,
      cfInner_zsmul_left, cfInner_eq_zero_of_ne hc hχS hψS hχψ,
      cfInner_eq_zero_of_ne hc hψS hχS hψχ, hn χ hχS, hn ψ hψS]
    push_cast; ring
  have hXXval : cfInner Xv Xv = ((∑ r ∈ R χ, a r ^ 2 : ℤ) : ℂ) := hXX
  have hYnorm : cfInner Y Y ≤ (d : ℂ) ^ 2 * (n ψ : ℂ) := by
    have hYY : cfInner Y Y = cfInner (α - Xv) (α - Xv) := by
      rw [hY, show Xv - α = -(α - Xv) by ring, cfInner_neg_left, cfInner_neg_right, neg_neg]
    rw [hYY]
    have h1 : cfInner (α - Xv) (α - Xv) = cfInner α α - cfInner Xv Xv := by rw [hspl]; ring
    rw [h1, hnormα, hXXval]
    have h2 : ((∑ r ∈ R χ, a r : ℤ) : ℂ) ≤ ((∑ r ∈ R χ, a r ^ 2 : ℤ) : ℂ) := by
      exact_mod_cast hle
    rw [hsuma] at h2
    have h3 : (n χ : ℂ) - ((∑ r ∈ R χ, a r ^ 2 : ℤ) : ℂ) ≤ 0 := sub_nonpos.2 h2
    calc (n χ : ℂ) + (d : ℂ) ^ 2 * (n ψ : ℂ) - ((∑ r ∈ R χ, a r ^ 2 : ℤ) : ℂ)
        = (d : ℂ) ^ 2 * (n ψ : ℂ) + ((n χ : ℂ) - ((∑ r ∈ R χ, a r ^ 2 : ℤ) : ℂ)) := by ring
    _ ≤ (d : ℂ) ^ 2 * (n ψ : ℂ) + 0 := add_le_add_right h3 ((d : ℂ) ^ 2 * (n ψ : ℂ))
    _ = (d : ℂ) ^ 2 * (n ψ : ℂ) := by ring
  have hXvorth : ∀ f : Submodule.span ℤ (T : Set (L → ℂ)), cfInner Xv (ν f : G → ℂ) = 0 := by
    intro f
    rw [hXv, cfInner_sum_left]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [cfInner_smul_left,
      show cfInner r (ν f : G → ℂ) = 0 from by
        rw [← conj_cfInner, cfInner_eq_zero_of_notMem hc hTS hTstar hν hτT hχS hχT f hr,
          map_zero],
      mul_zero]
  set nuv : (L → ℂ) → (G → ℂ) := fun γ =>
    if h : γ ∈ T then (ν ⟨γ, mem_span_of_mem h⟩ : G → ℂ) else 0 with hnuv
  have hnuv_eq : ∀ γ (h : γ ∈ T), nuv γ = (ν ⟨γ, mem_span_of_mem h⟩ : G → ℂ) := by
    intro γ h; rw [hnuv]; simp only [dif_pos h]
  have hYnuv : ∀ γ ∈ T, cfInner Y (nuv γ) = -cfInner α (nuv γ) := by
    intro γ hγ
    rw [hY, cfInner_sub_left, hnuv_eq γ hγ, hXvorth, zero_sub]
  have hnuvgram : ∀ γ ∈ T, ∀ δ ∈ T, cfInner (nuv γ) (nuv δ) = cfInner γ δ := by
    intro γ hγ δ hδ
    rw [hnuv_eq γ hγ, hnuv_eq δ hδ]
    exact hν.inner_eq _ _
  have hnuvnn : ∀ γ ∈ T, cfInner (nuv γ) (nuv γ) = (n γ : ℂ) := by
    intro γ hγ
    rw [hnuvgram γ hγ γ hγ, hn γ (hTS hγ)]
  have hnuvorth : ∀ γ ∈ T, ∀ δ ∈ T, γ ≠ δ → cfInner (nuv γ) (nuv δ) = 0 := by
    intro γ hγ δ hδ hne
    rw [hnuvgram γ hγ δ hδ]
    exact cfInner_eq_zero_of_ne hc (hTS hγ) (hTS hδ) hne
  obtain ⟨lamY, hlamY⟩ := exists_int_cfInner_of_mem_span_Irr
    (show Y ∈ Submodule.span ℤ (Irr G) from Submodule.sub_mem _
      (by rw [hXv, sum_cfInner_smul_eq ha]
          refine Submodule.sum_mem _ fun r hr => ?_
          rw [show ((a r : ℂ)) • r = (a r) • r from (Int.cast_smul_eq_zsmul ℂ _ _)]
          exact Submodule.smul_mem _ _ (R_subset_span_Irr hc hχS (Finset.mem_coe.2 hr)))
      hαmem) (coe_mem_span_Irr (ν ⟨ψ, mem_span_of_mem hψT⟩))
  set lam : ℤ := (d : ℤ) * (n ψ : ℤ) - lamY with hlam
  have hYψ : cfInner Y (nuv ψ) = (d : ℂ) * (n ψ : ℂ) - (lam : ℂ) := by
    rw [hnuv_eq ψ hψT, hlamY, hlam]
    push_cast
    ring
  have hYγ : ∀ γ ∈ T, cfInner Y (nuv γ)
      = (if γ = ψ then (d : ℂ) * (n ψ : ℂ) else 0) - (lam : ℂ) * (g γ : ℂ) / (p : ℂ) := by
    intro γ hγ
    have hrel := cfInner_tau_sub_apply hc hTS hν hτT hψT hχS hχT hp hγ (hg γ (hTS hγ)) hdeg
    rw [hn ψ hψS] at hrel
    rw [← hnuv_eq γ hγ, ← hnuv_eq ψ hψT] at hrel
    have hαγ : cfInner α (nuv γ) = -cfInner Y (nuv γ) := by rw [hYnuv γ hγ]; ring
    have hαψ : cfInner α (nuv ψ) = -cfInner Y (nuv ψ) := by rw [hYnuv ψ hψT]; ring
    rw [hαγ, hαψ, hYψ] at hrel
    refine mul_left_cancel₀ hpC ?_
    by_cases hgp : γ = ψ
    · subst hgp
      rw [if_pos rfl, hgψ] at *
      rw [show (lam : ℂ) * (p : ℂ) / (p : ℂ) = (lam : ℂ) from by field_simp]
      linear_combination -hrel
    · rw [if_neg hgp] at hrel ⊢
      rw [show (p : ℂ) * (0 - (lam : ℂ) * (g γ : ℂ) / (p : ℂ)) = -((lam : ℂ) * (g γ : ℂ))
        from by field_simp; ring]
      linear_combination -hrel
  have hbessel := cfInner_self_eq_sum_div_add (Tt := T) nuv
    (fun i hi j hj hij => hnuvorth i hi j hj hij) Y
  set Z : ℂ := cfInner (Y - ∑ γ ∈ T, (cfInner Y (nuv γ) / cfInner (nuv γ) (nuv γ)) • nuv γ)
      (Y - ∑ γ ∈ T, (cfInner Y (nuv γ) / cfInner (nuv γ) (nuv γ)) • nuv γ) with hZ
  have hZnn : 0 ≤ Z := cfInner_self_nonneg _
  have hsumcomp : ∑ γ ∈ T, cfInner Y (nuv γ) * conj (cfInner Y (nuv γ)) / cfInner (nuv γ) (nuv γ)
      = (d : ℂ) ^ 2 * (n ψ : ℂ) - 2 * (d : ℂ) * (lam : ℂ)
        + (lam : ℂ) ^ 2 / (p : ℂ) ^ 2 * ∑ γ ∈ T, (g γ : ℂ) ^ 2 / (n γ : ℂ) := by
    have step : ∀ γ ∈ T,
        cfInner Y (nuv γ) * conj (cfInner Y (nuv γ)) / cfInner (nuv γ) (nuv γ)
          = (if γ = ψ then (d : ℂ) ^ 2 * (n ψ : ℂ) - 2 * (d : ℂ) * (lam : ℂ) else 0)
            + (lam : ℂ) ^ 2 / (p : ℂ) ^ 2 * ((g γ : ℂ) ^ 2 / (n γ : ℂ)) := by
      intro γ hγ
      have hnC : ((n γ : ℂ)) ≠ 0 := by exact_mod_cast (hn0 γ (hTS hγ)).ne'
      rw [hYγ γ hγ, hnuvnn γ hγ]
      by_cases h : γ = ψ
      · subst h
        rw [if_pos rfl, if_pos rfl, hgψ,
          show conj ((d : ℂ) * (n γ : ℂ) - (lam : ℂ) * (p : ℂ) / (p : ℂ))
            = (d : ℂ) * (n γ : ℂ) - (lam : ℂ) * (p : ℂ) / (p : ℂ) from by simp]
        field_simp
        ring
      · rw [if_neg h, if_neg h,
          show conj ((0 : ℂ) - (lam : ℂ) * (g γ : ℂ) / (p : ℂ))
            = (0 : ℂ) - (lam : ℂ) * (g γ : ℂ) / (p : ℂ) from by simp]
        field_simp
        ring
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib,
      Finset.sum_ite_eq' T ψ (fun _ => (d : ℂ) ^ 2 * (n ψ : ℂ) - 2 * (d : ℂ) * (lam : ℂ)),
      if_pos hψT, ← Finset.mul_sum]
  set Sig : ℂ := ∑ γ ∈ T, (g γ : ℂ) ^ 2 / (n γ : ℂ) with hSig
  have hFeit2 : 2 * (d : ℂ) * (p : ℂ) ^ 2 < Sig := by
    have hsumeq : ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ = Sig := by
      rw [hSig]
      exact Finset.sum_congr rfl fun γ hγ => by rw [hg γ (hTS hγ), hn γ (hTS hγ)]
    rw [hsumeq, hdeg, hp] at hFeit
    calc 2 * (d : ℂ) * (p : ℂ) ^ 2 = 2 * ((d : ℂ) * (p : ℂ)) * (p : ℂ) := by ring
    _ < Sig := hFeit
  have hcD : 2 * (d : ℂ) < Sig / (p : ℂ) ^ 2 := by
    have hp2 : (0 : ℂ) < (p : ℂ) ^ 2 := by
      have hpp : (0 : ℂ) < (p : ℂ) := by exact_mod_cast hp0
      positivity
    rw [lt_div_iff₀ hp2]
    exact hFeit2
  have hDpos : (0 : ℂ) < (d : ℂ) := by exact_mod_cast hd
  have hsqueeze : (lam : ℂ) ^ 2 * (Sig / (p : ℂ) ^ 2) + Z ≤ 2 * (d : ℂ) * (lam : ℂ) := by
    rw [hsumcomp] at hbessel
    have hb : (d : ℂ) ^ 2 * (n ψ : ℂ) - 2 * (d : ℂ) * (lam : ℂ)
        + (lam : ℂ) ^ 2 * (Sig / (p : ℂ) ^ 2) + Z ≤ (d : ℂ) ^ 2 * (n ψ : ℂ) := by
      rw [show (lam : ℂ) ^ 2 * (Sig / (p : ℂ) ^ 2)
        = (lam : ℂ) ^ 2 / (p : ℂ) ^ 2 * Sig from by ring, ← hbessel]
      exact hYnorm
    set A : ℂ := (d : ℂ) ^ 2 * (n ψ : ℂ)
    set B : ℂ := 2 * (d : ℂ) * (lam : ℂ)
    set C : ℂ := (lam : ℂ) ^ 2 * (Sig / (p : ℂ) ^ 2)
    refine sub_nonpos.1 ((add_le_add_iff_left A).1 ?_)
    rw [add_zero]
    calc A + (C + Z - B) = A - B + C + Z := by ring
    _ ≤ A := hb
  obtain ⟨hlam0, hZ0⟩ := eq_zero_of_sq_mul_add_le hZnn hDpos hcD hsqueeze
  have hYd : Y = (d : ℤ) • (ν ⟨ψ, mem_span_of_mem hψT⟩ : G → ℂ) := by
    have hZeq : Y - ∑ γ ∈ T, (cfInner Y (nuv γ) / cfInner (nuv γ) (nuv γ)) • nuv γ = 0 :=
      cfInner_self_eq_zero.1 hZ0
    have hproj : ∑ γ ∈ T, (cfInner Y (nuv γ) / cfInner (nuv γ) (nuv γ)) • nuv γ
        = (d : ℂ) • nuv ψ := by
      have step : ∀ γ ∈ T, (cfInner Y (nuv γ) / cfInner (nuv γ) (nuv γ)) • nuv γ
          = if γ = ψ then (d : ℂ) • nuv ψ else 0 := by
        intro γ hγ
        have hnC : ((n γ : ℂ)) ≠ 0 := by exact_mod_cast (hn0 γ (hTS hγ)).ne'
        rw [hYγ γ hγ, hnuvnn γ hγ, hlam0]
        by_cases h : γ = ψ
        · rw [if_pos h, if_pos h]
          subst h
          push_cast
          rw [zero_mul, zero_div, sub_zero]
          congr 1
          field_simp
        · rw [if_neg h, if_neg h]
          push_cast
          rw [zero_mul, zero_div, sub_zero, zero_div, zero_smul]
      rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' T ψ (fun _ => (d : ℂ) • nuv ψ),
        if_pos hψT]
    rw [hproj, sub_eq_zero] at hZeq
    rw [hZeq, hnuv_eq ψ hψT, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  have hYYval : cfInner Y Y = (d : ℂ) ^ 2 * (n ψ : ℂ) := by
    rw [hYd, cfInner_zsmul_left, cfInner_zsmul_right, hν.inner_eq, hn ψ hψS]
    push_cast
    ring
  refine ⟨a, ha, ?_, ?_⟩
  · refine hiff.1 ?_
    have hYY : cfInner (α - Xv) (α - Xv) = cfInner Y Y := by
      rw [hY, show Xv - α = -(α - Xv) by ring, cfInner_neg_left, cfInner_neg_right, neg_neg]
    rw [hYY, hYYval, hnormα] at hspl
    rw [hsuma]
    linear_combination -hspl
  · rw [← sum_cfInner_smul_eq ha, ← hXv]
    exact hYd

theorem exists_isCoherentWith_of_tau_eq (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTstar : ∀ γ ∈ T, star γ ∈ T)
    {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
    {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
    (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    (hψT : ψ ∈ T) (hχS : χ ∈ S) (hχT : χ ∉ T) {d : ℕ}
    (hdeg : χ 1 = (d : ℂ) * ψ 1)
    {nχ : ℕ} (hnχ : cfInner χ χ = (nχ : ℂ))
    {E : Finset (G → ℂ)} (hER : E ⊆ R χ) (hEcard : E.card = nχ)
    (hα : tau (χ - (d : ℤ) • ψ)
      = (∑ r ∈ E, r) - (d : ℤ) • (ν ⟨ψ, mem_span_of_mem hψT⟩ : G → ℂ)) :
    ∃ ν' : Submodule.span ℤ (insertPair χ T) →+ virtualChars G,
      IsCoherentWith (insertPair χ T) (subTauHom hc (insertPair_subset hc hTS hχS)) ν' ∧
      (∀ f : Submodule.span ℤ (T : Set (L → ℂ)),
        (ν' (Submodule.inclusion span_le_span_insertPair f) : G → ℂ) = (ν f : G → ℂ)) ∧
      (ν' ⟨χ, self_mem_span_insertPair⟩ : G → ℂ) = ∑ r ∈ E, r ∧
      (ν' ⟨star χ, star_self_mem_span_insertPair⟩ : G → ℂ) = -∑ r ∈ R χ \ E, r := by
  classical
  have hψS : ψ ∈ S := hTS hψT
  have hstarχS : star χ ∈ S := hc.star_mem χ hχS
  have hstarχT : star χ ∉ T := fun h => hχT (by simpa using hTstar _ h)
  have hχstar : χ ≠ star χ := Ne.symm (hc.star_ne χ hχS)
  have hUS : insertPair χ T ⊆ (S : Set (L → ℂ)) := insertPair_subset hc hTS hχS
  have h0 : ∀ f ∈ insertPair χ T, cfInner f f ≠ 0 :=
    fun f hf => cfInner_self_ne_zero_of_mem hc (hUS hf)
  have horth : ∀ f ∈ insertPair χ T, ∀ g ∈ insertPair χ T, f ≠ g → cfInner f g = 0 :=
    fun f hf g hg h => cfInner_eq_zero_of_ne hc (hUS hf) (hUS hg) h
  have hFR : R χ \ E ⊆ R χ := Finset.sdiff_subset
  have hFcard : (R χ \ E).card = nχ := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hER, card_R_eq_two_mul' hc hχS hnχ, hEcard]
    omega
  set Vχ : virtualChars G := ⟨∑ r ∈ E, r, Submodule.sum_mem _ fun r hr =>
    mem_virtualChars_of_mem_span_Irr
      (mem_span_Irr_of_mem_virtualCharSpan (hc.R_subset χ hχS r (hER hr)))⟩ with hVχdef
  set Vstar : virtualChars G := -⟨∑ r ∈ R χ \ E, r, Submodule.sum_mem _ fun r hr =>
    mem_virtualChars_of_mem_span_Irr
      (mem_span_Irr_of_mem_virtualCharSpan (hc.R_subset χ hχS r (hFR hr)))⟩ with hVstardef
  have hVχcoe : (Vχ : G → ℂ) = ∑ r ∈ E, r := rfl
  have hVstarcoe : (Vstar : G → ℂ) = -∑ r ∈ R χ \ E, r := rfl
  set V : ↥(insertPair χ T) → virtualChars G := fun f =>
    if h1 : (f : L → ℂ) = χ then Vχ
    else if h2 : (f : L → ℂ) = star χ then Vstar
    else ν ⟨(f : L → ℂ), mem_span_of_mem (mem_of_mem_insertPair f.2 h1 h2)⟩ with hVdef
  have hVχeq : V ⟨χ, self_mem_insertPair⟩ = Vχ := by rw [hVdef]; simp
  have hVstareq : V ⟨star χ, star_self_mem_insertPair⟩ = Vstar := by
    rw [hVdef]; simp [Ne.symm hχstar]
  have hVT : ∀ γ (h : γ ∈ T), V ⟨γ, subset_insertPair h⟩ = ν ⟨γ, mem_span_of_mem h⟩ := by
    intro γ h
    have h1 : γ ≠ χ := fun he => hχT (he ▸ h)
    have h2 : γ ≠ star χ := fun he => hstarχT (he ▸ h)
    rw [hVdef]; simp [h1, h2]
  have hgram : ∀ i j : ↥(insertPair χ T),
      cfInner (V i : G → ℂ) (V j : G → ℂ) = cfInner (i : L → ℂ) (j : L → ℂ) := by
    have hEE : cfInner (∑ r ∈ E, r) (∑ r ∈ E, r) = cfInner χ χ := by
      rw [cfInner_sum_sum_R hc hχS hER hER, Finset.inter_self, hEcard, hnχ]
    have hFF : cfInner (∑ r ∈ R χ \ E, r) (∑ r ∈ R χ \ E, r) = cfInner (star χ) (star χ) := by
      rw [cfInner_sum_sum_R hc hχS hFR hFR, Finset.inter_self, hFcard,
        show cfInner (star χ) (star χ) = (nχ : ℂ) from by
          rw [cfInner_star_star, ← conj_cfInner, hnχ]; simp]
    have hEF : cfInner (∑ r ∈ E, r) (∑ r ∈ R χ \ E, r) = 0 := by
      rw [cfInner_sum_sum_R hc hχS hER hFR, Finset.inter_sdiff_self]
      simp
    have hFE : cfInner (∑ r ∈ R χ \ E, r) (∑ r ∈ E, r) = 0 := by
      rw [cfInner_sum_sum_R hc hχS hFR hER, Finset.inter_comm, Finset.inter_sdiff_self]
      simp
    have hEν : ∀ F : Finset (G → ℂ), F ⊆ R χ →
        ∀ f : Submodule.span ℤ (T : Set (L → ℂ)), cfInner (∑ r ∈ F, r) (ν f : G → ℂ) = 0 := by
      intro F hF f
      rw [cfInner_sum_left]
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [← conj_cfInner, cfInner_eq_zero_of_notMem hc hTS hTstar hν hτT hχS hχT f (hF hr),
        map_zero]
    have hνE : ∀ F : Finset (G → ℂ), F ⊆ R χ →
        ∀ f : Submodule.span ℤ (T : Set (L → ℂ)), cfInner (ν f : G → ℂ) (∑ r ∈ F, r) = 0 := by
      intro F hF f
      rw [← conj_cfInner, hEν F hF f, map_zero]
    intro i j
    rcases mem_insertPair_iff.1 i.2 with hi | hi | hi
    · rcases mem_insertPair_iff.1 j.2 with hj | hj | hj
      · rw [show i = ⟨χ, self_mem_insertPair⟩ from Subtype.ext hi,
          show j = ⟨χ, self_mem_insertPair⟩ from Subtype.ext hj, hVχeq, hVχcoe]
        exact hEE
      · rw [show i = ⟨χ, self_mem_insertPair⟩ from Subtype.ext hi,
          show j = ⟨star χ, star_self_mem_insertPair⟩ from Subtype.ext hj,
          hVχeq, hVstareq, hVχcoe, hVstarcoe, cfInner_neg_right, hEF, neg_zero]
        exact (cfInner_eq_zero_of_ne hc hχS hstarχS hχstar).symm
      · rw [show i = ⟨χ, self_mem_insertPair⟩ from Subtype.ext hi,
          show j = ⟨(j : L → ℂ), subset_insertPair hj⟩ from Subtype.ext rfl,
          hVχeq, hVT _ hj, hVχcoe, hEν E hER]
        exact (cfInner_eq_zero_of_ne hc hχS (hTS hj) (fun h => hχT (h ▸ hj))).symm
    · rcases mem_insertPair_iff.1 j.2 with hj | hj | hj
      · rw [show i = ⟨star χ, star_self_mem_insertPair⟩ from Subtype.ext hi,
          show j = ⟨χ, self_mem_insertPair⟩ from Subtype.ext hj,
          hVχeq, hVstareq, hVχcoe, hVstarcoe, cfInner_neg_left, hFE, neg_zero]
        exact (cfInner_eq_zero_of_ne hc hstarχS hχS (Ne.symm hχstar)).symm
      · rw [show i = ⟨star χ, star_self_mem_insertPair⟩ from Subtype.ext hi,
          show j = ⟨star χ, star_self_mem_insertPair⟩ from Subtype.ext hj,
          hVstareq, hVstarcoe, cfInner_neg_left, cfInner_neg_right, neg_neg]
        exact hFF
      · rw [show i = ⟨star χ, star_self_mem_insertPair⟩ from Subtype.ext hi,
          show j = ⟨(j : L → ℂ), subset_insertPair hj⟩ from Subtype.ext rfl,
          hVstareq, hVT _ hj, hVstarcoe, cfInner_neg_left, hEν _ hFR, neg_zero]
        exact (cfInner_eq_zero_of_ne hc hstarχS (hTS hj) (fun h => hstarχT (h ▸ hj))).symm
    · rcases mem_insertPair_iff.1 j.2 with hj | hj | hj
      · rw [show i = ⟨(i : L → ℂ), subset_insertPair hi⟩ from Subtype.ext rfl,
          show j = ⟨χ, self_mem_insertPair⟩ from Subtype.ext hj,
          hVχeq, hVT _ hi, hVχcoe, hνE E hER]
        exact (cfInner_eq_zero_of_ne hc (hTS hi) hχS (fun h => hχT (h ▸ hi))).symm
      · rw [show i = ⟨(i : L → ℂ), subset_insertPair hi⟩ from Subtype.ext rfl,
          show j = ⟨star χ, star_self_mem_insertPair⟩ from Subtype.ext hj,
          hVstareq, hVT _ hi, hVstarcoe, cfInner_neg_right, hνE _ hFR, neg_zero]
        exact (cfInner_eq_zero_of_ne hc (hTS hi) hstarχS (fun h => hstarχT (h ▸ hi))).symm
      · rw [show i = ⟨(i : L → ℂ), subset_insertPair hi⟩ from Subtype.ext rfl,
          show j = ⟨(j : L → ℂ), subset_insertPair hj⟩ from Subtype.ext rfl,
          hVT _ hi, hVT _ hj]
        exact hν.inner_eq _ _
  set ν' := orthSpanExtend h0 horth V with hν'def
  have hν'χ : (ν' ⟨χ, self_mem_span_insertPair⟩ : G → ℂ) = ∑ r ∈ E, r := by
    rw [hν'def, show (⟨χ, self_mem_span_insertPair⟩ : Submodule.span ℤ (insertPair χ T))
        = ⟨((⟨χ, self_mem_insertPair⟩ : ↥(insertPair χ T)) : L → ℂ),
            Submodule.subset_span self_mem_insertPair⟩ from rfl,
      orthSpanExtend_apply, hVχeq, hVχcoe]
  have hν'star : (ν' ⟨star χ, star_self_mem_span_insertPair⟩ : G → ℂ)
      = -∑ r ∈ R χ \ E, r := by
    rw [hν'def,
      show (⟨star χ, star_self_mem_span_insertPair⟩ : Submodule.span ℤ (insertPair χ T))
        = ⟨((⟨star χ, star_self_mem_insertPair⟩ : ↥(insertPair χ T)) : L → ℂ),
            Submodule.subset_span star_self_mem_insertPair⟩ from rfl,
      orthSpanExtend_apply, hVstareq, hVstarcoe]
  have hν'T : ∀ f : Submodule.span ℤ (T : Set (L → ℂ)),
      ν' (Submodule.inclusion span_le_span_insertPair f) = ν f := by
    intro f
    obtain ⟨u, hu⟩ := f
    induction hu using Submodule.span_induction with
    | mem x hx =>
        rw [show (Submodule.inclusion span_le_span_insertPair
            ⟨x, Submodule.subset_span hx⟩ : Submodule.span ℤ (insertPair χ T))
            = ⟨((⟨x, subset_insertPair hx⟩ : ↥(insertPair χ T)) : L → ℂ),
                Submodule.subset_span (subset_insertPair hx)⟩ from rfl,
          hν'def, orthSpanExtend_apply, hVT x (Finset.mem_coe.1 hx)]
    | zero =>
        rw [show (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℤ (T : Set (L → ℂ))) = 0 from rfl,
          map_zero, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
        rw [show (⟨x + y, Submodule.add_mem _ hx hy⟩ : Submodule.span ℤ (T : Set (L → ℂ)))
            = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, map_add, map_add, ihx, ihy]
    | smul m x hx ih =>
        rw [show (⟨m • x, Submodule.smul_mem _ m hx⟩ : Submodule.span ℤ (T : Set (L → ℂ)))
            = m • ⟨x, hx⟩ from rfl, map_zsmul, map_zsmul, map_zsmul, ih]
  refine ⟨ν', ⟨cfInner_orthSpanExtend h0 horth V hgram, ?_⟩,
    fun f => by rw [hν'T f], hν'χ, hν'star⟩
  intro f
  refine Subtype.ext ?_
  rw [subTauHom_apply]
  have hχstar1 : (star χ) 1 = χ 1 := (hc.isCharacter χ hχS).star_apply_one
  obtain ⟨m, m', h, hhz, hfeq⟩ :=
    exists_decomp_charSpanZero_insertPair (d := d) hdeg hχstar1 hψT f.2
  have hamem : χ - (d : ℤ) • ψ ∈ Submodule.span ℤ (insertPair χ T) :=
    Submodule.sub_mem _ self_mem_span_insertPair
      (Submodule.smul_mem _ _ (Submodule.span_mono subset_insertPair (mem_span_of_mem hψT)))
  have hbmem : χ - star χ ∈ Submodule.span ℤ (insertPair χ T) :=
    Submodule.sub_mem _ self_mem_span_insertPair star_self_mem_span_insertPair
  have hhmem : h ∈ Submodule.span ℤ (insertPair χ T) :=
    span_le_span_insertPair (charSpanZero_le _ hhz)
  have hν'a : (ν' ⟨χ - (d : ℤ) • ψ, hamem⟩ : G → ℂ) = tau (χ - (d : ℤ) • ψ) := by
    rw [show (⟨χ - (d : ℤ) • ψ, hamem⟩ : Submodule.span ℤ (insertPair χ T))
        = ⟨χ, self_mem_span_insertPair⟩
          - (d : ℤ) • Submodule.inclusion span_le_span_insertPair ⟨ψ, mem_span_of_mem hψT⟩
        from rfl, map_sub, map_zsmul]
    change (ν' ⟨χ, self_mem_span_insertPair⟩ : G → ℂ)
      - (d : ℤ) • (ν' (Submodule.inclusion span_le_span_insertPair
          ⟨ψ, mem_span_of_mem hψT⟩) : G → ℂ) = _
    rw [hν'χ, hν'T, hα]
  have hν'b : (ν' ⟨χ - star χ, hbmem⟩ : G → ℂ) = tau (χ - star χ) := by
    rw [show (⟨χ - star χ, hbmem⟩ : Submodule.span ℤ (insertPair χ T))
        = ⟨χ, self_mem_span_insertPair⟩ - ⟨star χ, star_self_mem_span_insertPair⟩ from rfl,
      map_sub]
    change (ν' ⟨χ, self_mem_span_insertPair⟩ : G → ℂ)
      - (ν' ⟨star χ, star_self_mem_span_insertPair⟩ : G → ℂ) = _
    rw [hν'χ, hν'star, hc.tau_sub_star χ hχS, sub_neg_eq_add, ← Finset.sum_sdiff (h := hER)]
    ring
  have hν'h : (ν' ⟨h, hhmem⟩ : G → ℂ) = tau h := by
    rw [show (⟨h, hhmem⟩ : Submodule.span ℤ (insertPair χ T))
        = Submodule.inclusion span_le_span_insertPair ⟨h, charSpanZero_le _ hhz⟩ from rfl,
      hν'T,
      show (⟨h, charSpanZero_le _ hhz⟩ : Submodule.span ℤ (T : Set (L → ℂ)))
        = Submodule.inclusion (charSpanZero_le _) ⟨h, hhz⟩ from rfl,
      hν.eq_on_zero ⟨h, hhz⟩, hτT]
  rw [show (Submodule.inclusion (charSpanZero_le (insertPair χ T)) f)
      = m • ⟨χ - (d : ℤ) • ψ, hamem⟩ + m' • ⟨χ - star χ, hbmem⟩ + ⟨h, hhmem⟩
      from Subtype.ext hfeq, map_add, map_add, map_zsmul, map_zsmul]
  change m • (ν' ⟨χ - (d : ℤ) • ψ, hamem⟩ : G → ℂ) + m' • (ν' ⟨χ - star χ, hbmem⟩ : G → ℂ)
    + (ν' ⟨h, hhmem⟩ : G → ℂ) = _
  rw [hν'a, hν'b, hν'h, hfeq]
  have hamemS : χ - (d : ℤ) • ψ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    sub_nsmul_mem_intSpanZeroAtOne hχS hψS hdeg
  have hbmemS : χ - star χ ∈ intSpanZeroAtOne (S : Set (L → ℂ)) := hc.sub_star_mem hχS
  have hhmemS : h ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    mem_intSpanZeroAtOne_of_mem_charSpanZero (by exact_mod_cast hTS) hhz
  rw [hc.map_add _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hamemS)
      (Submodule.smul_mem _ _ hbmemS)) _ hhmemS,
    hc.map_add _ (Submodule.smul_mem _ _ hamemS) _ (Submodule.smul_mem _ _ hbmemS),
    hc.map_zsmul _ hamemS, hc.map_zsmul _ hbmemS]

theorem exists_isCoherentWith_insertPair (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTne : T.Nonempty) (hTstar : ∀ γ ∈ T, star γ ∈ T)
    {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
    {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
    (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    (hψT : ψ ∈ T) (hχS : χ ∈ S) (hχT : χ ∉ T) {d : ℕ} (hd : 1 ≤ d)
    (hdeg : χ 1 = (d : ℂ) * ψ 1)
    (hFeit : 2 * χ 1 * ψ 1 < ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ) :
    ∃ ν' : Submodule.span ℤ (insertPair χ T) →+ virtualChars G,
      IsCoherentWith (insertPair χ T) (subTauHom hc (insertPair_subset hc hTS hχS)) ν' ∧
      (∀ f : Submodule.span ℤ (T : Set (L → ℂ)),
        (ν' (Submodule.inclusion span_le_span_insertPair f) : G → ℂ) = (ν f : G → ℂ)) ∧
      ∃ E ⊆ R χ,
        (ν' ⟨χ, self_mem_span_insertPair⟩ : G → ℂ) = ∑ r ∈ E, r ∧
        (ν' ⟨star χ, star_self_mem_span_insertPair⟩ : G → ℂ) = -∑ r ∈ R χ \ E, r := by
  classical
  obtain ⟨nχ, -, hnχ⟩ := exists_pos_nat_cfInner_self_of_mem hc hχS
  obtain ⟨a, ha, ha01, hsub⟩ :=
    exists_int_coeff_and_proj_sub_eq hc hTS hTstar hν hτT hψT hχS hχT hd hdeg hFeit
  set E : Finset (G → ℂ) := (R χ).filter (fun r => a r = 1) with hE
  have hER : E ⊆ R χ := Finset.filter_subset _ _
  have hproj : ∑ r ∈ R χ, ((a r : ℂ)) • r = ∑ r ∈ E, r := by
    rw [hE, ← Finset.sum_filter_add_sum_filter_not (R χ) (fun r => a r = 1)]
    rw [show ∑ r ∈ (R χ).filter (fun r => a r = 1), ((a r : ℂ)) • r
          = ∑ r ∈ (R χ).filter (fun r => a r = 1), r from
        Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.1 hr).2]; simp,
      show ∑ r ∈ (R χ).filter (fun r => ¬ a r = 1), ((a r : ℂ)) • r = 0 from
        Finset.sum_eq_zero fun r hr => by
          rw [(ha01 r (Finset.mem_filter.1 hr).1).resolve_right (Finset.mem_filter.1 hr).2]
          simp,
      add_zero]
  have hsuma : ((∑ r ∈ R χ, a r : ℤ) : ℂ) = (nχ : ℂ) := by
    rw [← sum_cfInner_eq_intCast ha, ← cfInner_sum_right]
    have hstarχS : star χ ∈ S := hc.star_mem χ hχS
    have hχstar : χ ≠ star χ := Ne.symm (hc.star_ne χ hχS)
    have hstarχT : star χ ∉ T := fun h => hχT (by simpa using hTstar _ h)
    have hχψ : χ ≠ ψ := fun h => hχT (h ▸ hψT)
    rw [← hc.tau_sub_star χ hχS,
      cfInner_tau_tau hc (sub_nsmul_mem_intSpanZeroAtOne hχS (hTS hψT) hdeg)
        (hc.sub_star_mem hχS),
      cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_zsmul_left,
      cfInner_zsmul_left, cfInner_eq_zero_of_ne hc hχS hstarχS hχstar,
      cfInner_eq_zero_of_ne hc (hTS hψT) hχS (Ne.symm hχψ),
      cfInner_eq_zero_of_ne hc (hTS hψT) hstarχS (fun h => hstarχT (h ▸ hψT)), hnχ]
    ring
  have hEcard : E.card = nχ := by
    have hint : (∑ r ∈ R χ, a r) = (E.card : ℤ) := by
      rw [hE, ← Finset.sum_filter_add_sum_filter_not (R χ) (fun r => a r = 1),
        Finset.sum_congr rfl (fun r hr => (Finset.mem_filter.1 hr).2),
        Finset.sum_eq_zero (fun r hr =>
          (ha01 r (Finset.mem_filter.1 hr).1).resolve_right (Finset.mem_filter.1 hr).2),
        add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hint] at hsuma
    exact_mod_cast hsuma
  have hα : tau (χ - (d : ℤ) • ψ)
      = (∑ r ∈ E, r) - (d : ℤ) • (ν ⟨ψ, mem_span_of_mem hψT⟩ : G → ℂ) := by
    rw [← hproj] at *
    rw [← hsub]
    ring
  obtain ⟨ν', hν', hres, hχval, hstarval⟩ :=
    exists_isCoherentWith_of_tau_eq hc hTS hTstar hν hτT hψT hχS hχT hdeg hnχ hER hEcard hα
  exact ⟨ν', hν', hres, E, hER, hχval, hstarval⟩

theorem isCoherent_insertPair (hc : IsSubcoherent S tau R) (hTS : T ⊆ S)
    (hTne : T.Nonempty) (hTstar : ∀ γ ∈ T, star γ ∈ T)
    {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
    {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}
    (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    (hψT : ψ ∈ T) (hχS : χ ∈ S) (hχT : χ ∉ T) {d : ℕ} (hd : 1 ≤ d)
    (hdeg : χ 1 = (d : ℂ) * ψ 1)
    (hFeit : 2 * χ 1 * ψ 1 < ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ) :
    IsCoherent (insertPair χ T) (subTauHom hc (insertPair_subset hc hTS hχS)) := by
  obtain ⟨ν', hν', -, -⟩ :=
    exists_isCoherentWith_insertPair hc hTS hTne hTstar hν hτT hψT hχS hχT hd hdeg hFeit
  exact hν'.isCoherent

end WeightedFeitExtension

end CFSG.FeitThompson
