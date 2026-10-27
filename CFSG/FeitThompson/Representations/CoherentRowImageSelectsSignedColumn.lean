module

public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
public import CFSG.FeitThompson.Representations.CoreCoherentIrreducibleArrayOrthogonality
import CFSG.FeitThompson.Representations.IntegralOrthonormalBlockProjection
import CFSG.FeitThompson.Representations.CyclicTIIsometryUnique
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace IsCyclicTIPair

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G}

omit [Fintype G] [Fintype ↥W] in
theorem sum_signedTwoColumn (hW : IsCyclicTIPair W W1 W2) (δ : ℂ) (j k : Irr ↥W2)
    [Fintype ↑(Irr ↥W1)] :
    ∑ p : Irr ↥W1 × Bool, hW.signedTwoColumn ω δ j k p
      = δ • hW.prodCharEtaColSum ω j - δ • hW.prodCharEtaColSum ω k := by
  have key : ∀ i : Irr ↥W1, (∑ b : Bool, hW.signedTwoColumn ω δ j k (i, b))
      = δ • hW.prodCharEta ω i j - δ • hW.prodCharEta ω i k := by
    intro i
    rw [Fintype.sum_bool, signedTwoColumn_apply_true, signedTwoColumn_apply_false, neg_smul,
      sub_eq_add_neg]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => key i),
    Finset.sum_sub_distrib, hW.prodCharEtaColSum_eq_sum, hW.prodCharEtaColSum_eq_sum,
    Finset.smul_sum, Finset.smul_sum]

open scoped Classical in
theorem cfInner_signedTwoColumn_signedTwoColumn (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) {j k : Irr ↥W2}
    (hjk : j ≠ k) (p q : Irr ↥W1 × Bool) :
    cfInner (hW.signedTwoColumn ω δ j k p) (hW.signedTwoColumn ω δ j k q) =
      if p = q then 1 else 0 := by
  have hconj : (starRingEnd ℂ) δ = δ := by rcases hδ with rfl | rfl <;> simp
  have hsq : δ * δ = 1 := by rcases hδ with rfl | rfl <;> ring
  obtain ⟨i, b⟩ := p
  obtain ⟨i', b'⟩ := q
  have hij : ∀ (l m : Irr ↥W2), cfInner (hW.prodCharEta ω i l) (hW.prodCharEta ω i' m)
      = if i = i' ∧ l = m then 1 else 0 := fun l m => hW.cfInner_prodCharEta hω i i' l m
  cases b <;> cases b'
  ·
    rw [signedTwoColumn_apply_false, signedTwoColumn_apply_false, cfInner_smul_left,
      cfInner_smul_right, map_neg, hconj, hij, if_congr (and_iff_left rfl) rfl rfl,
      if_congr (show ((i, false) = (i', false)) ↔ i = i' by simp) rfl rfl]
    by_cases h : i = i' <;> simp [h, hsq]
  ·
    rw [signedTwoColumn_apply_false, signedTwoColumn_apply_true, cfInner_smul_left,
      cfInner_smul_right, hconj, hij, if_neg (fun h => hjk h.2.symm),
      if_neg (show ¬((i, false) = (i', true)) by simp)]
    ring
  ·
    rw [signedTwoColumn_apply_true, signedTwoColumn_apply_false, cfInner_smul_left,
      cfInner_smul_right, map_neg, hconj, hij, if_neg (fun h => hjk h.2),
      if_neg (show ¬((i, true) = (i', false)) by simp)]
    ring
  ·
    rw [signedTwoColumn_apply_true, signedTwoColumn_apply_true, cfInner_smul_left,
      cfInner_smul_right, hconj, hij, if_congr (and_iff_left rfl) rfl rfl,
      if_congr (show ((i, true) = (i', true)) ↔ i = i' by simp) rfl rfl]
    by_cases h : i = i' <;> simp [h, hsq]

theorem signedTwoColumn_mem_span_Irr (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) (j k : Irr ↥W2)
    (p : Irr ↥W1 × Bool) : hW.signedTwoColumn ω δ j k p ∈ Submodule.span ℤ (Irr G) := by
  obtain ⟨i, b⟩ := p
  have hj : hW.prodCharEta ω i j ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_signedIrr (hW.prodCharEta_mem_signedIrr hω i j)
  have hk : hW.prodCharEta ω i k ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_signedIrr (hW.prodCharEta_mem_signedIrr hω i k)
  rcases hδ with rfl | rfl <;> cases b <;>
    simp only [signedTwoColumn_apply_true, signedTwoColumn_apply_false, one_smul, neg_neg,
      neg_one_smul] <;>
    first
      | exact hj
      | exact hk
      | exact neg_mem hj
      | exact neg_mem hk

open scoped Classical in
theorem eq_signed_prodCharEtaColSum_of_cfInner_eq (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) {j k : Irr ↥W2}
    (hjk : j ≠ k) {φ : G → ℂ} (hφ : φ ∈ Submodule.span ℤ (Irr G))
    (hnorm : cfInner φ φ = (Nat.card ↥W1 : ℂ))
    (hpair : cfInner φ (δ • hW.prodCharEtaColSum ω j - δ • hW.prodCharEtaColSum ω k)
      = (Nat.card ↥W1 : ℂ))
    (hV : ∀ v ∈ cyclicTIDiff W W1 W2, φ v = 0) :
    φ = δ • hW.prodCharEtaColSum ω j ∨ φ = (-δ) • hW.prodCharEtaColSum ω k := by
  have := hW.finite_left
  have : Fintype ↑(Irr ↥W1) := Fintype.ofFinite _
  rw [← hW.sum_signedTwoColumn δ j k] at hpair
  have hδ0 : δ ≠ 0 := by rcases hδ with rfl | rfl <;> norm_num
  have hinj : Function.Injective (hW.signedTwoColumn ω δ j k) :=
    hW.signedTwoColumn_injective hω hδ0 hjk
  set R : Finset (G → ℂ) := Finset.univ.image (hW.signedTwoColumn ω δ j k) with hR
  have hmemR : ∀ r ∈ R, ∃ p : Irr ↥W1 × Bool, hW.signedTwoColumn ω δ j k p = r := by
    intro r hr
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hr
    exact ⟨p, hp⟩
  have hone : ∀ r ∈ R, cfInner r r = 1 := by
    intro r hr
    obtain ⟨p, rfl⟩ := hmemR r hr
    simpa using hW.cfInner_signedTwoColumn_signedTwoColumn hω hδ hjk p p
  have hzero : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → cfInner r s = 0 := by
    intro r hr s hs hrs
    obtain ⟨p, rfl⟩ := hmemR r hr
    obtain ⟨q, rfl⟩ := hmemR s hs
    have hpq : p ≠ q := fun h => hrs (by rw [h])
    simpa [hpq] using hW.cfInner_signedTwoColumn_signedTwoColumn hω hδ hjk p q
  have hRZ : ↑R ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) := by
    intro r hr
    obtain ⟨p, rfl⟩ := hmemR r hr
    exact hW.signedTwoColumn_mem_span_Irr hω hδ j k p
  obtain ⟨a, ha⟩ := IntegralBlockProjection.exists_int_cfInner_forall_mem hRZ hφ
  have hsumR : ∑ r ∈ R, cfInner φ r = (Nat.card ↥W1 : ℂ) := by
    rw [hR, Finset.sum_image fun p _ q _ h => hinj h, ← cfInner_sum_right]
    exact hpair
  have hqI : ∑ r ∈ R, a r = (Nat.card ↥W1 : ℤ) := by
    have hcast : ((∑ r ∈ R, a r : ℤ) : ℂ) = ((Nat.card ↥W1 : ℤ) : ℂ) := by
      rw [← IntegralBlockProjection.sum_cfInner_eq_intCast ha, hsumR]
      push_cast
      ring
    exact_mod_cast hcast
  have hn : cfInner φ φ = ((∑ r ∈ R, a r : ℤ) : ℂ) := by
    rw [hqI, hnorm]
    push_cast
    ring
  obtain ⟨h01, hφP⟩ :=
    IntegralBlockProjection.eq_sum_cfInner_smul_of_cfInner_self_eq hone hzero ha hn
  obtain ⟨T0, hT0R, hcardT0, hPT0⟩ :=
    IntegralBlockProjection.exists_subset_sum_cfInner_smul_eq ha h01
  have hφT0 : φ = ∑ t ∈ T0, t := by rw [hφP, hPT0]
  have hcard : T0.card = Nat.card ↑(Irr ↥W1) := by
    have hcast : (T0.card : ℤ) = (Nat.card ↥W1 : ℤ) := by rw [hcardT0, hqI]
    rw [hW.card_Irr_left]
    exact_mod_cast hcast
  have hsub : (T0 : Set (G → ℂ)) ⊆ Set.range (hW.signedTwoColumn ω δ j k) := by
    intro t ht
    obtain ⟨p, rfl⟩ := hmemR t (hT0R ht)
    exact ⟨p, rfl⟩
  have hQ0 : ∀ x ∈ cyclicTIDiff W W1 W2, (∑ t ∈ T0, t) x = 0 := by
    intro x hx
    rw [← hφT0]
    exact hV x hx
  rw [hφT0]
  exact hW.eq_col_sum_of_card_eq_of_vanishing_on_cyclicTIDiff hω hδ hjk hsub hcard hQ0

end IsCyclicTIPair

namespace CoherentRowColumn

variable {G : Type*} [Group G] {L : Subgroup G} {A0 : Set G}
  {T : G → Subgroup G} {S : Set (↥L → ℂ)}
  {ν : Submodule.span ℤ S →+ virtualChars G}

theorem coe_nu_sub {M M' : ↥L → ℂ} (hMS : M ∈ S) (hM'S : M' ∈ S) :
    (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ) - (ν ⟨M', Submodule.subset_span hM'S⟩ : G → ℂ)
      = (ν ⟨M - M', sub_mem (Submodule.subset_span hMS)
          (Submodule.subset_span hM'S)⟩ : G → ℂ) := by
  have hsplit : (⟨M - M', sub_mem (Submodule.subset_span hMS) (Submodule.subset_span hM'S)⟩ :
        Submodule.span ℤ S)
      = ⟨M, Submodule.subset_span hMS⟩ - ⟨M', Submodule.subset_span hM'S⟩ := Subtype.ext rfl
  rw [hsplit, map_sub]
  rfl

theorem nu_apply_eq_zero_of_apply_eq_zero [Finite G] (hD : IsDadeData L A0 T)
    (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hScf : ∀ χ ∈ S, χ ∈ classFun ↥L)
    (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A0 → (f : ↥L → ℂ) x = 0)
    {M ξ : ↥L → ℂ} (hMS : M ∈ S) (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L)
    {a b : ℤ} (ha : ξ 1 = (a : ℂ)) (hb : M 1 = (b : ℂ))
    {v : G} (hvA : v ∈ A0) (hvL : v ∈ L)
    (hMv : M (⟨v, hvL⟩ : ↥L) = 0) (hξv : ξ (⟨v, hvL⟩ : ↥L) = 0)
    (hξV : (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) v = 0) :
    (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ) v = 0 := by
  have hfmem : a • M - b • ξ ∈ Submodule.span ℤ S :=
    sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span hMS))
      (Submodule.smul_mem _ _ (Submodule.subset_span hξS))
  have hf1 : (a • M - b • ξ) 1 = 0 := by
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul, ha, hb]
    ring
  have hfz : a • M - b • ξ ∈ charSpanZero S := mem_charSpanZero.2 ⟨hfmem, hf1⟩
  have hfcf : a • M - b • ξ ∈ classFun ↥L :=
    sub_mem (Submodule.smul_of_tower_mem _ _ (hScf _ hMS))
      (Submodule.smul_of_tower_mem _ _ (hScf _ hξS))
  have hfdom : a • M - b • ξ ∈ dadeDomain L A0 :=
    mem_dadeDomain.2 ⟨hfcf, fun z hz => hS0 ⟨_, hfz⟩ z hz⟩
  have hval : (ν ⟨a • M - b • ξ, hfmem⟩ : G → ℂ) v = 0 := by
    rw [hντ ⟨a • M - b • ξ, hfmem⟩ ⟨a • M - b • ξ, hfdom⟩ rfl,
      dadeMap_apply_mem hD ⟨a • M - b • ξ, hfdom⟩ hvA]
    have hveq : (⟨v, hD.mem_of_mem hvA⟩ : ↥L) = ⟨v, hvL⟩ := rfl
    change (a • M - b • ξ) (⟨v, hD.mem_of_mem hvA⟩ : ↥L) = 0
    rw [hveq, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul, hMv, hξv]
    ring
  have hsplit : (⟨a • M - b • ξ, hfmem⟩ : Submodule.span ℤ S)
      = a • (⟨M, Submodule.subset_span hMS⟩ : Submodule.span ℤ S)
        - b • (⟨ξ, Submodule.subset_span hξS⟩ : Submodule.span ℤ S) := Subtype.ext rfl
  rw [hsplit, map_sub, map_zsmul, map_zsmul] at hval
  have hval2 : (a : ℂ) * (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ) v = 0 := by
    have h := hval
    rw [Submodule.coe_sub, SetLike.val_smul, SetLike.val_smul, Pi.sub_apply, Pi.smul_apply,
      Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul, hξV, mul_zero, sub_zero] at h
    exact h
  have hane : (a : ℂ) ≠ 0 := by
    rw [← ha]
    exact apply_one_ne_zero_of_mem_Irr hξIrr
  exact (mul_eq_zero.1 hval2).resolve_left hane

variable [Fintype G] [Fintype ↥L] {τ : charSpanZero S →+ virtualChars G}
  {K : Subgroup ↥L} [K.Normal] {H : Subgroup ↥K} {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G}

theorem cfInner_nu_nu_sub (hν : IsCoherentWith S τ ν) {M M' : ↥L → ℂ} (hMS : M ∈ S)
    (hM'S : M' ∈ S) {q : ℂ} (hnorm : cfInner M M = q) (horth : cfInner M M' = 0) :
    cfInner (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ)
      ((ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ)
        - (ν ⟨M', Submodule.subset_span hM'S⟩ : G → ℂ)) = q := by
  rw [coe_nu_sub hMS hM'S, hν.inner_eq]
  change cfInner M (M - M') = q
  rw [cfInner_sub_right, hnorm, horth, sub_zero]

theorem nu_apply_eq_zero_of_mem_cyclicTIDiff (hodd : Odd (Nat.card G))
    (hW : IsCyclicTIPair W W1 W2) (hW2 : W2 ≤ K.map L.subtype)
    (hW1 : W1 ⊓ K.map L.subtype = ⊥) (hω : IsCyclicTIIsometry W W1 W2 ω)
    (hD : IsDadeData L A0 T) (hVA : cyclicTIDiff W W1 W2 ⊆ A0) (hS : S ⊆ indFamDetect K H)
    (hSstar : ∀ χ ∈ S, star χ ∈ S)
    (hνiso : ∀ f h : Submodule.span ℤ S,
      cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
    (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A0 → (f : ↥L → ℂ) x = 0)
    (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {M ξ : ↥L → ℂ} (hMS : M ∈ S) (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L)
    {a b : ℤ} (ha : ξ 1 = (a : ℂ)) (hb : M 1 = (b : ℂ))
    {v : G} (hv : v ∈ cyclicTIDiff W W1 W2) :
    (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ) v = 0 := by
  have hvA : v ∈ A0 := hVA hv
  have hvL : v ∈ L := hD.mem_of_mem hvA
  have hvK : (⟨v, hvL⟩ : ↥L) ∉ K := fun hc =>
    notMem_map_of_mem_cyclicTIDiff hW hW2 hW1 hv ⟨⟨v, hvL⟩, hc, rfl⟩
  refine nu_apply_eq_zero_of_apply_eq_zero hD hντ
    (fun χ hχ => mem_classFun_of_mem_span_indFamDetect hS (Submodule.subset_span hχ)) hS0
    hMS hξS hξIrr ha hb hvA hvL
    (apply_eq_zero_of_mem_span_indFamDetect hS (Submodule.subset_span hMS) hvK)
    (apply_eq_zero_of_mem_span_indFamDetect hS (Submodule.subset_span hξS) hvK) ?_
  exact CoherentCore.nu_apply_eq_zero_of_mem_cyclicTIDiff hodd hW hW2 hW1 hω hD hVA hS hSstar
    hνiso hS0 hντ hξS hξIrr hv

theorem eq_signed_col_or_neg_signed_col (hodd : Odd (Nat.card G))
    (hW : IsCyclicTIPair W W1 W2) (hW2 : W2 ≤ K.map L.subtype)
    (hW1 : W1 ⊓ K.map L.subtype = ⊥) (hω : IsCyclicTIIsometry W W1 W2 ω)
    (hD : IsDadeData L A0 T) (hVA : cyclicTIDiff W W1 W2 ⊆ A0) (hS : S ⊆ indFamDetect K H)
    (hSstar : ∀ χ ∈ S, star χ ∈ S)
    (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A0 → (f : ↥L → ℂ) x = 0)
    (hν : IsCoherentWith S τ ν)
    (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {M M' ξ : ↥L → ℂ} (hMS : M ∈ S) (hM'S : M' ∈ S) (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L)
    {a b : ℤ} (ha : ξ 1 = (a : ℂ)) (hb : M 1 = (b : ℂ))
    (hnorm : cfInner M M = (Nat.card ↥W1 : ℂ)) (horth : cfInner M M' = 0)
    {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) {j k : Irr ↥W2} (hjk : j ≠ k)
    (htau : (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ)
        - (ν ⟨M', Submodule.subset_span hM'S⟩ : G → ℂ)
      = δ • hW.prodCharEtaColSum ω j - δ • hW.prodCharEtaColSum ω k) :
    (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ) = δ • hW.prodCharEtaColSum ω j ∨
      (ν ⟨M, Submodule.subset_span hMS⟩ : G → ℂ) = (-δ) • hW.prodCharEtaColSum ω k := by
  refine hW.eq_signed_prodCharEtaColSum_of_cfInner_eq hω hδ hjk
    (mem_span_Irr_of_mem_virtualChars (ν _).2) ?_ ?_ ?_
  · rw [hν.inner_eq]
    exact hnorm
  · rw [← htau]
    exact cfInner_nu_nu_sub hν hMS hM'S hnorm horth
  · intro v hv
    exact nu_apply_eq_zero_of_mem_cyclicTIDiff hodd hW hW2 hW1 hω hD hVA hS hSstar
      hν.inner_eq hS0 hντ hMS hξS hξIrr ha hb hv

end CoherentRowColumn

end CFSG.FeitThompson

end
