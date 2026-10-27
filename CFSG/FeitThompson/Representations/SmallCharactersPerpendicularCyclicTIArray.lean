module

public import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.NonrealPairArrayOrthogonality
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset
open scoped ComplexConjugate ComplexOrder

variable {G : Type*} [Group G] [Fintype G]

theorem cfInner_eq_zero_of_add_swap_of_cfInner_self_re_lt_min {ι κ : Type*} [Finite ι] [Finite κ]
    [DecidableEq ι] [DecidableEq κ] {η : ι × κ → G → ℂ} {f : G → ℂ}
    (hηmem : ∀ p, η p ∈ Submodule.span ℤ (Irr G))
    (hη : ∀ p q, cfInner (η p) (η q) = if p = q then 1 else 0)
    (hf : f ∈ Submodule.span ℤ (Irr G))
    (hrect : ∀ i k : ι, ∀ j l : κ, cfInner f (η (i, j)) + cfInner f (η (k, l))
      = cfInner f (η (i, l)) + cfInner f (η (k, j)))
    (hnorm : (cfInner f f).re < min (Nat.card ι) (Nat.card κ)) :
    ∀ p, cfInner f (η p) = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite _
  have : Fintype κ := Fintype.ofFinite _
  choose a ha using fun p => exists_int_cfInner_of_mem_span_Irr hf (hηmem p)
  by_contra hcon
  push Not at hcon
  obtain ⟨p₀, hp₀⟩ := hcon
  set A : ι → κ → ℂ := fun i j => cfInner f (η (i, j)) with hA
  have hAne : ∃ i j, A i j ≠ 0 := ⟨p₀.1, p₀.2, hp₀⟩
  have hcard : min (Nat.card ι) (Nat.card κ) ≤ {p : ι × κ | A p.1 p.2 ≠ 0}.ncard :=
    min_le_ncard_support_of_add_swap A hrect hAne
  have hcard' : min (Nat.card ι) (Nat.card κ) ≤ #{p : ι × κ | A p.1 p.2 ≠ 0} := by
    rwa [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] at hcard
  have hone : ∀ p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), (1 : ℝ) ≤ ‖cfInner f (η p)‖ ^ 2 := by
    intro p hp
    have hp' : cfInner f (η p) ≠ 0 := by simpa [hA] using hp
    have hane : a p ≠ 0 := by
      intro h
      rw [ha p, h] at hp'
      simp at hp'
    have h1 : (1 : ℝ) ≤ ‖cfInner f (η p)‖ := by
      rw [ha p, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hane
    nlinarith [norm_nonneg (cfInner f (η p))]
  have h1 : ((#{p : ι × κ | A p.1 p.2 ≠ 0} : ℕ) : ℝ)
      ≤ ∑ p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), ‖cfInner f (η p)‖ ^ 2 := by
    calc ((#{p : ι × κ | A p.1 p.2 ≠ 0} : ℕ) : ℝ)
        = ∑ _p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum hone
  have h2 : ∑ p ∈ ({p : ι × κ | A p.1 p.2 ≠ 0} : Finset _), ‖cfInner f (η p)‖ ^ 2
      ≤ ∑ p : ι × κ, ‖cfInner f (η p)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  have h3 : ∑ p : ι × κ, ‖cfInner f (η p)‖ ^ 2 ≤ (cfInner f f).re :=
    sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hη f
  have h4 : ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ)
      ≤ ((#{p : ι × κ | A p.1 p.2 ≠ 0} : ℕ) : ℝ) := by exact_mod_cast hcard'
  have hlt : ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ)
      < ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ) := by
    calc ((min (Nat.card ι) (Nat.card κ) : ℕ) : ℝ) ≤ _ := h4
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ _ := h3
      _ < _ := hnorm
  simp at hlt

variable {W W1 W2 : Subgroup G} [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIPair

omit [Fintype G] [Fintype ↥W] in
theorem exists_apply_eq_prodCharEta (hW : IsCyclicTIPair W W1 W2) {χ : classFun ↥W}
    (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) :
    ∃ i : Irr ↥W1, ∃ j : Irr ↥W2, (σ χ : G → ℂ) = hW.prodCharEta σ i j := by
  obtain ⟨lam, hlam, mu, hmu, he⟩ := hW.exists_prodChar_eq_of_mem_Irr hχ
  refine ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, ?_⟩
  have hb : hW.basisProdIrr (⟨lam, hlam⟩, ⟨mu, hmu⟩) = χ :=
    Subtype.ext (by rw [coe_basisProdIrr_apply, he])
  rw [prodCharEta_eq_coe_apply, hb]

theorem apply_mem_signedIrr (hσ : IsCyclicTIIsometry W W1 W2 σ) {χ : classFun ↥W}
    (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) : (σ χ : G → ℂ) ∈ signedIrr G := by
  refine mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
    (virtualChars_le_span_Irr (hσ.map_virtualChars χ (Irr_subset_virtualChars hχ))) ?_
  rw [hσ.inner_eq, cfInner_eq_ite_of_mem_Irr hχ hχ, if_pos rfl]

open scoped Classical in
theorem cfInner_prodCharEta_prod (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (p q : Irr ↥W1 × Irr ↥W2) :
    cfInner (hW.prodCharEta σ p.1 p.2) (hW.prodCharEta σ q.1 q.2) = if p = q then 1 else 0 := by
  rw [hW.cfInner_prodCharEta hσ]
  exact if_congr Prod.ext_iff.symm rfl rfl

theorem cfInner_prodCharEta_eq_zero_of_cfInner_self_lt_min (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    (hf0 : ∀ x ∈ cyclicTIDiff W W1 W2, f x = 0)
    (hnorm : cfInner f f < ((min (Nat.card ↥W1) (Nat.card ↥W2) : ℕ) : ℂ))
    (i : Irr ↥W1) (j : Irr ↥W2) : cfInner f (hW.prodCharEta σ i j) = 0 := by
  classical
  have hfin1 : Finite ↥W1 := hW.finite_left
  have hfin2 : Finite ↥W2 := hW.finite_right
  set η : Irr ↥W1 × Irr ↥W2 → G → ℂ := fun p => hW.prodCharEta σ p.1 p.2 with hη
  have hηmem : ∀ p, η p ∈ Submodule.span ℤ (Irr G) := fun p =>
    virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hσ p.1 p.2)
  have hηorth : ∀ p q, cfInner (η p) (η q) = if p = q then 1 else 0 := fun p q =>
    hW.cfInner_prodCharEta_prod hσ p q
  have hexch := fun i' j' =>
    hW.cfInner_prodCharEta_exchange hσ (mem_classFun_of_mem_span_Irr hf) hf0 i' j'
  have hrect : ∀ i' k : Irr ↥W1, ∀ j' l : Irr ↥W2,
      cfInner f (η (i', j')) + cfInner f (η (k, l))
        = cfInner f (η (i', l)) + cfInner f (η (k, j')) := by
    intro i' k j' l
    simp only [hη]
    linear_combination (hexch i' j') + (hexch k l) - (hexch i' l) - (hexch k j')
  have hre : (cfInner f f).re < min (Nat.card (Irr ↥W1)) (Nat.card (Irr ↥W2)) := by
    rw [hW.card_Irr_left, hW.card_Irr_right]
    simpa using (Complex.lt_def.1 hnorm).1
  exact cfInner_eq_zero_of_add_swap_of_cfInner_self_re_lt_min hηmem hηorth hf hrect hre (i, j)

theorem isOrthogonal_apply_of_cfInner_self_lt_min (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {f : G → ℂ} (hf : f ∈ virtualChars G)
    (hf0 : ∀ x ∈ cyclicTIDiff W W1 W2, f x = 0)
    (hnorm : cfInner f f < ((min (Nat.card ↥W1) (Nat.card ↥W2) : ℕ) : ℂ))
    {χ : classFun ↥W} (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) : IsOrthogonal f (σ χ : G → ℂ) := by
  obtain ⟨i, j, hij⟩ := hW.exists_apply_eq_prodCharEta (σ := σ) hχ
  rw [isOrthogonal_iff, hij]
  exact hW.cfInner_prodCharEta_eq_zero_of_cfInner_self_lt_min hσ
    (virtualChars_le_span_Irr hf) hf0 hnorm i j

theorem isOrthogonal_apply_of_ne_conj (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {ρ : G → ℂ} (hρ : ρ ∈ signedIrr G)
    (hρr : ρ ≠ fun x => conj (ρ x))
    (hρ0 : ∀ x ∈ cyclicTIDiff W W1 W2, (ρ - fun y => conj (ρ y)) x = 0)
    {χ : classFun ↥W} (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) : IsOrthogonal ρ (σ χ : G → ℂ) := by
  have hcmem : (fun x => conj (ρ x)) ∈ signedIrr G := conj_mem_signedIrr hρ
  set d : G → ℂ := ρ - fun x => conj (ρ x) with hd
  have hdmem : d ∈ Submodule.span ℤ (Irr G) :=
    Submodule.sub_mem _ (signedIrr_subset_span_Irr hρ) (signedIrr_subset_span_Irr hcmem)
  have h3 : 3 ≤ min (Nat.card ↥W1) (Nat.card ↥W2) :=
    le_min hW.three_le_natCard_left hW.three_le_natCard_right
  have hlt : cfInner d d < ((min (Nat.card ↥W1) (Nat.card ↥W2) : ℕ) : ℂ) := by
    rw [hd, cfInner_self_sub_conj_of_mem_signedIrr hρ hρr, Complex.lt_def]
    have h3' : (3 : ℝ) ≤ ((min (Nat.card ↥W1) (Nat.card ↥W2) : ℕ) : ℝ) := by exact_mod_cast h3
    refine ⟨?_, ?_⟩
    · simp only [Complex.re_ofNat, Complex.natCast_re]
      linarith
    · simp
  obtain ⟨i, j, hij⟩ := hW.exists_apply_eq_prodCharEta (σ := σ) hχ
  have hηsigned : hW.prodCharEta σ i j ∈ signedIrr G := hij ▸ apply_mem_signedIrr hσ hχ
  have hzero : cfInner d (hW.prodCharEta σ i j) = 0 :=
    hW.cfInner_prodCharEta_eq_zero_of_cfInner_self_lt_min hσ hdmem hρ0 hlt i j
  rw [isOrthogonal_iff, hij]
  exact cfInner_eq_zero_of_cfInner_sub_conj_eq_zero hρ hρr hηsigned hzero

end IsCyclicTIPair

end CFSG.FeitThompson
