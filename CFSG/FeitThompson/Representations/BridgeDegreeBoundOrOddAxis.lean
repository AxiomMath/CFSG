module

public import CFSG.FeitThompson.Representations.DadeBetaProjectionIntegralParameter
public import CFSG.FeitThompson.Representations.DadeRealCorrectedCharacter
import CFSG.FeitThompson.Representations.CrossedBridgeCoefficientKernelBound
import CFSG.FeitThompson.Representations.DadeIntegerParameterNormBounds
import CFSG.FeitThompson.Representations.BridgeCrossedCoefficientsOppositeParity
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace DadeBridgeParity

open scoped ComplexConjugate
open CrossFamilyProjection (coherentImage coherentImage_apply)
open NormalInducedFamily
open NormalInducedWeightedNorm (weightedCoherentSum weightedCoherentSum_apply)

section Axis

variable {G : Type*} [Fintype G] {p j : ℕ} {Θ : ℕ → G → ℂ}

theorem card_sub_one_mul_norm_sq_le {f : G → ℂ} (hp : 0 < p)
    (hΘ : IsOrthonormalFamily fun i : Fin p => Θ (i : ℕ)) {b : ℂ}
    (hb : ∀ j, 0 < j → j < p → cfInner f (Θ j) = b) :
    ((p : ℝ) - 1) * ‖b‖ ^ 2 ≤ (cfInner f f).re := by
  classical
  set v : Fin (p - 1) → G → ℂ := fun i => Θ ((i : ℕ) + 1) with hv
  have hlt : ∀ i : Fin (p - 1), (i : ℕ) + 1 < p := fun i => by omega
  have hvite : ∀ i i' : Fin (p - 1), cfInner (v i) (v i') = if i = i' then 1 else 0 := by
    intro i i'
    have h := hΘ.cfInner_eq_ite (⟨(i : ℕ) + 1, hlt i⟩ : Fin p) ⟨(i' : ℕ) + 1, hlt i'⟩
    simp only [hv]
    rw [h]
    congr 1
    simp [Fin.ext_iff]
  have hbessel := sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hvite f
  have hterm : ∀ i : Fin (p - 1), ‖cfInner f (v i)‖ ^ 2 = ‖b‖ ^ 2 := fun i => by
    rw [hv, hb _ (Nat.succ_pos _) (hlt i)]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hbessel
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by push_cast [Nat.cast_sub hp]; ring
  rwa [hcast] at hbessel

theorem cfInner_axis_one (hΘ : IsOrthonormalFamily fun i : Fin p => Θ (i : ℕ))
    (hΘ0 : Θ 0 = (1 : G → ℂ)) (hp : 0 < p) (hjp : j < p) (hj0 : j ≠ 0) :
    cfInner (Θ j) (1 : G → ℂ) = 0 := by
  have h := hΘ.cfInner_eq_ite (⟨j, hjp⟩ : Fin p) ⟨0, hp⟩
  rw [hΘ0] at h
  simpa [Fin.ext_iff, hj0] using h

theorem cfInner_one_axis (hΘ : IsOrthonormalFamily fun i : Fin p => Θ (i : ℕ))
    (hΘ0 : Θ 0 = (1 : G → ℂ)) (hp : 0 < p) (hjp : j < p) (hj0 : j ≠ 0) :
    cfInner (1 : G → ℂ) (Θ j) = 0 := by
  have h := hΘ.cfInner_eq_ite (⟨0, hp⟩ : Fin p) ⟨j, hjp⟩
  rw [hΘ0] at h
  simpa [Fin.ext_iff, Ne.symm hj0] using h

theorem axis_mem_signedIrr [Group G] (hΘ : IsOrthonormalFamily fun i : Fin p => Θ (i : ℕ))
    (hΘmem : ∀ i < p, Θ i ∈ Submodule.span ℤ (Irr G)) (hjp : j < p) : Θ j ∈ signedIrr G := by
  refine mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one (hΘmem j hjp) ?_
  simpa [Fin.ext_iff] using hΘ.cfInner_self (⟨j, hjp⟩ : Fin p)

end Axis

section Delta

variable {G : Type*} [Group G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} {ι : Type*} {ξ : ι → (↥L → ℂ)}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

noncomputable def bridgeDelta (A : Set G) (R : G → Subgroup G) (H : Subgroup ↥L)
    (ξ : ι → (↥L → ℂ)) (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) :
    G → ℂ :=
  dadeDelta A R H ν (Set.mem_range_self k₀) - 1

theorem bridgeDelta_eq :
    bridgeDelta A R H ξ ν k₀ = dadeDelta A R H ν (Set.mem_range_self k₀) - 1 := (rfl)

theorem dadeBeta_eq_one_sub_add_bridgeDelta :
    dadeBeta A R H (ξ k₀)
      = (1 : G → ℂ) - coherentImage ξ ν k₀ + bridgeDelta A R H ξ ν k₀ := by
  rw [bridgeDelta, dadeDelta_eq, coherentImage_apply]
  abel

variable [Finite G] [H.Normal]
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hζ1 : ξ k₀ 1 = (H.index : ℂ))

include hD hA hS hζ1 in
theorem bridgeDelta_mem_span_Irr :
    bridgeDelta A R H ξ ν k₀ ∈ Submodule.span ℤ (Irr G) :=
  Submodule.sub_mem _
    (mem_span_Irr_of_mem_virtualChars
      (dadeDelta_mem_virtualChars hD hA hS (Set.mem_range_self k₀) hζ1))
    (Submodule.subset_span one_mem_Irr)

variable [Fintype G]
  (hν : ∀ f g : Submodule.span ℤ (Set.range ξ),
    cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ))
  (hντ : ∀ (f : Submodule.span ℤ (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζIrr : ξ k₀ ∈ Irr ↥L)

include hD hA hS hζ1 hν hντ hζIrr in
theorem bridgeDelta_apply_im (hodd : Odd (Nat.card G)) (x : G) :
    (bridgeDelta A R H ξ ν k₀ x).im = 0 := by
  have h := dadeDelta_apply_im hodd hD hA hS hν hντ (Set.mem_range_self k₀) hζIrr hζ1 x
  simp [bridgeDelta, h]

include hD hA hS hζ1 hν hντ hζIrr in
theorem cfInner_bridgeDelta_one (hS2 : (Set.range ξ).Nontrivial) :
    cfInner (bridgeDelta A R H ξ ν k₀) (1 : G → ℂ) = 0 := by
  have h := cfInner_dadeDelta_one hD hA hS hν hντ (Set.mem_range_self k₀) hζIrr hζ1 hS2
  rw [bridgeDelta, cfInner_sub_left, h, cfInner_one_one, sub_self]

end Delta

section Remainder

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} {ι : Type*} [Fintype ι] {ξ : ι → (↥L → ℂ)}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}
  {p j : ℕ} {Θ : ℕ → G → ℂ}

theorem cfInner_weightedCoherentSum_right {f : G → ℂ}
    (hf : ∀ k, cfInner (coherentImage ξ ν k) f = 0) :
    cfInner (weightedCoherentSum ξ ν (H.index : ℂ)) f = 0 := by
  rw [weightedCoherentSum_apply, cfInner_sum_left]
  exact Finset.sum_eq_zero fun k _ => by rw [cfInner_smul_left, hf k, mul_zero]

theorem cfInner_dadeBetaRemainder_axis
    (hΘ : IsOrthonormalFamily fun i : Fin p => Θ (i : ℕ)) (hΘ0 : Θ 0 = (1 : G → ℂ))
    (hνΘ : ∀ k, ∀ i < p, cfInner (coherentImage ξ ν k) (Θ i) = 0)
    (hj : 0 < j) (hjp : j < p) :
    cfInner (dadeBetaRemainder A R H ξ ν k₀) (Θ j) = cfInner (dadeBeta A R H (ξ k₀)) (Θ j) := by
  have hQ : cfInner (weightedCoherentSum ξ ν (H.index : ℂ)) (Θ j) = 0 :=
    cfInner_weightedCoherentSum_right fun k => hνΘ k j hjp
  rw [dadeBetaRemainder_apply, cfInner_sub_left, cfInner_add_left, cfInner_sub_left,
    cfInner_smul_left, cfInner_one_axis hΘ hΘ0 (by omega) hjp hj.ne', hQ, hνΘ k₀ j hjp]
  ring

end Remainder

section Setting

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {ι : Type*} [Finite ι] {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}
  {p j : ℕ} {Θ : ℕ → G → ℂ} {Γ : G → ℂ} {r : ℝ}

variable (hodd : Odd (Nat.card G))
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hinj : Function.Injective ξ)
  (hν : IsCoherentWith (Set.range ξ) τ ν)
  (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hIrr : ∀ k, ξ k ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ))
  (hS2 : (Set.range ξ).Nontrivial)
  (hhe : 2 * H.index + 1 ≤ Nat.card ↥H)
  (hp : 3 ≤ p)
  (hΘ : IsOrthonormalFamily fun i : Fin p => Θ (i : ℕ))
  (hΘmem : ∀ i < p, Θ i ∈ Submodule.span ℤ (Irr G))
  (hΘ0 : Θ 0 = (1 : G → ℂ))
  (hΘnr : Θ 1 ≠ fun x => conj (Θ 1 x))
  (hconj : ∃ m, 0 < m ∧ m < p ∧ (fun x => conj (Θ 1 x)) = Θ m)
  (hνΘ : ∀ k, ∀ i < p, cfInner (coherentImage ξ ν k) (Θ i) = 0)
  (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ x, (Γ x).im = 0)
  (hΓ1 : cfInner Γ (1 : G → ℂ) = 0)
  (hBnorm : cfInner ((1 : G → ℂ) - Θ 1 + Γ) ((1 : G → ℂ) - Θ 1 + Γ) = (r : ℂ) + 2)
  (hbridge : ∀ F : dadeDomain L A, ∀ i, 0 < i → i < p →
    cfInner ((1 : G → ℂ) - Θ i + Γ) ((dadeMap hD F : classFun G) : G → ℂ) = 0)

omit [Finite ι] in
include hD hν hτ in
theorem coe_nu_eq_dadeMap (f : Submodule.span ℤ (Set.range ξ)) (F : dadeDomain L A)
    (h : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have hF1 : (F : ↥L → ℂ) 1 = 0 :=
    dadeDomain.apply_eq_zero F.2 (by simpa using hD.one_notMem)
  have hf1 : (f : ↥L → ℂ) 1 = 0 := by rw [h, hF1]
  set f₀ : charSpanZero (Set.range ξ) := ⟨(f : ↥L → ℂ), mem_charSpanZero.2 ⟨f.2, hf1⟩⟩ with hf₀
  have hincl : Submodule.inclusion (charSpanZero_le (Set.range ξ)) f₀ = f := Subtype.ext rfl
  rw [← hincl, hν.eq_on_zero f₀, hτ f₀ F h]

omit [Finite ι] in
include hD hA hS hτ hbridge in
theorem cfInner_bridge_baseline (hj : 0 < j) (hjp : j < p)
    (g : charSpanZero (Set.range ξ)) :
    cfInner ((1 : G → ℂ) - Θ j + Γ) (τ g : G → ℂ) = 0 := by
  have hSsub : Set.range ξ ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset
  have hg := mem_charSpanZero.1 g.2
  have hgdom : (g : ↥L → ℂ) ∈ dadeDomain L A :=
    mem_dadeDomain_of_mem_span_indFam hA hSsub hg.1 hg.2
  rw [hτ g ⟨_, hgdom⟩ rfl]
  exact hbridge ⟨_, hgdom⟩ j hj hjp

include hinj hν hIrr in
theorem coherentImage_mem_signedIrr (k : ι) : coherentImage ξ ν k ∈ signedIrr G := by
  have : Fintype ι := Fintype.ofFinite ι
  refine mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
    (CoherentBridgeProjection.coherentImage_mem_span_Irr k) ?_
  simpa using CrossFamilyProjection.cfInner_coherentImage_coherentImage hinj hIrr hν k k

omit [Finite ι] in
include hD hA hS hζ1 hbridge in
theorem cfInner_dadeBeta_axis_eq_one_add (hj : 0 < j) (hjp : j < p) :
    cfInner (dadeBeta A R H (ξ k₀)) (Θ j) = 1 + cfInner (dadeBeta A R H (ξ k₀)) Γ := by
  have hdom : indClassFun H (1 : ↥H → ℂ) - ξ k₀ ∈ dadeDomain L A :=
    indClassFun_one_sub_mem_dadeDomain hA (hS ▸ Set.mem_range_self k₀) hζ1
  have h := hbridge ⟨_, hdom⟩ j hj hjp
  rw [← dadeBeta_eq_dadeMap hD hdom] at h
  have h' : cfInner (dadeBeta A R H (ξ k₀)) ((1 : G → ℂ) - Θ j + Γ) = 0 := by
    rw [← conj_cfInner, h, map_zero]
  rw [cfInner_add_right, cfInner_sub_right,
    cfInner_dadeBeta_one hD hA (hS ▸ Set.mem_range_self k₀) hζ1] at h'
  linear_combination -h'

omit [Finite ι] in
include hD hA hS hζ1 hp hbridge in
theorem cfInner_dadeBeta_axis_eq (hj : 0 < j) (hjp : j < p) :
    cfInner (dadeBeta A R H (ξ k₀)) (Θ j) = cfInner (dadeBeta A R H (ξ k₀)) (Θ 1) := by
  rw [cfInner_dadeBeta_axis_eq_one_add hD hA hS hζ1 hbridge hj hjp,
    cfInner_dadeBeta_axis_eq_one_add hD hA hS hζ1 hbridge Nat.one_pos (by omega)]

include hodd hD hA hS hinj hν hτ hIrr hζ1 hS2 hp hΘ hΘmem hΘ0 hνΘ hΓ hΓreal hΓ1 hbridge in
theorem xor_odd_bridge :
    ∃ b c : ℤ, cfInner ((1 : G → ℂ) - Θ 1 + Γ) (coherentImage ξ ν k₀) = (c : ℂ) ∧
      cfInner (dadeBeta A R H (ξ k₀)) (Θ 1) = (b : ℂ) ∧ Xor (Odd b) (Odd c) := by
  have : Fintype ι := Fintype.ofFinite ι
  have h1p : (1 : ℕ) < p := by omega
  have hα1 : cfInner (coherentImage ξ ν k₀) (1 : G → ℂ) = 0 :=
    cfInner_coherentImage_one hD hA hS hν hτ (hIrr k₀) hζ1 hS2 k₀
  have hθ1 : cfInner (Θ 1) (1 : G → ℂ) = 0 :=
    cfInner_axis_one hΘ hΘ0 (by omega) h1p one_ne_zero
  have hΔreal : ∀ x, (bridgeDelta A R H ξ ν k₀ x).im = 0 :=
    bridgeDelta_apply_im hD hA hS hζ1 (fun f g => hν.inner_eq f g)
      (fun f F h => coe_nu_eq_dadeMap hD hν hτ f F h) (hIrr k₀) hodd
  have hΔ1 : cfInner (bridgeDelta A R H ξ ν k₀) (1 : G → ℂ) = 0 :=
    cfInner_bridgeDelta_one hD hA hS hζ1 (fun f g => hν.inner_eq f g)
      (fun f F h => coe_nu_eq_dadeMap hD hν hτ f F h) (hIrr k₀) hS2
  have hβB : cfInner ((1 : G → ℂ) - coherentImage ξ ν k₀ + bridgeDelta A R H ξ ν k₀)
      ((1 : G → ℂ) - Θ 1 + Γ) = 0 := by
    rw [← dadeBeta_eq_one_sub_add_bridgeDelta]
    have hdom : indClassFun H (1 : ↥H → ℂ) - ξ k₀ ∈ dadeDomain L A :=
      indClassFun_one_sub_mem_dadeDomain hA (hS ▸ Set.mem_range_self k₀) hζ1
    have h := hbridge ⟨_, hdom⟩ 1 Nat.one_pos h1p
    rw [← dadeBeta_eq_dadeMap hD hdom] at h
    rw [← conj_cfInner, h, map_zero]
  obtain ⟨b, c, hc, hb, -, -, hxor⟩ :=
    two_bridge_parity hodd (coherentImage_mem_signedIrr hinj hν hIrr k₀)
      (axis_mem_signedIrr hΘ hΘmem h1p) hα1 hθ1 (hνΘ k₀ 1 h1p) hΓ hΓreal hΓ1
      (bridgeDelta_mem_span_Irr hD hA hS hζ1) hΔreal hΔ1 hβB
  exact ⟨b, c, hc, by rw [← hb, dadeBeta_eq_one_sub_add_bridgeDelta], hxor⟩

include hD hA hS hinj hν hτ hIrr hζ1 hS2 hp hΘ hΘmem hΘ0 hΘnr hconj hνΘ hΓ hΓreal hΓ1
  hBnorm hbridge in
theorem div_le_of_cfInner_bridge_ne_zero
    (hc : cfInner ((1 : G → ℂ) - Θ 1 + Γ) (coherentImage ξ ν k₀) ≠ 0) :
    ((Nat.card ↥H : ℝ) - 1) / (H.index : ℝ) ≤ r := by
  have : Fintype ι := Fintype.ofFinite ι
  have h1p : (1 : ℕ) < p := by omega
  have hθ1 : IsOrthogonal (Θ 1) (1 : G → ℂ) :=
    isOrthogonal_iff.2 (cfInner_axis_one hΘ hΘ0 (by omega) h1p one_ne_zero)
  obtain ⟨m, hm0, hmp, hmeq⟩ := hconj
  refine CoherentBridgeProjection.div_le_of_cfInner_bridge_ne_zero H hinj hS hIrr hν
    (k₀ := k₀) hζ1 (axis_mem_signedIrr hΘ hΘmem h1p) hΘnr hθ1 hΓ
    (fun x => Complex.conj_eq_iff_im.2 (hΓreal x)) (isOrthogonal_iff.2 hΓ1) rfl hBnorm
    (fun g => cfInner_bridge_baseline hD hA hS hτ hbridge Nat.one_pos h1p g)
    (fun k => isOrthogonal_iff.2
      (cfInner_coherentImage_one hD hA hS hν hτ (hIrr k₀) hζ1 hS2 k))
    (fun k => isOrthogonal_iff.2 (hνΘ k 1 h1p))
    (fun k => isOrthogonal_iff.2 (by rw [hmeq]; exact hνΘ k m hmp)) hc

include hD hA hS hinj hν hτ hIrr hζ1 hS2 hhe hp hΘ hΘmem hΘ0 hνΘ hbridge in
theorem le_index_of_cfInner_dadeBeta_axis_ne_zero
    (hb : cfInner (dadeBeta A R H (ξ k₀)) (Θ 1) ≠ 0) : p ≤ H.index := by
  have : Fintype ι := Fintype.ofFinite ι
  have h1p : (1 : ℕ) < p := by omega
  have hrow : ∀ j, 0 < j → j < p →
      cfInner (dadeBetaRemainder A R H ξ ν k₀) (Θ j)
        = cfInner (dadeBeta A R H (ξ k₀)) (Θ 1) := fun j hj hjp => by
    rw [cfInner_dadeBetaRemainder_axis hΘ hΘ0 hνΘ hj hjp,
      cfInner_dadeBeta_axis_eq hD hA hS hζ1 hp hbridge hj hjp]
  have hbessel := card_sub_one_mul_norm_sq_le (Θ := Θ) (by omega) hΘ hrow
  have hnorm := cfInner_self_dadeBetaRemainder_re_le_index_sub_one hD hA hS hinj hν hτ
    (hIrr k₀) hζ1 hS2 hhe (k₀ := k₀)
  have hβmem : dadeBeta A R H (ξ k₀) ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars
      (dadeBeta_mem_virtualChars hD hA (hS ▸ Set.mem_range_self k₀) hζ1)
  obtain ⟨n, hn⟩ := exists_int_cfInner_of_mem_span_Irr hβmem (hΘmem 1 h1p)
  have hn0 : n ≠ 0 := fun h0 => hb (by rw [hn, h0]; simp)
  have hone : (1 : ℝ) ≤ ‖cfInner (dadeBeta A R H (ξ k₀)) (Θ 1)‖ ^ 2 := by
    rw [hn, Complex.norm_intCast, sq_abs]
    have hsq : (1 : ℤ) ≤ n ^ 2 := by rcases lt_or_gt_of_ne hn0 with h | h <;> nlinarith
    exact_mod_cast (Int.cast_le (R := ℝ)).2 hsq
  have hidx : (1 : ℝ) ≤ (H.index : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
  have hfinal : ((p : ℝ) - 1) ≤ (H.index : ℝ) - 1 := by nlinarith [hbessel, hnorm, hone]
  have hple : (p : ℝ) ≤ (H.index : ℝ) := by linarith
  exact_mod_cast hple

include hodd hD hA hS hinj hν hτ hIrr hζ1 hS2 hhe hp hΘ hΘmem hΘ0 hΘnr hconj hνΘ hΓ hΓreal
  hΓ1 hBnorm hbridge in
theorem bridge_parity_alternative :
    ∃ b c : ℤ, cfInner ((1 : G → ℂ) - Θ 1 + Γ) (coherentImage ξ ν k₀) = (c : ℂ) ∧
      cfInner (dadeBeta A R H (ξ k₀)) (Θ 1) = (b : ℂ) ∧
      (∀ j, 0 < j → j < p → cfInner (dadeBeta A R H (ξ k₀)) (Θ j) = (b : ℂ)) ∧
      Xor (Odd b) (Odd c) ∧
      ((Odd c ∧ ((Nat.card ↥H : ℝ) - 1) / (H.index : ℝ) ≤ r) ∨ (Odd b ∧ p ≤ H.index)) := by
  obtain ⟨b, c, hc, hb, hxor⟩ := xor_odd_bridge hodd hD hA hS hinj hν hτ hIrr hζ1 hS2 hp hΘ
    hΘmem hΘ0 hνΘ hΓ hΓreal hΓ1 hbridge
  refine ⟨b, c, hc, hb, fun j hj hjp => by
    rw [cfInner_dadeBeta_axis_eq hD hA hS hζ1 hp hbridge hj hjp, hb], hxor, ?_⟩
  rcases hxor with ⟨hbodd, -⟩ | ⟨hcodd, -⟩
  ·
    refine Or.inr ⟨hbodd, le_index_of_cfInner_dadeBeta_axis_ne_zero hD hA hS hinj hν hτ hIrr
      hζ1 hS2 hhe hp hΘ hΘmem hΘ0 hνΘ hbridge ?_⟩
    have hb0 : b ≠ 0 := by rcases hbodd with ⟨k, hk⟩; omega
    rw [hb]
    simpa using hb0
  ·
    refine Or.inl ⟨hcodd, div_le_of_cfInner_bridge_ne_zero hD hA hS hinj hν hτ hIrr hζ1 hS2 hp
      hΘ hΘmem hΘ0 hΘnr hconj hνΘ hΓ hΓreal hΓ1 hBnorm hbridge ?_⟩
    have hc0 : c ≠ 0 := by rcases hcodd with ⟨k, hk⟩; omega
    rw [hc]
    simpa using hc0

include hodd hD hA hS hinj hν hτ hIrr hζ1 hS2 hhe hp hΘ hΘmem hΘ0 hΘnr hconj hνΘ hΓ hΓreal
  hΓ1 hBnorm hbridge in
theorem odd_row_and_le_index_of_lt (hr : r < ((Nat.card ↥H : ℝ) - 1) / (H.index : ℝ)) :
    (∀ j, 0 < j → j < p → ∃ n : ℤ, Odd n ∧
        cfInner (dadeBeta A R H (ξ k₀)) (Θ j) = (n : ℂ)) ∧ p ≤ H.index := by
  obtain ⟨b, c, -, -, hrow, -, halt⟩ := bridge_parity_alternative hodd hD hA hS hinj hν hτ hIrr
    hζ1 hS2 hhe hp hΘ hΘmem hΘ0 hΘnr hconj hνΘ hΓ hΓreal hΓ1 hBnorm hbridge
  rcases halt with ⟨-, hle⟩ | ⟨hbodd, hple⟩
  · exact absurd hle (not_le.2 hr)
  · exact ⟨fun j hj hjp => ⟨b, hbodd, hrow j hj hjp⟩, hple⟩

end Setting

end DadeBridgeParity

end CFSG.FeitThompson
