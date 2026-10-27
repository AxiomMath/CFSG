module

public import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.NormalInducedFamilyWeightedNorm
public import CFSG.FeitThompson.Representations.DadeBetaIntegralDegreeZero
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.WitnessCongruenceLocalInverseNormBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace MultipleRemainderProjection

open CrossFamilyProjection DisjointCoherentFamilies

section Def

variable {L G : Type*} [One L] [Group G] {ι : Type*} [Fintype ι]

noncomputable def coherentRemainder (β : G → ℂ) (ξ : ι → (L → ℂ))
    (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) (a e : ℂ) : G → ℂ :=
  β - 1 + coherentImage ξ ν k₀ - a • coherentSum ξ ν e

theorem coherentRemainder_apply (β : G → ℂ) (ξ : ι → (L → ℂ))
    (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) (a e : ℂ) :
    coherentRemainder β ξ ν k₀ a e
      = β - 1 + coherentImage ξ ν k₀ - a • coherentSum ξ ν e := (rfl)

omit [One L] [Fintype ι] in
noncomputable def remainderCoeff [Fintype G] (β : G → ℂ) (ξ : ι → (L → ℂ))
    (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) : ℂ :=
  cfInner β (coherentImage ξ ν k₀) + 1

omit [One L] [Fintype ι] in
theorem remainderCoeff_apply [Fintype G] (β : G → ℂ) (ξ : ι → (L → ℂ))
    (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) :
    remainderCoeff β ξ ν k₀ = cfInner β (coherentImage ξ ν k₀) + 1 := (rfl)

end Def

section OneFamily

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {ι : Type*} {ξ : ι → (L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {D : Set G}

theorem cfInner_one_coherentImage (h : IsFullCoherentFamily ξ τ ν D) (k : ι) :
    cfInner (1 : G → ℂ) (coherentImage ξ ν k) = 0 := by
  have h0 : cfInner (coherentVal ν (⟨ξ k, ⟨k, rfl⟩⟩ : Set.range ξ)) (1 : G → ℂ) = 0 :=
    cfInner_coherentVal_one h.subset_Irr (h.two_le_ncard k) h.star_mem h.star_ne
      h.apply_one_eq_zero h.star_tau' h.isCoherentWith _
  rw [coherentVal_apply, ← coherentImage_apply] at h0
  rw [← conj_cfInner, h0, map_zero]

theorem cfInner_coherentSum_coherentImage_eq_zero {L' : Type*} [Group L'] [Fintype L']
    {ι' : Type*} {ξ' : ι' → (L' → ℂ)}
    {τ' : charSpanZero (Set.range ξ') →+ virtualChars G}
    {ν' : Submodule.span ℤ (Set.range ξ') →+ virtualChars G} {D' : Set G} [Fintype ι]
    (h : IsFullCoherentFamily ξ τ ν D) (h' : IsFullCoherentFamily ξ' τ' ν' D')
    (hd : Disjoint D D') (e : ℂ) (l : ι') :
    cfInner (coherentSum ξ ν e) (coherentImage ξ' ν' l) = 0 := by
  rw [coherentSum_apply, cfInner_sum_left]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [cfInner_smul_left, cfInner_coherentImage_coherentImage_eq_zero h h' hd k l, mul_zero]

theorem exists_natCast_apply_one_div_index (H : Subgroup L) [H.Normal]
    (hS : Set.range ξ = indFam H (Irr H \ {1})) (k : ι) :
    ∃ m : ℕ, ξ k 1 / (H.index : ℂ) = (m : ℂ) := by
  obtain ⟨d, -, ⟨m, rfl⟩, hd⟩ :=
    NormalInducedFamily.exists_apply_one_eq_of_mem_indFam H
      (NormalInducedWeightedNorm.mem_indFam_of_range_eq hS k)
  have he : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  refine ⟨m, ?_⟩
  rw [hd]
  push_cast
  field_simp

theorem sum_norm_sq_apply_one_div_index [Fintype ι] (H : Subgroup L) [H.Normal]
    (hinj : Function.Injective ξ) (hS : Set.range ξ = indFam H (Irr H \ {1}))
    (hIrr : ∀ k, ξ k ∈ Irr L) :
    ∑ k, ‖ξ k 1 / (H.index : ℂ)‖ ^ 2 = ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
  have key := NormalInducedWeightedNorm.sum_sq_div_cfInner H hinj hS
  simp only [cfInner_self_of_mem_Irr (hIrr _), div_one] at key
  refine Complex.ofReal_injective ?_
  push_cast
  rw [← key]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨m, hm⟩ := exists_natCast_apply_one_div_index H hS k
  rw [hm]
  simp

end OneFamily

section Main

variable {G : Type*} [Group G] [Fintype G] {I : Type*} {Lty : I → Type*} [∀ i, Group (Lty i)]
  [∀ i, Fintype (Lty i)] {ι : I → Type*} [∀ i, Fintype (ι i)] {ξ : ∀ i, ι i → (Lty i → ℂ)}
  {τ : ∀ i, charSpanZero (Set.range (ξ i)) →+ virtualChars G}
  {ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G} {D : I → Set G}
  {H : ∀ i, Subgroup (Lty i)} {k₀ : ∀ i, ι i} {β : I → (G → ℂ)} {a : I → ℂ}

theorem cfInner_coherentRemainder_coherentImage
    (hfam : ∀ i, IsFullCoherentFamily (ξ i) (τ i) (ν i) (D i))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j))
    (hS : ∀ i, Set.range (ξ i) ⊆ indFam (H i) (Irr (H i)))
    (hζ : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
    (hβ : ∀ i, Function.support (β i) ⊆ D i)
    {i j : I} (hij : i ≠ j) (k : ι j) :
    cfInner (coherentRemainder (β i) (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ))
        (coherentImage (ξ j) (ν j) k)
      = (ξ j k 1 / ((H j).index : ℂ))
        * cfInner (β i) (coherentImage (ξ j) (ν j) (k₀ j)) := by
  have hβτ : ∀ f : charSpanZero (Set.range (ξ j)), cfInner (β i) (τ j f : G → ℂ) = 0 :=
    CrossFamilyProjection.forall_cfInner_eq_zero_of_disjoint_support (hβ i)
      (hfam j).support_subset (hdisj hij)
  have h1 : cfInner (1 : G → ℂ) (coherentImage (ξ j) (ν j) k) = 0 :=
    cfInner_one_coherentImage (hfam j) k
  have h2 : cfInner (coherentImage (ξ i) (ν i) (k₀ i)) (coherentImage (ξ j) (ν j) k) = 0 :=
    cfInner_coherentImage_coherentImage_eq_zero_of_ne hfam hdisj hij _ k
  have h3 : cfInner (coherentSum (ξ i) (ν i) ((H i).index : ℂ))
      (coherentImage (ξ j) (ν j) k) = 0 :=
    cfInner_coherentSum_coherentImage_eq_zero (hfam i) (hfam j) (hdisj hij) _ k
  have h4 := CrossFamilyProjection.cfInner_coherentImage_eq (β := β i) (H j) (hS j)
    (hfam j).isCoherentWith hβτ (hζ j) k
  rw [coherentRemainder_apply, cfInner_sub_left, cfInner_add_left, cfInner_sub_left,
    cfInner_smul_left, h1, h2, h3, h4]
  ring

variable [∀ i, (H i).Normal]

open scoped Classical in
theorem sum_norm_sq_cfInner_mul_le
    (hfam : ∀ i, IsFullCoherentFamily (ξ i) (τ i) (ν i) (D i))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j))
    (hinj : ∀ i, Function.Injective (ξ i))
    (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr (H i) \ {1}))
    (hζ : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
    (hβ : ∀ i, Function.support (β i) ⊆ D i)
    (i : I) (B : Finset I) (hB : ∀ j ∈ B, j ≠ i) :
    ∑ j ∈ B, ‖cfInner (β i) (coherentImage (ξ j) (ν j) (k₀ j))‖ ^ 2
        * (((Nat.card (H j) : ℝ) - 1) / ((H j).index : ℝ))
      ≤ (cfInner (coherentRemainder (β i) (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ))
          (coherentRemainder (β i) (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ))).re := by
  set Γ := coherentRemainder (β i) (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ) with hΓ
  have hSsub : ∀ i, Set.range (ξ i) ⊆ indFam (H i) (Irr (H i)) := fun i => by
    rw [hS i]; exact indFam_mono _ Set.sdiff_subset
  have hortho : ∀ p q : (Σ j : {x // x ∈ B}, ι j),
      cfInner (coherentImage (ξ p.1) (ν p.1) p.2) (coherentImage (ξ q.1) (ν q.1) q.2)
        = if p = q then 1 else 0 := by
    rintro ⟨j, k⟩ ⟨j', k'⟩
    by_cases hjj : (j : I) = (j' : I)
    · obtain rfl : j = j' := Subtype.ext hjj
      rw [CrossFamilyProjection.cfInner_coherentImage_coherentImage (hinj j)
        (fun k => (hfam j).subset_Irr ⟨k, rfl⟩) (hfam j).isCoherentWith]
      by_cases hk : k = k'
      · subst hk; simp
      · rw [if_neg hk, if_neg (by simpa using hk)]
    · rw [cfInner_coherentImage_coherentImage_eq_zero_of_ne hfam hdisj hjj,
        if_neg (fun h => hjj (congrArg Subtype.val (congrArg Sigma.fst h)))]
  have hbessel := sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hortho Γ
  refine le_trans (le_of_eq ?_) hbessel
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_coe_sort B]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hone : ∀ k : ι j, ‖cfInner Γ (coherentImage (ξ j) (ν j) k)‖ ^ 2
      = ‖ξ j k 1 / ((H j).index : ℂ)‖ ^ 2
        * ‖cfInner (β i) (coherentImage (ξ j) (ν j) (k₀ j))‖ ^ 2 := by
    intro k
    rw [hΓ, cfInner_coherentRemainder_coherentImage hfam hdisj hSsub hζ hβ
      (Ne.symm (hB j j.2)) k, norm_mul, mul_pow]
  rw [Finset.sum_congr rfl fun k _ => hone k, ← Finset.sum_mul,
    sum_norm_sq_apply_one_div_index (H j) (hinj j) (hS j)
      (fun k => (hfam j).subset_Irr ⟨k, rfl⟩)]
  ring

open scoped ComplexOrder in
theorem sum_norm_sq_cfInner_mul_le_cfInner_self
    (hfam : ∀ i, IsFullCoherentFamily (ξ i) (τ i) (ν i) (D i))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j))
    (hinj : ∀ i, Function.Injective (ξ i))
    (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr (H i) \ {1}))
    (hζ : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
    (hβ : ∀ i, Function.support (β i) ⊆ D i)
    (i : I) (B : Finset I) (hB : ∀ j ∈ B, j ≠ i) :
    ((∑ j ∈ B, ‖cfInner (β i) (coherentImage (ξ j) (ν j) (k₀ j))‖ ^ 2
        * (((Nat.card (H j) : ℝ) - 1) / ((H j).index : ℝ)) : ℝ) : ℂ)
      ≤ cfInner (coherentRemainder (β i) (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ))
          (coherentRemainder (β i) (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ)) := by
  have hle := sum_norm_sq_cfInner_mul_le (a := a) hfam hdisj hinj hS hζ hβ i B hB
  rw [cfInner_self_eq_ofReal] at hle ⊢
  rw [Complex.ofReal_re] at hle
  exact Complex.real_le_real.2 hle

theorem sum_norm_sq_cfInner_mul_le_remainderCoeff
    (hfam : ∀ i, IsFullCoherentFamily (ξ i) (τ i) (ν i) (D i))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j))
    (hinj : ∀ i, Function.Injective (ξ i))
    (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr (H i) \ {1}))
    (hζ : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
    (hβ : ∀ i, Function.support (β i) ⊆ D i)
    (i : I) (B : Finset I) (hB : ∀ j ∈ B, j ≠ i) :
    ∑ j ∈ B, ‖cfInner (β i) (coherentImage (ξ j) (ν j) (k₀ j))‖ ^ 2
        * (((Nat.card (H j) : ℝ) - 1) / ((H j).index : ℝ))
      ≤ (cfInner
          (coherentRemainder (β i) (ξ i) (ν i) (k₀ i)
            (remainderCoeff (β i) (ξ i) (ν i) (k₀ i)) ((H i).index : ℂ))
          (coherentRemainder (β i) (ξ i) (ν i) (k₀ i)
            (remainderCoeff (β i) (ξ i) (ν i) (k₀ i)) ((H i).index : ℂ))).re :=
  sum_norm_sq_cfInner_mul_le (a := fun i => remainderCoeff (β i) (ξ i) (ν i) (k₀ i))
    hfam hdisj hinj hS hζ hβ i B hB

end Main

section Bridge

variable {G : Type*} [Group G] [Fintype G] {I : Type*}
  {Lsub : I → Subgroup G} [∀ i, Fintype ↥(Lsub i)] {A : I → Set G} {J : I → G → Subgroup G}
  {H : ∀ i, Subgroup ↥(Lsub i)} [∀ i, (H i).Normal]
  {ι : I → Type*} {ξ : ∀ i, ι i → (↥(Lsub i) → ℂ)} {k₀ : ∀ i, ι i}

omit [Fintype G] in
theorem support_dadeBeta_subset [Finite G] {i : I} (hD : IsDadeData (Lsub i) (A i) (J i))
    (hA : A i = (fun x : ↥(Lsub i) => (x : G)) '' (((H i) : Set ↥(Lsub i)) \ {1}))
    (hζS : ξ i (k₀ i) ∈ indFam (H i) (Irr ↥(H i) \ {1}))
    (hζ1 : ξ i (k₀ i) 1 = ((H i).index : ℂ)) :
    Function.support (NormalInducedFamily.dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
      ⊆ totalDadeSupport (A i) (J i) := by
  intro x hx
  by_contra h
  exact hx (NormalInducedFamily.dadeBeta_eq_zero_of_notMem hD
    (NormalInducedFamily.indClassFun_one_sub_mem_dadeDomain hA hζS hζ1) h)

variable [∀ i, Fintype (ι i)]
  {τ : ∀ i, charSpanZero (Set.range (ξ i)) →+ virtualChars G}
  {ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G} {a : I → ℂ}

open scoped Classical in
theorem sum_norm_sq_cfInner_dadeBeta_mul_le
    (hDade : ∀ i, IsDadeData (Lsub i) (A i) (J i))
    (hA : ∀ i, A i = (fun x : ↥(Lsub i) => (x : G)) '' (((H i) : Set ↥(Lsub i)) \ {1}))
    (hfam : ∀ i, IsFullCoherentFamily (ξ i) (τ i) (ν i) (totalDadeSupport (A i) (J i)))
    (hdisj : Pairwise fun i j =>
      Disjoint (totalDadeSupport (A i) (J i)) (totalDadeSupport (A j) (J j)))
    (hinj : ∀ i, Function.Injective (ξ i))
    (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr ↥(H i) \ {1}))
    (hζ : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
    (i : I) (B : Finset I) (hB : ∀ j ∈ B, j ≠ i) :
    ∑ j ∈ B, ‖cfInner (NormalInducedFamily.dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
          (coherentImage (ξ j) (ν j) (k₀ j))‖ ^ 2
        * (((Nat.card ↥(H j) : ℝ) - 1) / ((H j).index : ℝ))
      ≤ (cfInner
          (coherentRemainder (NormalInducedFamily.dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
            (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ))
          (coherentRemainder (NormalInducedFamily.dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
            (ξ i) (ν i) (k₀ i) (a i) ((H i).index : ℂ))).re :=
  sum_norm_sq_cfInner_mul_le hfam hdisj hinj hS hζ
    (fun i => support_dadeBeta_subset (hDade i) (hA i)
      (by rw [← hS i]; exact ⟨k₀ i, rfl⟩) (hζ i)) i B hB

end Bridge

end MultipleRemainderProjection

end CFSG.FeitThompson
