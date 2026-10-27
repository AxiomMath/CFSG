module

public import CFSG.FeitThompson.Representations.CoherentExtensionNonrealConjPairs
public import CFSG.FeitThompson.Representations.ProjectionCoefficientsDistinctFamilies
public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace DisjointCoherentFamilies

open CrossFamilyProjection (coherentImage coherentImage_apply coherentSum coherentSum_apply)

section Irreducibles

variable {G : Type*} [Group G] [Fintype G]

theorem cfInner_sub_star_self_eq_two {a : G → ℂ} (ha : a ∈ Irr G) (hanr : star a ≠ a) :
    cfInner (a - star a) (a - star a) = 2 := by
  have has : star a ∈ Irr G := star_mem_Irr ha
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_eq_ite_of_mem_Irr ha ha, cfInner_eq_ite_of_mem_Irr ha has,
    cfInner_eq_ite_of_mem_Irr has ha, cfInner_eq_ite_of_mem_Irr has has, if_pos rfl, if_pos rfl,
    if_neg (fun h : a = star a => hanr h.symm), if_neg hanr]
  norm_num

theorem cfInner_eq_zero_of_cfInner_sub_star_eq_zero {a b : G → ℂ} (ha : a ∈ Irr G)
    (hb : b ∈ Irr G) (hanr : star a ≠ a) (h : cfInner (a - star a) (b - star b) = 0) :
    cfInner a b = 0 := by
  classical
  have hab : a ≠ b := by
    rintro rfl
    rw [cfInner_sub_star_self_eq_two ha hanr] at h
    norm_num at h
  rw [cfInner_eq_ite_of_mem_Irr ha hb, if_neg hab]

end Irreducibles

section Induced

variable {L : Type*} [Group L] [Fintype L] (K : Subgroup L)

theorem indClassFun_star (θ : K → ℂ) : indClassFun K (star θ) = star (indClassFun K θ) := by
  classical
  funext y
  rw [Pi.star_apply, indClassFun_apply, indClassFun_apply]
  simp only [Complex.star_def, map_mul, map_sum, map_inv₀, Complex.conj_natCast, Pi.star_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

theorem star_mem_indFam {X : Set (K → ℂ)} (hX : ∀ θ ∈ X, star θ ∈ X) {f : L → ℂ}
    (hf : f ∈ indFam K X) : star f ∈ indFam K X := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFam K).1 hf
  exact (mem_indFam K).2 ⟨star θ, hX θ hθ, indClassFun_star K θ⟩

omit [Fintype L] in
theorem star_mem_Irr_diff_one [Finite K] {θ : K → ℂ} (hθ : θ ∈ Irr K \ {1}) :
    star θ ∈ Irr K \ {1} := by
  refine ⟨star_mem_Irr hθ.1, fun h => hθ.2 ?_⟩
  simpa using congrArg (fun f : K → ℂ => star f) h

theorem ne_one_of_mem_indFam_diff_one [K.Normal] {f : L → ℂ} (hf : f ∈ indFam K (Irr K \ {1})) :
    f ≠ (1 : L → ℂ) := by
  intro hone
  have h0 : cfInner f (1 : L → ℂ) = 0 :=
    NormalInducedFamily.cfInner_one_of_mem_indFam_diff K
      (by rw [NormalInducedFamily.indFam_diff_singleton]; exact hf)
  rw [hone, cfInner_one_one] at h0
  exact one_ne_zero h0

theorem star_ne_self_of_mem_indFam_diff_one [K.Normal] (hodd : Odd (Nat.card L)) {f : L → ℂ}
    (hIrr : f ∈ Irr L) (hf : f ∈ indFam K (Irr K \ {1})) : star f ≠ f := by
  intro h
  refine ne_conj_of_mem_Irr_of_ne_one_of_odd hodd hIrr (ne_one_of_mem_indFam_diff_one K hf) ?_
  funext g
  exact (congrFun h g).symm

end Induced

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {ι : Type*} {ξ : ι → (L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {D : Set G}

structure IsFullCoherentFamily (ξ : ι → (L → ℂ))
    (τ : charSpanZero (Set.range ξ) →+ virtualChars G)
    (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (D : Set G) : Prop where
  subset_Irr : Set.range ξ ⊆ Irr L
  star_mem : ∀ χ ∈ Set.range ξ, star χ ∈ Set.range ξ
  star_ne : ∀ χ ∈ Set.range ξ, star χ ≠ χ
  support_subset : ∀ f : charSpanZero (Set.range ξ), Function.support (τ f : G → ℂ) ⊆ D
  one_notMem : (1 : G) ∉ D
  star_tau : ∀ f g : charSpanZero (Set.range ξ), (g : L → ℂ) = star (f : L → ℂ) →
    (τ g : G → ℂ) = star ((τ f : G → ℂ))
  isCoherentWith : IsCoherentWith (Set.range ξ) τ ν

namespace IsFullCoherentFamily

theorem apply_one_eq_zero (h : IsFullCoherentFamily ξ τ ν D) (f : charSpanZero (Set.range ξ)) :
    (τ f : G → ℂ) 1 = 0 := by
  by_contra hne
  exact h.one_notMem (h.support_subset f (Function.mem_support.2 hne))

theorem star_tau' (h : IsFullCoherentFamily ξ τ ν D) (f : charSpanZero (Set.range ξ)) :
    (τ (starCharSpanZero h.star_mem f) : G → ℂ) = star ((τ f : G → ℂ)) :=
  h.star_tau f _ (coe_starCharSpanZero h.star_mem f)

theorem two_le_ncard (h : IsFullCoherentFamily ξ τ ν D) (k : ι) : 2 ≤ (Set.range ξ).ncard := by
  have hfin : (Set.range ξ).Finite := Set.Finite.subset finite_Irr h.subset_Irr
  have hsub : ({ξ k, star (ξ k)} : Set (L → ℂ)) ⊆ Set.range ξ := by
    rintro f (rfl | rfl)
    · exact ⟨k, rfl⟩
    · exact h.star_mem _ ⟨k, rfl⟩
  have hpair : ({ξ k, star (ξ k)} : Set (L → ℂ)).ncard = 2 :=
    Set.ncard_pair (Ne.symm (h.star_ne _ ⟨k, rfl⟩))
  calc (2 : ℕ) = _ := hpair.symm
    _ ≤ (Set.range ξ).ncard := Set.ncard_le_ncard hsub hfin

theorem exists_sign_nonreal_root (h : IsFullCoherentFamily ξ τ ν D) (k₀ : ι) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ η : Set.range ξ → (G → ℂ), Function.Injective η ∧
      (∀ χ : Set.range ξ, η χ ∈ Irr G) ∧ (∀ χ : Set.range ξ, coherentVal ν χ = ε • η χ) ∧
      (∀ χ : Set.range ξ, star (η χ) ≠ η χ) ∧
      (∀ χ : Set.range ξ, η (starElem h.star_mem χ) = star (η χ)) :=
  exists_sign_nonreal_root_of_isCoherentWith h.subset_Irr (h.two_le_ncard k₀) h.star_mem
    h.star_ne h.apply_one_eq_zero h.star_tau' h.isCoherentWith

theorem support_coherentVal_sub_coherentVal_starElem (h : IsFullCoherentFamily ξ τ ν D)
    (χ : Set.range ξ) :
    Function.support (coherentVal ν χ - coherentVal ν (starElem h.star_mem χ)) ⊆ D := by
  rw [coherentVal_sub_coherentVal_starElem h.subset_Irr h.star_mem h.isCoherentWith χ]
  exact h.support_subset _

end IsFullCoherentFamily

section Bridge

variable {G : Type*} [Group G] [Fintype G] {Lsub : Subgroup G} [Fintype ↥Lsub] {A : Set G}
  {J : G → Subgroup G} {H : Subgroup ↥Lsub} {κ : Type*} {ζ : κ → (↥Lsub → ℂ)}
  {σ : charSpanZero (Set.range ζ) →+ virtualChars G}
  {μ : Submodule.span ℤ (Set.range ζ) →+ virtualChars G}

omit [Fintype G] in
theorem mem_dadeDomain_of_charSpanZero [H.Normal]
    (hA : A = (fun x : ↥Lsub => (x : G)) '' ((H : Set ↥Lsub) \ {1}))
    (hS : Set.range ζ = indFam H (Irr ↥H \ {1})) (f : charSpanZero (Set.range ζ)) :
    (f : ↥Lsub → ℂ) ∈ dadeDomain Lsub A := by
  refine NormalInducedFamily.mem_dadeDomain_of_mem_span_indFam hA ?_ (charSpanZero_le _ f.2)
    (charSpanZero_apply_one f)
  rw [hS]
  exact indFam_mono H Set.sdiff_subset

theorem isFullCoherentFamily_of_isDadeData [H.Normal] (hodd : Odd (Nat.card G))
    (hD : IsDadeData Lsub A J)
    (hA : A = (fun x : ↥Lsub => (x : G)) '' ((H : Set ↥Lsub) \ {1}))
    (hS : Set.range ζ = indFam H (Irr ↥H \ {1})) (hIrr : Set.range ζ ⊆ Irr ↥Lsub)
    (hσ : ∀ (f : charSpanZero (Set.range ζ)) (hf : (f : ↥Lsub → ℂ) ∈ dadeDomain Lsub A),
      (σ f : G → ℂ) = ((dadeMap hD ⟨(f : ↥Lsub → ℂ), hf⟩ : classFun G) : G → ℂ))
    (hμ : IsCoherentWith (Set.range ζ) σ μ) :
    IsFullCoherentFamily ζ σ μ (totalDadeSupport A J) where
  subset_Irr := hIrr
  star_mem := fun χ hχ => by
    rw [hS] at hχ ⊢
    exact star_mem_indFam H (fun θ hθ => star_mem_Irr_diff_one H hθ) hχ
  star_ne := fun χ hχ =>
    star_ne_self_of_mem_indFam_diff_one H
      (Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card Lsub)) (hIrr hχ)
      (by rw [← hS]; exact hχ)
  support_subset := fun f => by
    rw [hσ f (mem_dadeDomain_of_charSpanZero hA hS f)]
    exact support_dadeMap_subset hD _
  one_notMem := hD.one_notMem_totalDadeSupport
  star_tau := fun f g hg => by
    rw [hσ g (mem_dadeDomain_of_charSpanZero hA hS g),
      hσ f (mem_dadeDomain_of_charSpanZero hA hS f), ←
      dadeMap_star hD (mem_dadeDomain_of_charSpanZero hA hS f)]
    congr 2
    exact Subtype.ext hg
  isCoherentWith := hμ

end Bridge

section Main

variable {G : Type*} [Group G] [Fintype G] {L₁ L₂ : Type*} [Group L₁] [Fintype L₁] [Group L₂]
  [Fintype L₂] {ι₁ ι₂ : Type*} {ξ₁ : ι₁ → (L₁ → ℂ)} {ξ₂ : ι₂ → (L₂ → ℂ)}
  {τ₁ : charSpanZero (Set.range ξ₁) →+ virtualChars G}
  {ν₁ : Submodule.span ℤ (Set.range ξ₁) →+ virtualChars G}
  {τ₂ : charSpanZero (Set.range ξ₂) →+ virtualChars G}
  {ν₂ : Submodule.span ℤ (Set.range ξ₂) →+ virtualChars G} {D₁ D₂ : Set G}

theorem cfInner_coherentVal_coherentVal_eq_zero (h₁ : IsFullCoherentFamily ξ₁ τ₁ ν₁ D₁)
    (h₂ : IsFullCoherentFamily ξ₂ τ₂ ν₂ D₂) (hd : Disjoint D₁ D₂)
    (χ : Set.range ξ₁) (ψ : Set.range ξ₂) :
    cfInner (coherentVal ν₁ χ) (coherentVal ν₂ ψ) = 0 := by
  obtain ⟨k, -⟩ := χ.2
  obtain ⟨l, -⟩ := ψ.2
  obtain ⟨ε₁, hε₁, η₁, -, hη₁Irr, hη₁eq, hη₁nr, hη₁star⟩ := h₁.exists_sign_nonreal_root k
  obtain ⟨ε₂, hε₂, η₂, -, hη₂Irr, hη₂eq, -, hη₂star⟩ := h₂.exists_sign_nonreal_root l
  have hε₁ne : ε₁ ≠ 0 := by rcases hε₁ with rfl | rfl <;> simp
  have hε₂ne : (starRingEnd ℂ) ε₂ ≠ 0 := by rcases hε₂ with rfl | rfl <;> simp
  have hd₁ : coherentVal ν₁ χ - coherentVal ν₁ (starElem h₁.star_mem χ)
      = ε₁ • (η₁ χ - star (η₁ χ)) := by
    rw [hη₁eq χ, hη₁eq (starElem h₁.star_mem χ), hη₁star χ, smul_sub]
  have hd₂ : coherentVal ν₂ ψ - coherentVal ν₂ (starElem h₂.star_mem ψ)
      = ε₂ • (η₂ ψ - star (η₂ ψ)) := by
    rw [hη₂eq ψ, hη₂eq (starElem h₂.star_mem ψ), hη₂star ψ, smul_sub]
  have hzero : cfInner (ε₁ • (η₁ χ - star (η₁ χ))) (ε₂ • (η₂ ψ - star (η₂ ψ))) = 0 := by
    rw [← hd₁, ← hd₂]
    exact cfInner_eq_zero_of_disjoint_support
      (hd.mono (h₁.support_coherentVal_sub_coherentVal_starElem χ)
        (h₂.support_coherentVal_sub_coherentVal_starElem ψ))
  rw [cfInner_smul_left, cfInner_smul_right] at hzero
  have hpair : cfInner (η₁ χ - star (η₁ χ)) (η₂ ψ - star (η₂ ψ)) = 0 := by
    simpa [hε₁ne, hε₂ne] using hzero
  rw [hη₁eq χ, hη₂eq ψ, cfInner_smul_left, cfInner_smul_right,
    cfInner_eq_zero_of_cfInner_sub_star_eq_zero (hη₁Irr χ) (hη₂Irr ψ) (hη₁nr χ) hpair]
  ring

theorem cfInner_coherentImage_coherentImage_eq_zero (h₁ : IsFullCoherentFamily ξ₁ τ₁ ν₁ D₁)
    (h₂ : IsFullCoherentFamily ξ₂ τ₂ ν₂ D₂) (hd : Disjoint D₁ D₂) (k : ι₁) (l : ι₂) :
    cfInner (coherentImage ξ₁ ν₁ k) (coherentImage ξ₂ ν₂ l) = 0 := by
  have h := cfInner_coherentVal_coherentVal_eq_zero h₁ h₂ hd ⟨ξ₁ k, ⟨k, rfl⟩⟩ ⟨ξ₂ l, ⟨l, rfl⟩⟩
  rwa [coherentVal_apply, coherentVal_apply, ← coherentImage_apply, ← coherentImage_apply] at h

theorem cfInner_coherentSum_coherentSum_eq_zero [Fintype ι₁] [Fintype ι₂]
    (h₁ : IsFullCoherentFamily ξ₁ τ₁ ν₁ D₁) (h₂ : IsFullCoherentFamily ξ₂ τ₂ ν₂ D₂)
    (hd : Disjoint D₁ D₂) (e₁ e₂ : ℂ) :
    cfInner (coherentSum ξ₁ ν₁ e₁) (coherentSum ξ₂ ν₂ e₂) = 0 := by
  rw [coherentSum_apply, coherentSum_apply, cfInner_sum_left]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [cfInner_smul_left, cfInner_sum_right, Finset.sum_eq_zero fun l _ => ?_, mul_zero]
  rw [cfInner_smul_right, cfInner_coherentImage_coherentImage_eq_zero h₁ h₂ hd k l, mul_zero]

end Main

section Indexed

variable {G : Type*} [Group G] [Fintype G] {I : Type*} {Lty : I → Type*} [∀ i, Group (Lty i)]
  [∀ i, Fintype (Lty i)] {ι : I → Type*} {ξ : ∀ i, ι i → (Lty i → ℂ)}
  {τ : ∀ i, charSpanZero (Set.range (ξ i)) →+ virtualChars G}
  {ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G} {D : I → Set G}

theorem cfInner_coherentImage_coherentImage_eq_zero_of_ne
    (hfam : ∀ i, IsFullCoherentFamily (ξ i) (τ i) (ν i) (D i))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) {i j : I} (hij : i ≠ j)
    (k : ι i) (l : ι j) :
    cfInner (coherentImage (ξ i) (ν i) k) (coherentImage (ξ j) (ν j) l) = 0 :=
  cfInner_coherentImage_coherentImage_eq_zero (hfam i) (hfam j) (hdisj hij) k l

theorem cfInner_coherentSum_coherentSum_eq_zero_of_ne [∀ i, Fintype (ι i)]
    (hfam : ∀ i, IsFullCoherentFamily (ξ i) (τ i) (ν i) (D i))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) {i j : I} (hij : i ≠ j) (e : I → ℂ) :
    cfInner (coherentSum (ξ i) (ν i) (e i)) (coherentSum (ξ j) (ν j) (e j)) = 0 :=
  cfInner_coherentSum_coherentSum_eq_zero (hfam i) (hfam j) (hdisj hij) (e i) (e j)

end Indexed

end DisjointCoherentFamilies

end CFSG.FeitThompson
