module

public import CFSG.FeitThompson.Representations.FrobeniusKernelInductionIrreducible
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
import CFSG.FeitThompson.Representations.ComplementActsFreelyKernelCharacters
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct

theorem eq_irrFinset_of_sum_sq_eq {G : Type*} [Group G] [Finite G] {S : Finset (G → ℂ)}
    (hS : S ⊆ irrFinset G) (hsum : ∑ ξ ∈ S, ξ 1 ^ 2 = (Nat.card G : ℂ)) :
    S = irrFinset G := by
  classical
  refine Finset.Subset.antisymm hS ?_
  have hsplit := Finset.sum_sdiff (f := fun ξ : G → ℂ => ξ 1 ^ 2) hS
  rw [hsum, sum_character_one_sq'] at hsplit
  have hzero : ∑ ξ ∈ irrFinset G \ S, ξ 1 ^ 2 = 0 := by linear_combination hsplit
  have hre : ∑ ξ ∈ irrFinset G \ S, (ξ 1 ^ 2).re = 0 := by
    rw [← Complex.re_sum, hzero, Complex.zero_re]
  have hpos : ∀ ξ ∈ irrFinset G \ S, (1 : ℝ) ≤ (ξ 1 ^ 2).re := by
    intro ξ hξ
    obtain ⟨n, hn, hn1, -⟩ := Irr.exists_degree (mem_irrFinset.1 (Finset.mem_sdiff.1 hξ).1)
    rw [hn1, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hempty : irrFinset G \ S = ∅ := by
    by_contra hne
    obtain ⟨ξ, hξ⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have h0 : (ξ 1 ^ 2).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun η hη => le_trans zero_le_one (hpos η hη)).1 hre ξ hξ
    have := hpos ξ hξ
    rw [h0] at this
    linarith
  intro ξ hξ
  by_contra h
  exact absurd (Finset.mem_sdiff.2 ⟨hξ, h⟩) (by simp [hempty])

theorem finite_Irr_diff_one {G : Type*} [Group G] [Finite G] :
    (Irr G \ {1} : Set (G → ℂ)).Finite :=
  (finite_Irr (G := G)).subset Set.sdiff_subset

noncomputable def irrNonprincipalFinset (G : Type*) [Group G] [Finite G] : Finset (G → ℂ) :=
  finite_Irr_diff_one.toFinset

@[simp] theorem mem_irrNonprincipalFinset {G : Type*} [Group G] [Finite G] {θ : G → ℂ} :
    θ ∈ irrNonprincipalFinset G ↔ θ ∈ Irr G ∧ θ ≠ 1 := by
  simp [irrNonprincipalFinset]

@[simp] theorem coe_irrNonprincipalFinset {G : Type*} [Group G] [Finite G] :
    (irrNonprincipalFinset G : Set (G → ℂ)) = Irr G \ {1} := by
  ext θ; simp

theorem sum_sq_irrNonprincipalFinset {G : Type*} [Group G] [Finite G] :
    ∑ θ ∈ irrNonprincipalFinset G, θ 1 ^ 2 = (Nat.card G : ℂ) - 1 := by
  classical
  have hsub : irrNonprincipalFinset G = (irrFinset G).erase 1 := by
    ext θ; simp [Finset.mem_erase, and_comm]
  have h := Finset.sum_erase_add (irrFinset G) (fun θ : G → ℂ => θ 1 ^ 2)
    (mem_irrFinset.2 (one_mem_Irr (G := G)))
  rw [sum_character_one_sq'] at h
  have h1 : ((1 : G → ℂ) 1) ^ 2 = 1 := by norm_num
  rw [h1] at h
  rw [hsub]
  linear_combination h

variable {H E : Type*} [Group H] [Group E] {φ : E →* MulAut H}

theorem comp_mem_Irr {θ : H → ℂ} (hθ : θ ∈ Irr H) (u : E) : θ ∘ (φ u) ∈ Irr H := by
  have := (irrAut (φ u) ⟨θ, hθ⟩).2
  rwa [coe_irrAut_apply] at this

theorem comp_ne_one {θ : H → ℂ} (hθ1 : θ ≠ 1) (u : E) : θ ∘ (φ u) ≠ 1 := fun h =>
  hθ1 (funext fun y => by simpa using congrFun h ((φ u).symm y))

theorem comp_injective [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {ψ : H → ℂ}
    (hψ : ψ ∈ Irr H) (hψ1 : ψ ≠ 1) :
    Function.Injective (fun u : E => ψ ∘ (φ u)) := by
  intro u v huv
  have h : ∀ y : H, ψ (φ (u * v⁻¹) y) = ψ y := fun y => by
    simpa [map_mul] using congrFun huv ((φ v).symm y)
  have := eq_one_of_comp_eq_self_of_ne_one hφ hψ hψ1 h
  rwa [mul_inv_eq_one] at this

def inflFam (φ : E →* MulAut H) : Set (H ⋊[φ] E → ℂ) :=
  (fun χ : E → ℂ => χ ∘ (rightHom : H ⋊[φ] E → E)) '' Irr E

theorem mem_inflFam {ξ : H ⋊[φ] E → ℂ} :
    ξ ∈ inflFam φ ↔ ∃ χ ∈ Irr E, χ ∘ (rightHom : H ⋊[φ] E → E) = ξ := Iff.rfl

theorem inflFam_subset_Irr : inflFam φ ⊆ Irr (H ⋊[φ] E) := by
  rintro ξ ⟨χ, hχ, rfl⟩
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hχ
  have hirr : Representation.IsIrreducible
      (V.ρ.comp (rightHom : H ⋊[φ] E →* E) : Representation ℂ (H ⋊[φ] E) V) :=
    (Representation.isIrreducible_comp_iff V.ρ rightHom_surjective).2 hV
  have := character_mem_Irr_of_isIrreducible _ hirr
  rwa [Representation.character_comp, ← fdRepCharacter_eq] at this

theorem resClassFun_of_mem_inflFam {ξ : H ⋊[φ] E → ℂ} (hξ : ξ ∈ inflFam φ) :
    resClassFun (inl : H →* H ⋊[φ] E).range ξ
      = ξ 1 • (1 : (inl : H →* H ⋊[φ] E).range → ℂ) := by
  obtain ⟨χ, hχ, rfl⟩ := hξ
  funext x
  obtain ⟨y, hy⟩ := x.2
  simp only [resClassFun_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
    Function.comp_apply]
  rw [← hy]
  simp

noncomputable def rightHomQuotientEquiv (φ : E →* MulAut H) :
    (H ⋊[φ] E) ⧸ (inl : H →* H ⋊[φ] E).range ≃* E :=
  (QuotientGroup.quotientMulEquivOfEq range_inl_eq_ker_rightHom).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ rightHom_surjective)

@[simp] theorem rightHomQuotientEquiv_mk (l : H ⋊[φ] E) :
    rightHomQuotientEquiv φ (QuotientGroup.mk l) = rightHom l := (rfl)

theorem inflFam_eq_irrTrivialOn [Finite H] [Finite E] :
    inflFam φ = irrTrivialOn (inl : H →* H ⋊[φ] E).range := by
  ext ξ
  refine ⟨fun hξ => mem_irrTrivialOn.2 ⟨inflFam_subset_Irr hξ, fun n hn => ?_⟩, fun hξ => ?_⟩
  · obtain ⟨χ, hχ, rfl⟩ := hξ
    obtain ⟨y, rfl⟩ := hn
    simp
  · obtain ⟨ψ, hψ, rfl⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn hξ
    refine mem_inflFam.2 ⟨ψ ∘ (rightHomQuotientEquiv φ).symm, ?_, ?_⟩
    · have h : ψ ∈ NormalInduction.irrChars ((H ⋊[φ] E) ⧸ (inl : H →* H ⋊[φ] E).range) := by
        rw [normalInduction_irrChars_eq_Irr]; exact hψ
      have := NormalInduction.mem_irrChars_comp_mulEquiv h (rightHomQuotientEquiv φ).symm
      rwa [normalInduction_irrChars_eq_Irr] at this
    · funext l
      simp only [Function.comp_apply]
      congr 1
      exact ((rightHomQuotientEquiv φ).symm_apply_eq).2 (rightHomQuotientEquiv_mk l).symm

theorem finite_inflFam [Finite E] : (inflFam (H := H) φ).Finite := finite_Irr.image _

noncomputable def inflFinset (φ : E →* MulAut H) [Finite E] : Finset (H ⋊[φ] E → ℂ) :=
  finite_inflFam.toFinset

@[simp] theorem mem_inflFinset [Finite E] {ξ : H ⋊[φ] E → ℂ} :
    ξ ∈ inflFinset φ ↔ ξ ∈ inflFam φ := Set.Finite.mem_toFinset _

@[simp] theorem coe_inflFinset [Finite E] :
    (inflFinset φ : Set (H ⋊[φ] E → ℂ)) = inflFam φ := Set.Finite.coe_toFinset _

theorem sum_sq_inflFinset [Finite E] :
    ∑ ξ ∈ inflFinset (H := H) φ, ξ 1 ^ 2 = (Nat.card E : ℂ) := by
  classical
  rw [← sum_character_one_sq' (G := E)]
  refine (Finset.sum_bij (fun χ _ => χ ∘ (rightHom : H ⋊[φ] E → E)) ?_ ?_ ?_ ?_).symm
  · intro χ hχ
    exact mem_inflFinset.2 ⟨χ, mem_irrFinset.1 hχ, rfl⟩
  · intro χ₁ _ χ₂ _ h
    funext u
    obtain ⟨l, hl⟩ := rightHom_surjective (φ := φ) u
    rw [← hl]
    exact congrFun h l
  · intro ξ hξ
    obtain ⟨χ, hχ, rfl⟩ := mem_inflFinset.1 hξ
    exact ⟨χ, mem_irrFinset.2 hχ, rfl⟩
  · intro χ _
    simp

variable [Fintype H] [Fintype E]

noncomputable def indKernelFam (φ : E →* MulAut H) : Set (H ⋊[φ] E → ℂ) :=
  (fun θ : H → ℂ => indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ)) ''
    (Irr H \ {1})

theorem mem_indKernelFam {ξ : H ⋊[φ] E → ℂ} :
    ξ ∈ indKernelFam φ ↔ ∃ θ ∈ Irr H, θ ≠ 1 ∧
      indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ) = ξ := by
  simp only [indKernelFam, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
  exact ⟨fun ⟨θ, ⟨hθ, hθ1⟩, h⟩ => ⟨θ, hθ, hθ1, h⟩, fun ⟨θ, hθ, hθ1, h⟩ => ⟨θ, ⟨hθ, hθ1⟩, h⟩⟩

noncomputable def indKernelFinset (φ : E →* MulAut H) : Finset (H ⋊[φ] E → ℂ) :=
  (irrNonprincipalFinset H).image
    (fun θ : H → ℂ => indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ))

theorem mem_indKernelFinset {ξ : H ⋊[φ] E → ℂ} :
    ξ ∈ indKernelFinset φ ↔ ∃ θ ∈ Irr H, θ ≠ 1 ∧
      indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ) = ξ := by
  classical
  simp only [indKernelFinset, Finset.mem_image, mem_irrNonprincipalFinset]
  constructor
  · rintro ⟨θ, ⟨hθ, hθ1⟩, rfl⟩; exact ⟨θ, hθ, hθ1, rfl⟩
  · rintro ⟨θ, hθ, hθ1, rfl⟩; exact ⟨θ, ⟨hθ, hθ1⟩, rfl⟩

@[simp] theorem coe_indKernelFinset :
    (indKernelFinset φ : Set (H ⋊[φ] E → ℂ)) = indKernelFam φ := by
  ext ξ
  rw [Finset.mem_coe, mem_indKernelFinset, mem_indKernelFam]

theorem indKernelFam_subset_Irr [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) :
    indKernelFam φ ⊆ Irr (H ⋊[φ] E) := by
  intro ξ hξ
  obtain ⟨θ, hθ, hθ1, rfl⟩ := mem_indKernelFam.1 hξ
  exact indClassFun_kernelClassFun_mem_Irr hφ hθ hθ1

omit [Fintype H] [Fintype E] in
theorem kernelClassFun_ne_one {θ : H → ℂ} (hθ1 : θ ≠ 1) : kernelClassFun φ θ ≠ 1 := by
  intro h
  refine hθ1 (kernelClassFun_injective (φ := φ) ?_)
  rw [h]
  funext x
  simp

theorem cfInner_eq_zero_of_mem_indKernelFam_of_mem_inflFam {ξ η : H ⋊[φ] E → ℂ}
    (hξ : ξ ∈ indKernelFam φ) (hη : η ∈ inflFam φ) : cfInner ξ η = 0 := by
  obtain ⟨θ, hθ, hθ1, rfl⟩ := mem_indKernelFam.1 hξ
  have _ : Fintype ((inl : H →* H ⋊[φ] E).range) := Fintype.ofFinite _
  rw [cfInner_indClassFun _ _ (Irr_subset_classFun (inflFam_subset_Irr hη)),
    resClassFun_of_mem_inflFam hη, cfInner_smul_right,
    cfInner_eq_zero_of_mem_Irr (kernelClassFun_mem_Irr hθ) one_mem_Irr
      (kernelClassFun_ne_one hθ1), mul_zero]

theorem disjoint_inflFam_indKernelFam [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) :
    Disjoint (inflFam φ) (indKernelFam φ) := by
  rw [Set.disjoint_right]
  intro ξ hξ hinfl
  have h0 := cfInner_eq_zero_of_mem_indKernelFam_of_mem_inflFam hξ hinfl
  obtain ⟨θ, hθ, hθ1, rfl⟩ := mem_indKernelFam.1 hξ
  rw [cfInner_self_indClassFun_kernelClassFun hφ hθ hθ1] at h0
  exact one_ne_zero h0

theorem card_fiber_indKernel [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) :
    {θ' ∈ irrNonprincipalFinset H |
        indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ')
          = indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ)}.card
      = Nat.card E := by
  classical
  have himg : {θ' ∈ irrNonprincipalFinset H |
      indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ')
        = indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ)}
      = Finset.image (fun u : E => θ ∘ (φ u)) Finset.univ := by
    ext θ'
    simp only [Finset.mem_filter, mem_irrNonprincipalFinset, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨hθ', hθ'1⟩, heq⟩
      exact (indClassFun_kernelClassFun_eq_iff hθ' hθ).1 heq
    · rintro ⟨u, rfl⟩
      refine ⟨⟨comp_mem_Irr hθ u, comp_ne_one hθ1 u⟩, ?_⟩
      exact (indClassFun_kernelClassFun_eq_iff (comp_mem_Irr hθ u) hθ).2 ⟨u, rfl⟩
  rw [himg, Finset.card_image_of_injective _ (comp_injective hφ hθ hθ1), Finset.card_univ,
    Nat.card_eq_fintype_card]

theorem sum_sq_indKernelFinset [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) :
    ∑ ξ ∈ indKernelFinset φ, ξ 1 ^ 2 = (Nat.card E : ℂ) * ((Nat.card H : ℂ) - 1) := by
  classical
  set g : (H → ℂ) → (H ⋊[φ] E → ℂ) :=
    fun θ => indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ) with hg
  have hEne : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hcomp := Finset.sum_comp (s := irrNonprincipalFinset H)
    (fun ξ : H ⋊[φ] E → ℂ => ξ 1 ^ 2) g
  have hL : ∑ θ ∈ irrNonprincipalFinset H, (g θ) 1 ^ 2
      = (Nat.card E : ℂ) ^ 2 * ((Nat.card H : ℂ) - 1) := by
    rw [← sum_sq_irrNonprincipalFinset (G := H), Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hg]
    simp only
    rw [indClassFun_kernelClassFun_one]
    ring
  have hR : ∑ ξ ∈ Finset.image g (irrNonprincipalFinset H),
      {θ' ∈ irrNonprincipalFinset H | g θ' = ξ}.card • ξ 1 ^ 2
      = (Nat.card E : ℂ) * ∑ ξ ∈ indKernelFinset φ, ξ 1 ^ 2 := by
    rw [show Finset.image g (irrNonprincipalFinset H) = indKernelFinset φ from rfl,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    obtain ⟨θ, hθ, hθ1, rfl⟩ := mem_indKernelFinset.1 hξ
    rw [show ({θ' ∈ irrNonprincipalFinset H | g θ' = g θ}.card) = Nat.card E from
      card_fiber_indKernel hφ hθ hθ1, nsmul_eq_mul]
  rw [hL, hR] at hcomp
  field_simp at hcomp
  exact hcomp.symm

theorem irrFinset_eq_union [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) :
    inflFinset (H := H) φ ∪ indKernelFinset φ = irrFinset (H ⋊[φ] E) := by
  classical
  have hdisj : Disjoint (inflFinset (H := H) φ) (indKernelFinset φ) := by
    rw [← Finset.disjoint_coe, coe_inflFinset, coe_indKernelFinset]
    exact disjoint_inflFam_indKernelFam hφ
  refine eq_irrFinset_of_sum_sq_eq ?_ ?_
  · intro ξ hξ
    rcases Finset.mem_union.1 hξ with h | h
    · exact mem_irrFinset.2 (inflFam_subset_Irr (mem_inflFinset.1 h))
    · exact mem_irrFinset.2 (indKernelFam_subset_Irr hφ
        (by rw [← coe_indKernelFinset]; exact h))
  · rw [Finset.sum_union hdisj, sum_sq_inflFinset, sum_sq_indKernelFinset hφ,
      SemidirectProduct.card]
    push_cast
    ring

theorem Irr_eq_union [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) :
    Irr (H ⋊[φ] E) = inflFam φ ∪ indKernelFam φ := by
  have h := irrFinset_eq_union hφ
  ext ξ
  rw [← mem_irrFinset, ← h, Finset.mem_union, mem_inflFinset,
    show ξ ∈ indKernelFinset φ ↔ ξ ∈ indKernelFam φ from
      (mem_indKernelFinset).trans (mem_indKernelFam).symm, Set.mem_union]

end CFSG.FeitThompson
