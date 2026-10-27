module

public import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.FrobeniusSemidirectIrrCharacterList

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FrobeniusInduction

open SemidirectProduct

instance instFiniteSemidirectProduct {N H : Type*} [Group N] [Group H] {ψ : H →* MulAut N}
    [Finite N] [Finite H] : Finite (N ⋊[ψ] H) :=
  Finite.of_equiv _ (equivProd (φ := ψ)).symm

variable {P U : Type*} [CommGroup P] [CommGroup U] {φ : U →* MulAut P}

theorem mem_Irr_comp_of_surjective {G Q : Type*} [Group G] [Group Q] {f : G →* Q}
    (hf : Function.Surjective f) {χ : Q → ℂ} (hχ : χ ∈ Irr Q) : χ ∘ f ∈ Irr G := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hχ
  have hirr : Representation.IsIrreducible (W.ρ.comp f : Representation ℂ G W.V) :=
    (Representation.isIrreducible_comp_iff W.ρ hf).2 hW
  have hchar : Representation.character (W.ρ.comp f : Representation ℂ G W.V)
      = FDRep.character W ∘ f := by
    funext g
    rw [fdRepCharacter_eq]
    rfl
  rw [← hchar]
  exact character_mem_Irr_of_isIrreducible _ hirr

noncomputable def quotientRangeInlEquiv (φ : U →* MulAut P) :
    (P ⋊[φ] U) ⧸ (inl : P →* P ⋊[φ] U).range ≃* U :=
  (QuotientGroup.quotientMulEquivOfEq (range_inl_eq_ker_rightHom (φ := φ))).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ rightHom_surjective)

@[simp] theorem quotientRangeInlEquiv_mk (x : P ⋊[φ] U) :
    quotientRangeInlEquiv φ (QuotientGroup.mk x) = x.right := (rfl)

def inflatedIrr (φ : U →* MulAut P) : Set (P ⋊[φ] U → ℂ) :=
  (fun χ : U → ℂ => χ ∘ (rightHom : P ⋊[φ] U →* U)) '' Irr U

theorem mem_inflatedIrr {f : P ⋊[φ] U → ℂ} :
    f ∈ inflatedIrr φ ↔ ∃ χ ∈ Irr U, χ ∘ (rightHom : P ⋊[φ] U →* U) = f := Iff.rfl

theorem comp_rightHom_mem_inflatedIrr {χ : U → ℂ} (hχ : χ ∈ Irr U) :
    χ ∘ (rightHom : P ⋊[φ] U →* U) ∈ inflatedIrr φ := ⟨χ, hχ, rfl⟩

theorem comp_quotientRangeInlEquiv_comp_mk (χ : U → ℂ) :
    (χ ∘ quotientRangeInlEquiv φ) ∘ (QuotientGroup.mk : P ⋊[φ] U → _)
      = χ ∘ (rightHom : P ⋊[φ] U →* U) := (rfl)

theorem inflatedIrr_subset_Irr : inflatedIrr φ ⊆ Irr (P ⋊[φ] U) := by
  rintro f ⟨χ, hχ, rfl⟩
  exact mem_Irr_comp_of_surjective rightHom_surjective hχ

theorem apply_one_of_mem_inflatedIrr {f : P ⋊[φ] U → ℂ} (hf : f ∈ inflatedIrr φ) : f 1 = 1 := by
  obtain ⟨χ, hχ, rfl⟩ := hf
  change χ (rightHom (1 : P ⋊[φ] U)) = 1
  rw [map_one, Irr.apply_one_eq_one hχ]

theorem resClassFun_of_mem_inflatedIrr {f : P ⋊[φ] U → ℂ} (hf : f ∈ inflatedIrr φ) :
    resClassFun (inl : P →* P ⋊[φ] U).range f = 1 := by
  obtain ⟨χ, hχ, rfl⟩ := hf
  funext n
  rw [resClassFun_apply, Pi.one_apply]
  change χ (rightHom (n : P ⋊[φ] U)) = 1
  rw [rightHom_eq_right, mem_range_inl_iff.1 n.2, Irr.apply_one_eq_one hχ]

section Finite

variable [Finite P] [Finite U]

theorem inflatedIrr_eq_irrTrivialOn :
    inflatedIrr φ = irrTrivialOn (inl : P →* P ⋊[φ] U).range := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro f hf
    refine mem_irrTrivialOn.2 ⟨inflatedIrr_subset_Irr hf, fun n hn => ?_⟩
    obtain ⟨χ, hχ, rfl⟩ := hf
    change χ (rightHom n) = χ (rightHom (1 : P ⋊[φ] U))
    rw [map_one, rightHom_eq_right, mem_range_inl_iff.1 hn]
  · intro χ hχ
    obtain ⟨ψ, hψ, rfl⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn hχ
    refine ⟨ψ ∘ (quotientRangeInlEquiv φ).symm,
      mem_Irr_comp_mulEquiv hψ (quotientRangeInlEquiv φ).symm, ?_⟩
    funext x
    change ψ ((quotientRangeInlEquiv φ).symm (rightHom x)) = ψ (QuotientGroup.mk x)
    congr 1
    exact (quotientRangeInlEquiv φ).symm_apply_eq.2 (quotientRangeInlEquiv_mk x).symm

theorem finite_inflatedIrr : (inflatedIrr φ).Finite := finite_Irr.image _

noncomputable def inflatedIrrFinset (φ : U →* MulAut P) : Finset (P ⋊[φ] U → ℂ) :=
  finite_inflatedIrr.toFinset

@[simp] theorem mem_inflatedIrrFinset {f : P ⋊[φ] U → ℂ} :
    f ∈ inflatedIrrFinset φ ↔ f ∈ inflatedIrr φ := Set.Finite.mem_toFinset _

theorem inflatedIrrFinset_eq :
    inflatedIrrFinset φ = irrTrivialOnFinset (inl : P →* P ⋊[φ] U).range := by
  ext f
  rw [mem_inflatedIrrFinset, mem_irrTrivialOnFinset, inflatedIrr_eq_irrTrivialOn]

theorem sum_sq_inflatedIrrFinset :
    ∑ f ∈ inflatedIrrFinset φ, f 1 ^ 2 = (Nat.card U : ℂ) := by
  have : Fintype P := Fintype.ofFinite P
  have : Fintype U := Fintype.ofFinite U
  rw [inflatedIrrFinset_eq, sum_sq_degree_irrTrivialOn_eq_index, index_range_inl]

theorem card_inflatedIrrFinset : (inflatedIrrFinset φ).card = Nat.card U := by
  have h := sum_sq_inflatedIrrFinset (φ := φ)
  rw [Finset.sum_congr rfl fun f hf => by
    rw [apply_one_of_mem_inflatedIrr (mem_inflatedIrrFinset.1 hf), one_pow]] at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact Nat.cast_injective (R := ℂ) h

theorem natCard_inflatedIrr : Nat.card (inflatedIrr φ) = Nat.card U := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ finite_inflatedIrr]
  exact card_inflatedIrrFinset

end Finite

theorem kernelChar_one : kernelChar φ (1 : P → ℂ) = 1 := by
  funext n
  simp

theorem kernelChar_ne_one {lam : P → ℂ} (h : lam ≠ 1) : kernelChar φ lam ≠ 1 := fun hc =>
  h (kernelChar_injective (φ := φ) (hc.trans kernelChar_one.symm))

variable [Fintype P] [Fintype U]

noncomputable def frobeniusInducedIrrFinset (φ : U →* MulAut P) : Finset (P ⋊[φ] U → ℂ) :=
  finite_frobeniusInducedIrr.toFinset

@[simp] theorem mem_frobeniusInducedIrrFinset {f : P ⋊[φ] U → ℂ} :
    f ∈ frobeniusInducedIrrFinset φ ↔ f ∈ frobeniusInducedIrr φ := Set.Finite.mem_toFinset _

theorem card_frobeniusInducedIrrFinset :
    (frobeniusInducedIrrFinset φ).card = Nat.card (frobeniusInducedIrr φ) := by
  rw [Nat.card_coe_set_eq, frobeniusInducedIrrFinset,
    Set.ncard_eq_toFinset_card _ finite_frobeniusInducedIrr]

theorem apply_one_of_mem_frobeniusInducedIrr {f : P ⋊[φ] U → ℂ}
    (hf : f ∈ frobeniusInducedIrr φ) : f 1 = (Nat.card U : ℂ) := by
  obtain ⟨lam, hlam, rfl⟩ := mem_frobeniusInducedIrr.1 hf
  exact indClassFun_kernelChar_one (mem_nonprincipalIrr.1 hlam).1

theorem sum_sq_frobeniusInducedIrrFinset
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) :
    ∑ f ∈ frobeniusInducedIrrFinset φ, f 1 ^ 2
      = ((Nat.card P : ℂ) - 1) * (Nat.card U : ℂ) := by
  rw [Finset.sum_congr rfl fun f hf => by
    rw [apply_one_of_mem_frobeniusInducedIrr (mem_frobeniusInducedIrrFinset.1 hf)]]
  rw [Finset.sum_const, nsmul_eq_mul, card_frobeniusInducedIrrFinset, sq, ← mul_assoc,
    ← Nat.cast_mul, natCard_frobeniusInducedIrr_mul_natCard hφ]
  congr 1
  have h1 : 1 ≤ Nat.card P := Nat.card_pos
  push_cast [h1]
  ring

theorem notMem_inflatedIrr_of_mem_frobeniusInducedIrr
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) {f : P ⋊[φ] U → ℂ}
    (hf : f ∈ frobeniusInducedIrr φ) : f ∉ inflatedIrr φ := by
  classical
  have : Fintype ((inl : P →* P ⋊[φ] U).range) := Fintype.ofFinite _
  obtain ⟨lam, hlam, rfl⟩ := mem_frobeniusInducedIrr.1 hf
  obtain ⟨hl, hl1⟩ := mem_nonprincipalIrr.1 hlam
  intro hmem
  have hker : kernelChar φ lam ∈ Irr ((inl : P →* P ⋊[φ] U).range) := kernelChar_mem_Irr hl
  have hχ : indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) ∈ Irr (P ⋊[φ] U) :=
    indClassFun_kernelChar_mem_Irr hφ hl hl1
  have hrec := cfInner_indClassFun_eq_cfInner_resClassFun hχ hker
  rw [resClassFun_of_mem_inflatedIrr hmem,
    cfInner_eq_ite_of_mem_Irr one_mem_Irr hker, if_neg (Ne.symm (kernelChar_ne_one hl1)),
    cfInner_self_indClassFun_kernelChar hφ hl hl1] at hrec
  exact one_ne_zero hrec

theorem disjoint_inflatedIrr_frobeniusInducedIrr
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) :
    Disjoint (inflatedIrr φ) (frobeniusInducedIrr φ) :=
  Set.disjoint_right.2 fun _ hf => notMem_inflatedIrr_of_mem_frobeniusInducedIrr hφ hf

theorem disjoint_inflatedIrrFinset_frobeniusInducedIrrFinset
    (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) :
    Disjoint (inflatedIrrFinset φ) (frobeniusInducedIrrFinset φ) := by
  rw [Finset.disjoint_right]
  intro f hf
  rw [mem_inflatedIrrFinset]
  exact notMem_inflatedIrr_of_mem_frobeniusInducedIrr hφ (mem_frobeniusInducedIrrFinset.1 hf)

theorem Irr_eq_union (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P)) :
    Irr (P ⋊[φ] U) = inflatedIrr φ ∪ frobeniusInducedIrr φ := by
  classical
  have hsub : inflatedIrrFinset φ ∪ frobeniusInducedIrrFinset φ ⊆ irrFinset (P ⋊[φ] U) := by
    intro f hf
    rw [Finset.mem_union] at hf
    rw [mem_irrFinset]
    rcases hf with h | h
    · exact inflatedIrr_subset_Irr (mem_inflatedIrrFinset.1 h)
    · exact frobeniusInducedIrr_subset_Irr hφ (mem_frobeniusInducedIrrFinset.1 h)
  have hsum : ∑ f ∈ inflatedIrrFinset φ ∪ frobeniusInducedIrrFinset φ, f 1 ^ 2
      = (Nat.card (P ⋊[φ] U) : ℂ) := by
    rw [Finset.sum_union (disjoint_inflatedIrrFinset_frobeniusInducedIrrFinset hφ),
      sum_sq_inflatedIrrFinset, sum_sq_frobeniusInducedIrrFinset hφ, SemidirectProduct.card]
    push_cast
    ring
  have heq := eq_irrFinset_of_sum_sq_eq hsub hsum
  ext f
  rw [← mem_irrFinset, ← heq, Finset.mem_union, mem_inflatedIrrFinset,
    mem_frobeniusInducedIrrFinset, Set.mem_union]

theorem mem_Irr_iff (hφ : ∀ v : U, v ≠ 1 → MonoidHom.FixedPointFree (φ v : P → P))
    {f : P ⋊[φ] U → ℂ} :
    f ∈ Irr (P ⋊[φ] U) ↔
      (∃ χ ∈ Irr U, χ ∘ (rightHom : P ⋊[φ] U →* U) = f) ∨
      (∃ lam ∈ nonprincipalIrr P,
        indClassFun (inl : P →* P ⋊[φ] U).range (kernelChar φ lam) = f) := by
  rw [Irr_eq_union hφ, Set.mem_union, mem_inflatedIrr, mem_frobeniusInducedIrr]

end FrobeniusInduction

end CFSG.FeitThompson
