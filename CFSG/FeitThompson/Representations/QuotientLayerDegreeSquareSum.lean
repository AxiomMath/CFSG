module

public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import CFSG.FeitThompson.Representations.MultiplicityFreeBlockAgreeOnCore
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Representations.AbelianPointStabilizersCharacterStabilizers
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsCentralizers
public import Mathlib.GroupTheory.Nilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInduction (conjClassFun conjClassFun_apply)
open scoped Pointwise

variable {L : Type*} [Group L]

theorem eq_one_of_mem_Irr_of_forall_apply_eq {K : Type*} [Group K] [Finite K] {θ : K → ℂ}
    (hθ : θ ∈ Irr K) (hconst : ∀ k : K, θ k = θ 1) : θ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨d, -, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hθ
  have hself : cfInner θ θ = 1 := cfInner_self_of_mem_Irr hθ
  rw [cfInner_def] at hself
  have hsum : ∀ g : K, θ g * (starRingEnd ℂ) (θ g) = (d : ℂ) * (d : ℂ) := fun g => by
    rw [hconst g, hd1, Complex.conj_natCast]
  rw [Finset.sum_congr rfl fun g _ => hsum g, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := K)), one_mul] at hself
  have hd' : d = 1 := Nat.eq_one_of_mul_eq_one_right (by exact_mod_cast hself)
  funext g
  rw [hconst g, hd1, hd']
  simp

theorem conjClassFun_eq_iff_mem_inertiaGroup (H : Subgroup L) [H.Normal] (θ : H → ℂ) (s t : L) :
    conjClassFun H t θ = conjClassFun H s θ ↔ s⁻¹ * t ∈ inertiaGroup H θ := by
  rw [mem_inertiaGroup]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [conjClassFun_mul, h, ← conjClassFun_mul, inv_mul_cancel, conjClassFun_one]
  · have := congrArg (conjClassFun H s) h
    rwa [← conjClassFun_mul, mul_inv_cancel_left] at this

@[simp] theorem conjClassFun_apply_one (H : Subgroup L) [H.Normal] (t : L) (θ : H → ℂ) :
    conjClassFun H t θ 1 = θ 1 := by rw [conjClassFun_apply, map_one]

theorem conjClassFun_ne_one (H : Subgroup L) [H.Normal] {θ : H → ℂ} (hne : θ ≠ 1) (t : L) :
    conjClassFun H t θ ≠ 1 := fun h => hne (by
  have := congrArg (conjClassFun H t⁻¹) h
  rwa [← conjClassFun_mul, inv_mul_cancel, conjClassFun_one,
    NormalInducedFamily.conjClassFun_one_right] at this)

theorem inertiaGroup_eq_of_ne_one [Finite L] {H E : Subgroup L} [H.Normal]
    (hHE : H.IsComplement' E) (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    {θ : H → ℂ} (hθ : θ ∈ Irr H) (hne : θ ≠ 1) : inertiaGroup H θ = H := by
  refine le_antisymm ?_ (le_inertiaGroup H (Irr_subset_classFun hθ))
  have hCH : ∀ h ∈ H, h ≠ 1 → (⊤ : Subgroup L) ⊓ Subgroup.centralizer {h} ≤ H := fun h hh hne1 =>
    le_trans inf_le_right (centralizer_singleton_le_of_mem_of_ne_one hHE hC hh hne1)
  simpa using inf_inertiaGroup_le_of_centralizer_le (U := ⊤) (U₁ := H) hCH hθ hne

theorem finite_nonprincipalIrrTrivialOn (H A : Subgroup L) [Finite L] :
    (irrTrivialOn (A.subgroupOf H) \ {1}).Finite :=
  finite_irrTrivialOn.subset Set.sdiff_subset

variable [Fintype L] {H A E : Subgroup L}

theorem card_conjOrbit (H : Subgroup L) [H.Normal] (θ : H → ℂ) :
    (NormalInduction.conjOrbit H θ).card = (inertiaGroup H θ).index := by
  classical
  set I := inertiaGroup H θ with hI
  set F : L ⧸ I → (H → ℂ) := fun q => Quotient.liftOn' q (fun t => conjClassFun H t θ)
    (fun a b hab => ((conjClassFun_eq_iff_mem_inertiaGroup H θ a b).2
      (QuotientGroup.leftRel_apply.1 hab)).symm) with hF
  have hFmk : ∀ t : L, F (QuotientGroup.mk t) = conjClassFun H t θ := fun _ => rfl
  have hFinj : Function.Injective F := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | _ a =>
      induction q₂ using QuotientGroup.induction_on with
      | _ b =>
        rw [hFmk, hFmk] at h
        exact QuotientGroup.eq.2 ((conjClassFun_eq_iff_mem_inertiaGroup H θ a b).1 h.symm)
  have hrange : Set.range F = ↑(NormalInduction.conjOrbit H θ) := by
    ext f
    refine ⟨?_, fun hf => ?_⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | _ a => exact NormalInduction.conjClassFun_mem_conjOrbit θ a
    · obtain ⟨t, ht⟩ := NormalInduction.mem_conjOrbit.1 hf
      exact ⟨QuotientGroup.mk t, ht⟩
  have h1 : Nat.card (Set.range F) = Nat.card (L ⧸ I) :=
    (Nat.card_congr (Equiv.ofInjective F hFinj)).symm
  rw [hrange] at h1
  rw [Subgroup.index_eq_card, ← h1, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem card_conjOrbit_eq_index [H.Normal] (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    {θ : H → ℂ} (hθ : θ ∈ Irr H) (hne : θ ≠ 1) :
    (NormalInduction.conjOrbit H θ).card = H.index := by
  rw [card_conjOrbit, inertiaGroup_eq_of_ne_one hHE hC hθ hne]

theorem indClassFun_mem_Irr_of_ne_one [H.Normal] (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    {θ : H → ℂ} (hθ : θ ∈ Irr H) (hne : θ ≠ 1) : indClassFun H θ ∈ Irr L := by
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam H
    (indClassFun_mem_indFam H hθ)
  refine mem_Irr.2 ⟨W, ?_, hW⟩
  rw [isIrreducible_iff_cfInner_self_eq_one, ← fdRepCharacter_eq W, hW,
    cfInner_self_indClassFun H hθ, inertiaGroup_eq_of_ne_one hHE hC hθ hne,
    Subgroup.relIndex_self]
  simp

noncomputable def frobeniusLayerSource (H A : Subgroup L) : Finset (H → ℂ) :=
  (finite_nonprincipalIrrTrivialOn H A).toFinset

@[simp] theorem mem_frobeniusLayerSource {θ : H → ℂ} :
    θ ∈ frobeniusLayerSource H A ↔
      θ ∈ Irr H ∧ θ ≠ 1 ∧ ∀ a ∈ A.subgroupOf H, θ a = θ 1 := by
  rw [frobeniusLayerSource, Set.Finite.mem_toFinset]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, mem_irrTrivialOn]
  tauto

theorem frobeniusLayerSource_subset_Irr : ↑(frobeniusLayerSource H A) ⊆ Irr H :=
  fun _ hθ => (mem_frobeniusLayerSource.1 hθ).1

theorem sum_sq_degree_frobeniusLayerSource [A.Normal] :
    ∑ θ ∈ frobeniusLayerSource H A, θ 1 ^ 2 = (A.relIndex H : ℂ) - 1 := by
  classical
  have : (A.subgroupOf H).Normal := ‹A.Normal›.subgroupOf H
  have h1mem : (1 : H → ℂ) ∈ irrTrivialOnFinset (A.subgroupOf H) :=
    mem_irrTrivialOnFinset.2 (mem_irrTrivialOn.2 ⟨one_mem_Irr, fun _ _ => rfl⟩)
  have hEq : frobeniusLayerSource H A = (irrTrivialOnFinset (A.subgroupOf H)).erase 1 := by
    ext θ
    rw [Finset.mem_erase, mem_irrTrivialOnFinset, mem_frobeniusLayerSource, mem_irrTrivialOn]
    tauto
  rw [hEq, Finset.sum_erase_eq_sub h1mem, sum_sq_degree_irrTrivialOn_eq_index,
    Subgroup.relIndex]
  norm_num

open scoped Classical in
noncomputable def frobeniusLayer (H A : Subgroup L) : Finset (L → ℂ) :=
  (frobeniusLayerSource H A).image (indClassFun H)

theorem mem_frobeniusLayer {f : L → ℂ} :
    f ∈ frobeniusLayer H A ↔ ∃ θ ∈ frobeniusLayerSource H A, indClassFun H θ = f := by
  classical
  rw [frobeniusLayer, Finset.mem_image]

theorem indClassFun_mem_frobeniusLayer {θ : H → ℂ} (hθ : θ ∈ frobeniusLayerSource H A) :
    indClassFun H θ ∈ frobeniusLayer H A :=
  mem_frobeniusLayer.2 ⟨θ, hθ, rfl⟩

theorem conjOrbit_subset_frobeniusLayerSource [H.Normal] [A.Normal]
    {θ : H → ℂ} (hθ : θ ∈ frobeniusLayerSource H A) :
    NormalInduction.conjOrbit H θ ⊆ frobeniusLayerSource H A := by
  intro θ' hθ'
  obtain ⟨t, rfl⟩ := NormalInduction.mem_conjOrbit.1 hθ'
  obtain ⟨hirr, hne, hker⟩ := mem_frobeniusLayerSource.1 hθ
  refine mem_frobeniusLayerSource.2
    ⟨conjClassFun_mem_Irr H t hirr, conjClassFun_ne_one H hne t, fun a ha => ?_⟩
  rw [conjClassFun_apply, conjClassFun_apply, map_one]
  refine hker _ ?_
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  rw [MulAut.conjNormal_apply]
  simpa using ‹A.Normal›.conj_mem _ ha t⁻¹

theorem filter_indClassFun_eq_conjOrbit [H.Normal] [A.Normal]
    {θ : H → ℂ} (hθ : θ ∈ frobeniusLayerSource H A) :
    {θ' ∈ frobeniusLayerSource H A | indClassFun H θ' = indClassFun H θ}
      = NormalInduction.conjOrbit H θ := by
  classical
  ext θ'
  rw [Finset.mem_filter]
  refine ⟨fun ⟨hθ', heq⟩ => NormalInduction.mem_conjOrbit.2
      ((NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun H
        (mem_frobeniusLayerSource.1 hθ').1 (mem_frobeniusLayerSource.1 hθ).1).1 heq), fun hθ' => ?_⟩
  refine ⟨conjOrbit_subset_frobeniusLayerSource hθ hθ', ?_⟩
  obtain ⟨t, rfl⟩ := NormalInduction.mem_conjOrbit.1 hθ'
  exact NormalInducedFamily.indClassFun_conjClassFun H t θ

theorem frobeniusLayer_subset_Irr [H.Normal] (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    ↑(frobeniusLayer H A) ⊆ Irr L := by
  intro χ hχ
  obtain ⟨θ, hθ, rfl⟩ := mem_frobeniusLayer.1 hχ
  obtain ⟨hirr, hne, -⟩ := mem_frobeniusLayerSource.1 hθ
  exact indClassFun_mem_Irr_of_ne_one hHE hC hirr hne

theorem exists_degree_eq_index_mul {χ : L → ℂ} (hχ : χ ∈ frobeniusLayer H A) :
    ∃ d : ℕ, 0 < d ∧ χ 1 = (H.index : ℂ) * (d : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := mem_frobeniusLayer.1 hχ
  obtain ⟨hirr, -, -⟩ := mem_frobeniusLayerSource.1 hθ
  obtain ⟨d, hd, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hirr
  exact ⟨d, hd, by rw [NormalInducedFamily.indClassFun_one_eq_index_mul, hd1]⟩

theorem sum_sq_degree_frobeniusLayer [H.Normal] [A.Normal] (hHE : H.IsComplement' E)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    ∑ χ ∈ frobeniusLayer H A, χ 1 ^ 2 = (H.index : ℂ) * ((A.relIndex H : ℂ) - 1) := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have key : ∀ θ ∈ frobeniusLayerSource H A, (indClassFun H θ) 1 ^ 2
      = ∑ θ' ∈ {θ' ∈ frobeniusLayerSource H A | indClassFun H θ' = indClassFun H θ},
          (H.index : ℂ) * θ' 1 ^ 2 := by
    intro θ hθ
    obtain ⟨hirr, hne, -⟩ := mem_frobeniusLayerSource.1 hθ
    rw [filter_indClassFun_eq_conjOrbit hθ]
    have hconst : ∀ θ' ∈ NormalInduction.conjOrbit H θ,
        (H.index : ℂ) * θ' 1 ^ 2 = (H.index : ℂ) * θ 1 ^ 2 := by
      intro θ' hθ'
      obtain ⟨t, rfl⟩ := NormalInduction.mem_conjOrbit.1 hθ'
      rw [conjClassFun_apply_one]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_conjOrbit_eq_index hHE hC hirr hne,
      nsmul_eq_mul, NormalInducedFamily.indClassFun_one_eq_index_mul]
    ring
  rw [frobeniusLayer, Finset.sum_image' _ key, ← Finset.mul_sum,
    sum_sq_degree_frobeniusLayerSource]

theorem frobeniusLayer_self_eq_empty : frobeniusLayer H H = ∅ := by
  classical
  have hsrc : frobeniusLayerSource H H = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun θ hθ => ?_
    obtain ⟨hirr, hne, hker⟩ := mem_frobeniusLayerSource.1 hθ
    have : Fintype H := Fintype.ofFinite H
    refine hne (eq_one_of_mem_Irr_of_forall_apply_eq hirr fun x => hker x ?_)
    rw [Subgroup.mem_subgroupOf]
    exact x.2
  rw [frobeniusLayer, hsrc, Finset.image_empty]

theorem sum_sq_degree_frobeniusLayer_self : ∑ χ ∈ frobeniusLayer H H, χ 1 ^ 2 = 0 := by
  rw [frobeniusLayer_self_eq_empty, Finset.sum_empty]

theorem sum_sq_degree_frobeniusLayer_of_frobeniusDecomposition [H.Normal] [A.Normal]
    (_hodd : Odd (Nat.card L)) (_hH : H ≠ ⊥) (_hE : E ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hdisj : H ⊓ E = ⊥)
    (_hnil : Group.IsNilpotent H)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) (_hAH : A ≤ H) :
    H.index = Nat.card E ∧ ↑(frobeniusLayer H A) ⊆ Irr L ∧
      (∀ χ ∈ frobeniusLayer H A, ∃ d : ℕ, 0 < d ∧ χ 1 = (Nat.card E : ℂ) * (d : ℂ)) ∧
      ∑ χ ∈ frobeniusLayer H A, χ 1 ^ 2 = (Nat.card E : ℂ) * ((A.relIndex H : ℂ) - 1) := by
  have hHE : H.IsComplement' E :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hdisj) hmul
  have hidx : H.index = Nat.card E := (Subgroup.isComplement'_comm.1 hHE).index_eq_card
  refine ⟨hidx, frobeniusLayer_subset_Irr hHE hC, fun χ hχ => ?_, ?_⟩
  · obtain ⟨d, hd, hd1⟩ := exists_degree_eq_index_mul hχ
    exact ⟨d, hd, by rwa [hidx] at hd1⟩
  · rw [sum_sq_degree_frobeniusLayer hHE hC, hidx]

end CFSG.FeitThompson
