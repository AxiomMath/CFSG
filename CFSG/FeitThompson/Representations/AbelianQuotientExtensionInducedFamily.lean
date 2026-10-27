module

public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Representations.InductionMulRestrictedClassFun
import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace AbelianQuotientExtension

section Abelian

variable {Q : Type*} [Group Q] [IsMulCommutative Q]

theorem exists_monoidHom_units_of_mem_Irr {β : Q → ℂ} (hβ : β ∈ Irr Q) :
    ∃ ψ : Q →* ℂˣ, ∀ q, (ψ q : ℂ) = β q := by
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  obtain ⟨ψ, hψ⟩ := exists_linearCharFun_eq_of_mem_Irr (A := Q) hβ
  exact ⟨ψ, fun q => (linearCharFun_apply ψ q).symm.trans (congrFun hψ q)⟩

theorem Irr.apply_one_eq_one_of_isMulCommutative {β : Q → ℂ} (hβ : β ∈ Irr Q) : β 1 = 1 := by
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  exact Irr.apply_one_eq_one (A := Q) hβ

theorem card_irrFinset_of_isMulCommutative [Finite Q] : (irrFinset Q).card = Nat.card Q := by
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  exact card_irrFinset (A := Q)

theorem leftRegular_character_eq_sum_irrFinset [Finite Q] :
    (Representation.leftRegular ℂ Q).character = ∑ β ∈ irrFinset Q, β := by
  have hcoe : ∑ β ∈ irrFinset Q, (β : Q → ℂ) = ∑ β : irrFinset Q, ((β : Q → ℂ)) :=
    (Finset.sum_coe_sort (irrFinset Q) (fun β : Q → ℂ => β)).symm
  rw [leftRegular_character_eq_sum, hcoe]
  exact Finset.sum_congr rfl fun β _ =>
    by rw [Irr.apply_one_eq_one_of_isMulCommutative (mem_irrFinset.1 β.2), one_smul]

end Abelian

variable {I : Type*} [Group I] {H : Subgroup I} [H.Normal]

theorem mul_monoidHom_units_mem_Irr {η : I → ℂ} (hη : η ∈ Irr I) (χ : I →* ℂˣ) :
    (η * fun i => (χ i : ℂ)) ∈ Irr I := by
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hη
  have h := character_mem_Irr_of_isIrreducible (Representation.twist V.ρ χ)
    (Representation.IsIrreducible.twist hV χ)
  have he : (Representation.twist V.ρ χ).character = V.character * fun i => (χ i : ℂ) := by
    funext i
    rw [Representation.character_twist, fdRepCharacter_eq, Pi.mul_apply, mul_comm]
  rwa [he] at h

theorem indClassFun_mul_resClassFun [Fintype I] {K : Subgroup I} (f : K → ℂ) {h : I → ℂ}
    (hh : h ∈ classFun I) :
    indClassFun K (f * resClassFun K h) = indClassFun K f * h := by
  have hres : InducedCharacterConstruction.resClassFun K h = resClassFun K h := by
    funext x; rw [InducedCharacterConstruction.resClassFun_apply, resClassFun_apply]
  have key := InducedCharacterConstruction.indClassFun_mul_resClassFun (S := K) f
    (h := h) (InducedCharacterConstruction.mem_classFun.2 fun g c => classFun.apply_conj hh g c)
  rw [hres, NormalInducedFamily.indClassFun_inducedCharacterConstruction_eq,
    NormalInducedFamily.indClassFun_inducedCharacterConstruction_eq] at key
  exact key

theorem indClassFun_one_eq_leftRegular_comp_mk [Fintype I] :
    indClassFun H (1 : H → ℂ)
      = (Representation.leftRegular ℂ (I ⧸ H)).character ∘ (QuotientGroup.mk : I → I ⧸ H) := by
  set g : I → ℂ :=
    (Representation.leftRegular ℂ (I ⧸ H)).character ∘ (QuotientGroup.mk : I → I ⧸ H) with hg
  have hconj : ∀ x c : I, g (c * x * c⁻¹) = g x := by
    intro x c
    have hq : (QuotientGroup.mk (c * x * c⁻¹) : I ⧸ H)
        = QuotientGroup.mk c * QuotientGroup.mk x * (QuotientGroup.mk c)⁻¹ := rfl
    simp only [hg, Function.comp_apply, hq, Representation.char_conj]
  have hgcf : g ∈ classFun I := by
    refine mem_classFun.2 fun x y hxy => ?_
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    exact (hconj x c).symm
  have hg0 : ∀ l ∉ H, g l = 0 := by
    intro l hl
    have hne : (QuotientGroup.mk l : I ⧸ H) ≠ 1 := fun h => hl ((QuotientGroup.eq_one_iff l).1 h)
    exact leftRegular_character_of_ne_one hne
  have hres : resClassFun H g = (H.index : ℂ) • (1 : H → ℂ) := by
    funext x
    have h1 : (QuotientGroup.mk (x : I) : I ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).2 x.2
    rw [resClassFun_apply, hg, Function.comp_apply, h1, leftRegular_character_one]
    simp [Subgroup.index_eq_card]
  have key := NormalInducedSupportBasis.indClassFun_resClassFun H hgcf hg0
  rw [hres, indClassFun_smul] at key
  have hne : (H.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  exact smul_right_injective _ hne key

theorem inertiaGroup_resClassFun_eq_top {η : I → ℂ} (hη : η ∈ classFun I) :
    inertiaGroup H (resClassFun H η) = ⊤ := by
  refine eq_top_iff.2 fun t _ => ?_
  rw [mem_inertiaGroup]
  funext n
  rw [NormalInduction.conjClassFun_apply, resClassFun_apply, resClassFun_apply,
    MulAut.conjNormal_apply]
  simpa using classFun.apply_conj hη (n : I) t⁻¹

theorem cfInner_self_indClassFun_resClassFun [Fintype I] {η : I → ℂ} (hη : η ∈ classFun I)
    (hres : resClassFun H η ∈ Irr H) :
    cfInner (indClassFun H (resClassFun H η)) (indClassFun H (resClassFun H η))
      = (H.index : ℂ) := by
  rw [cfInner_self_indClassFun H hres, inertiaGroup_resClassFun_eq_top hη,
    Subgroup.relIndex_top_right]

theorem injOn_of_cfInner_self_eq_card [Fintype I] {ι : Type*} (s : Finset ι) (F : ι → I → ℂ)
    (hF : ∀ i ∈ s, F i ∈ Irr I)
    (hnorm : cfInner (∑ i ∈ s, F i) (∑ i ∈ s, F i) = (s.card : ℂ)) :
    ∀ i ∈ s, ∀ j ∈ s, F i = F j → i = j := by
  classical
  have hexp : cfInner (∑ i ∈ s, F i) (∑ i ∈ s, F i)
      = ∑ i ∈ s, ((s.filter fun j => F i = F j).card : ℂ) := by
    rw [cfInner_sum_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [cfInner_sum_right, ← Finset.sum_boole]
    exact Finset.sum_congr rfl fun j hj => cfInner_eq_ite_of_mem_Irr (hF i hi) (hF j hj)
  have hnat : ∑ i ∈ s, (s.filter fun j => F i = F j).card = s.card := by
    have h := hexp.symm.trans hnorm
    exact_mod_cast (by push_cast at h ⊢; exact h : ((∑ i ∈ s,
      (s.filter fun j => F i = F j).card : ℕ) : ℂ) = ((s.card : ℕ) : ℂ))
  have hle : ∀ i ∈ s, 1 ≤ (s.filter fun j => F i = F j).card := fun i hi =>
    Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩⟩
  have heq : ∀ i ∈ s, (s.filter fun j => F i = F j).card = 1 := by
    have h1 : ∑ i ∈ s, 1 = ∑ i ∈ s, (s.filter fun j => F i = F j).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, hnat]
    exact fun i hi => ((Finset.sum_eq_sum_iff_of_le hle).1 h1 i hi).symm
  intro i hi j hj hij
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (heq i hi)
  have hmi : i ∈ s.filter fun j => F i = F j := Finset.mem_filter.2 ⟨hi, rfl⟩
  have hmj : j ∈ s.filter fun j => F i = F j := Finset.mem_filter.2 ⟨hj, hij⟩
  rw [ha, Finset.mem_singleton] at hmi hmj
  rw [hmi, hmj]

variable [IsMulCommutative (I ⧸ H)]

theorem mul_comp_mk_mem_Irr {η : I → ℂ} (hη : η ∈ Irr I) {β : I ⧸ H → ℂ}
    (hβ : β ∈ Irr (I ⧸ H)) : η * (β ∘ (QuotientGroup.mk : I → I ⧸ H)) ∈ Irr I := by
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_units_of_mem_Irr hβ
  have h := mul_monoidHom_units_mem_Irr hη (ψ.comp (QuotientGroup.mk' H))
  have he : (η * fun i => ((ψ.comp (QuotientGroup.mk' H)) i : ℂ))
      = η * (β ∘ (QuotientGroup.mk : I → I ⧸ H)) := by
    funext i
    rw [Pi.mul_apply, Pi.mul_apply]
    exact congrArg _ (hψ _)
  rwa [he] at h

theorem mul_comp_mk_one {η : I → ℂ} {β : I ⧸ H → ℂ} (hβ : β ∈ Irr (I ⧸ H)) :
    (η * (β ∘ (QuotientGroup.mk : I → I ⧸ H))) 1 = resClassFun H η 1 := by
  have h1 : (QuotientGroup.mk (1 : I) : I ⧸ H) = 1 := by simp
  rw [Pi.mul_apply, Function.comp_apply, h1,
    Irr.apply_one_eq_one_of_isMulCommutative hβ, mul_one, resClassFun_apply]
  rfl

theorem indClassFun_resClassFun_eq_sum [Fintype I] {η : I → ℂ} (hη : η ∈ classFun I) :
    indClassFun H (resClassFun H η)
      = ∑ β ∈ irrFinset (I ⧸ H), η * (β ∘ (QuotientGroup.mk : I → I ⧸ H)) := by
  have h1 : (1 : H → ℂ) * resClassFun H η = resClassFun H η := one_mul _
  have hstep : indClassFun H (resClassFun H η) = indClassFun H (1 : H → ℂ) * η := by
    rw [← h1, indClassFun_mul_resClassFun _ hη]
  rw [hstep, indClassFun_one_eq_leftRegular_comp_mk, leftRegular_character_eq_sum_irrFinset]
  funext i
  rw [Pi.mul_apply, Function.comp_apply, Finset.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun β _ => by rw [Pi.mul_apply, Function.comp_apply, mul_comm]

theorem card_irrFinset_quotient [Finite I] : (irrFinset (I ⧸ H)).card = H.index := by
  rw [card_irrFinset_of_isMulCommutative, Subgroup.index_eq_card]

theorem mul_comp_mk_injOn [Fintype I] {η : I → ℂ} (hη : η ∈ Irr I)
    (hres : resClassFun H η ∈ Irr H) :
    Set.InjOn (fun β : I ⧸ H → ℂ => η * (β ∘ (QuotientGroup.mk : I → I ⧸ H))) (Irr (I ⧸ H)) := by
  have hcard : ((irrFinset (I ⧸ H)).card : ℂ) = (H.index : ℂ) := by
    rw [card_irrFinset_quotient]
  have key := injOn_of_cfInner_self_eq_card (irrFinset (I ⧸ H))
    (fun β : I ⧸ H → ℂ => η * (β ∘ (QuotientGroup.mk : I → I ⧸ H)))
    (fun β hβ => mul_comp_mk_mem_Irr hη (mem_irrFinset.1 hβ)) ?_
  · exact fun β hβ γ hγ h => key β (mem_irrFinset.2 hβ) γ (mem_irrFinset.2 hγ) h
  · rw [← indClassFun_resClassFun_eq_sum (Irr_subset_classFun hη), hcard]
    exact cfInner_self_indClassFun_resClassFun (Irr_subset_classFun hη) hres

theorem exists_finset_Irr_card_eq_index [Fintype I] {η : I → ℂ} (hη : η ∈ Irr I)
    (hres : resClassFun H η ∈ Irr H) :
    ∃ S : Finset (I → ℂ), (↑S ⊆ Irr I) ∧ S.card = H.index ∧
      indClassFun H (resClassFun H η) = ∑ χ ∈ S, χ := by
  classical
  set f : (I ⧸ H → ℂ) → I → ℂ :=
    fun β => η * (β ∘ (QuotientGroup.mk : I → I ⧸ H)) with hf
  have hinj : ∀ β ∈ irrFinset (I ⧸ H), ∀ γ ∈ irrFinset (I ⧸ H), f β = f γ → β = γ :=
    fun β hβ γ hγ h =>
      mul_comp_mk_injOn hη hres (mem_irrFinset.1 hβ) (mem_irrFinset.1 hγ) h
  refine ⟨(irrFinset (I ⧸ H)).image f, ?_, ?_, ?_⟩
  · intro χ hχ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hχ
    obtain ⟨β, hβ, rfl⟩ := hχ
    exact mul_comp_mk_mem_Irr hη (mem_irrFinset.1 hβ)
  · rw [Finset.card_image_of_injOn hinj, card_irrFinset_quotient]
  · rw [Finset.sum_image hinj, indClassFun_resClassFun_eq_sum (Irr_subset_classFun hη)]

end AbelianQuotientExtension

end CFSG.FeitThompson
