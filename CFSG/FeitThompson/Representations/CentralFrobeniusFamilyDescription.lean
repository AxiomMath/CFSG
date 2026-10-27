module

public import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Representations.NormalInductionPreservesKernelSubgroup
import CFSG.FeitThompson.Representations.FrobeniusSemidirectIrrCharacterList
import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct
open scoped ComplexConjugate Pointwise

section Layer

variable {L : Type*} [Group L] {Z : Subgroup L}

theorem charValueKernel_one {M R : Type*} [One M] [One R] :
    charValueKernel (1 : M → R) = Set.univ :=
  Set.eq_univ_of_forall fun _ => mem_charValueKernel.2 rfl

theorem exists_im_ne_zero_of_mem_irrDetect [Finite L] (hodd : Odd (Nat.card L)) {χ : L → ℂ}
    (hχ : χ ∈ irrDetect ℂ Z) : ∃ x, (χ x).im ≠ 0 :=
  exists_im_ne_zero_of_mem_Irr_of_ne_one_of_odd hodd
    (by rw [Irr_eq_irrChar]; exact (mem_irrDetect.1 hχ).1) (ne_one_of_mem_irrDetect hχ)

end Layer

variable {L : Type*} [Group L] [Fintype L] {P E Z : Subgroup L}

def centralFrobeniusFam (P Z : Subgroup L) : Set (L → ℂ) :=
  indClassFun P '' {θ ∈ Irr P | ¬ (Z.subgroupOf P : Set P) ⊆ charValueKernel θ}

theorem mem_centralFrobeniusFam {χ : L → ℂ} :
    χ ∈ centralFrobeniusFam P Z ↔ ∃ θ ∈ Irr P,
      ¬ (Z.subgroupOf P : Set P) ⊆ charValueKernel θ ∧ indClassFun P θ = χ := by
  simp only [centralFrobeniusFam, Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨fun ⟨θ, ⟨h1, h2⟩, h3⟩ => ⟨θ, h1, h2, h3⟩, fun ⟨θ, h1, h2, h3⟩ => ⟨θ, ⟨h1, h2⟩, h3⟩⟩

theorem mem_centralFrobeniusFam_iff_values {χ : L → ℂ} :
    χ ∈ centralFrobeniusFam P Z ↔ ∃ θ ∈ Irr P,
      (∃ z : P, (z : L) ∈ Z ∧ θ z ≠ θ 1) ∧ indClassFun P θ = χ := by
  simp only [mem_centralFrobeniusFam, Set.not_subset, SetLike.mem_coe, Subgroup.mem_subgroupOf,
    mem_charValueKernel]

theorem subset_charValueKernel_indClassFun_iff [Z.Normal] (hZP : Z ≤ P) {θ : P → ℂ}
    (hθ : θ ∈ Irr P) :
    (Z : Set L) ⊆ charValueKernel (indClassFun P θ) ↔
      (Z.subgroupOf P : Set P) ⊆ charValueKernel θ := by
  rw [← normalInduction_indClassFun_eq]
  exact NormalInduction.subset_charValueKernel_indClassFun_iff hZP
    (by rw [normalInduction_irrChars_eq_Irr]; exact hθ)

theorem centralFrobeniusFam_eq_irrDetect [P.Normal] [Z.Normal] [Nontrivial P] (hZP : Z ≤ P)
    (hmul : (P : Set L) * (E : Set L) = Set.univ) (hinf : P ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = ⊥) :
    centralFrobeniusFam P Z = irrDetect ℂ Z := by
  have : Fintype P := Fintype.ofFinite _
  have : Fintype E := Fintype.ofFinite _
  have hPE : P.IsComplement' E := isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf
  set ε := frobeniusMulEquiv hPE with hε
  have hφ : ∀ v : E, v ≠ 1 →
      MonoidHom.FixedPointFree (frobeniusConjAut P E v : P → P) := fun v hv =>
    fixedPointFree_frobeniusConjAut (hC (v : L) v.2 fun h => hv (Subtype.ext h))
  ext χ
  rw [mem_centralFrobeniusFam, mem_irrDetect, ← Irr_eq_irrChar]
  constructor
  · rintro ⟨θ, hθ, hker, rfl⟩
    have hθ1 : θ ≠ 1 := fun h =>
      hker (by rw [h, charValueKernel_one]; exact Set.subset_univ _)
    refine ⟨?_, ?_⟩
    · refine mem_Irr_of_comp_mulEquiv ε ?_
      rw [hε, indClassFun_comp_frobeniusMulEquiv hPE θ]
      exact indClassFun_kernelClassFun_mem_Irr hφ hθ hθ1
    · rw [subset_charValueKernel_indClassFun_iff hZP hθ]
      exact hker
  · rintro ⟨hχ, hker⟩
    have hχε : χ ∘ ε ∈ Irr (P ⋊[frobeniusConjAut P E] E) := by
      refine mem_Irr_of_comp_mulEquiv ε.symm ?_
      have h : (χ ∘ (ε : P ⋊[frobeniusConjAut P E] E → L)) ∘ (ε.symm : L → _) = χ := by
        funext y; simp [hε]
      rw [h]; exact hχ
    rw [Irr_eq_union hφ, Set.mem_union] at hχε
    rcases hχε with hcase | hcase
    ·
      exfalso
      obtain ⟨ψ, -, hψeq⟩ := mem_inflFam.1 hcase
      refine hker fun z hz => mem_charValueKernel.2 ?_
      have hzP : z ∈ P := hZP hz
      have hz1 : ε (inl ⟨z, hzP⟩) = z := by
        rw [hε, frobeniusMulEquiv_apply]; simp
      have hA : χ z = ψ 1 := by
        have h2 := congrFun hψeq (inl (⟨z, hzP⟩ : P))
        rw [Function.comp_apply, Function.comp_apply, hz1] at h2
        simpa using h2.symm
      have hB : χ 1 = ψ 1 := by
        have h2 := congrFun hψeq (1 : P ⋊[frobeniusConjAut P E] E)
        rw [Function.comp_apply, Function.comp_apply, map_one] at h2
        simpa using h2.symm
      rw [hA, hB]
    ·
      obtain ⟨θ, hθ, -, heq⟩ := mem_indKernelFam.1 hcase
      have hchi : indClassFun P θ = χ := by
        funext y
        obtain ⟨x, rfl⟩ := ε.surjective y
        exact congrFun ((indClassFun_comp_frobeniusMulEquiv hPE θ).trans heq) x
      refine ⟨θ, hθ, ?_, hchi⟩
      rw [← hchi] at hker
      rwa [subset_charValueKernel_indClassFun_iff hZP hθ] at hker

theorem centralFrobeniusFam_subset_Irr [P.Normal] [Z.Normal] [Nontrivial P] (hZP : Z ≤ P)
    (hmul : (P : Set L) * (E : Set L) = Set.univ) (hinf : P ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = ⊥) :
    centralFrobeniusFam P Z ⊆ Irr L := by
  rw [centralFrobeniusFam_eq_irrDetect (E := E) hZP hmul hinf hC, Irr_eq_irrChar]
  exact irrDetect_subset_irrChar Z

theorem centralFrobeniusFam_spec {p a : ℕ} (_hp : p.Prime) (_hpodd : Odd p) (_ha : 1 ≤ a)
    (hLodd : Odd (Nat.card L)) [P.Normal] (hP : P ≠ ⊥) (_hE : E ≠ ⊥)
    (_hPcard : Nat.card P = p ^ a) (hmul : (P : Set L) * (E : Set L) = Set.univ)
    (hinf : P ⊓ E = ⊥) (hC : ∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = ⊥)
    [Z.Normal] (_hZ : Z ≠ ⊥) (hZP : Z ≤ P ⊓ Subgroup.centralizer (P : Set L)) :
    centralFrobeniusFam P Z = irrDetect ℂ Z ∧
      (∀ χ ∈ centralFrobeniusFam P Z, (fun x => conj (χ x)) ∈ centralFrobeniusFam P Z) ∧
      (∀ χ ∈ centralFrobeniusFam P Z, ∃ x, (χ x).im ≠ 0) := by
  have _ : Nontrivial P := P.nontrivial_iff_ne_bot.2 hP
  have heq := centralFrobeniusFam_eq_irrDetect (E := E) (le_trans hZP inf_le_left) hmul hinf hC
  refine ⟨heq, fun χ hχ => ?_, fun χ hχ => ?_⟩
  · rw [heq] at hχ ⊢
    exact conj_mem_irrDetect hχ
  · rw [heq] at hχ
    exact exists_im_ne_zero_of_mem_irrDetect hLodd hχ

end CFSG.FeitThompson
