module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Red
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Syl
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem comm_mem_linD (α β : MulAut (projectiveSL 3 K)) :
    α * β * α⁻¹ * β⁻¹ ∈ (conjAut 3 K).range := by
  have h := OuterDerived.commutator_mem_linearAutGroup (K := K) (n := 3) le_rfl α β
  rwa [linearAutGroup_eq_range] at h

instance normal_linD : (conjAut 3 K).range.Normal :=
  ⟨fun d hd g => by
    have h := comm_mem_linD g d
    have e : g * d * g⁻¹ = (g * d * g⁻¹ * d⁻¹) * d := by group
    rw [e]
    exact Subgroup.mul_mem _ h hd⟩

theorem mk_comm_linD (a b : MulAut (projectiveSL 3 K) ⧸ (conjAut 3 K).range) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have := comm_mem_linD b⁻¹ a⁻¹
  convert this using 1
  group

theorem lin_hcyc (P : Subgroup (MulAut (projectiveSL 3 K))) (hP : IsPGroup 3 P) :
    ∀ H ≤ P, ∃ x ∈ H, ∀ h ∈ H, ∃ k : ℤ, x ^ k * h⁻¹ ∈ (conjAut 3 K).range := by
  intro H hHP
  set D := (conjAut 3 K).range with hD
  let mk : MulAut (projectiveSL 3 K) →* MulAut (projectiveSL 3 K) ⧸ D := QuotientGroup.mk' D
  have hcycK : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  let C1 : Subgroup (MulAut (projectiveSL 3 K) ⧸ D) := (mk.comp (fieldAut 3 K)).range
  have hC1 : IsCyclic C1 :=
    isCyclic_of_surjective (mk.comp (fieldAut 3 K)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hconj : ∀ A : GL (Fin 3) K, mk (conjAut 3 K A) = 1 := fun A =>
    (QuotientGroup.eq_one_iff _).2 ⟨A, rfl⟩
  have hδ2 : dualAut 3 K * dualAut 3 K = 1 :=
    (standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have hmem : ∀ g ∈ P, mk g ∈ C1 := by
    intro g hg
    obtain ⟨A, σ, ε, hε, hgeq⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 g
    have hf : mk (fieldAut 3 K σ) ∈ C1 := ⟨σ, rfl⟩
    interval_cases ε
    · rw [hgeq, pow_zero, mul_one, map_mul, hconj, one_mul]
      exact hf
    · obtain ⟨m, hm⟩ := hP ⟨g, hg⟩
      have hm' : g ^ (3 ^ m) = 1 := congrArg Subtype.val hm
      rw [hgeq, pow_one] at hm' ⊢
      rw [map_mul, map_mul, hconj, one_mul]
      have hcomm : Commute (mk (fieldAut 3 K σ)) (mk (dualAut 3 K)) := mk_comm_linD _ _
      have h1 : (mk (fieldAut 3 K σ) * mk (dualAut 3 K)) ^ (3 ^ m) = 1 := by
        have := congrArg mk hm'
        rw [map_pow, map_mul, map_mul, hconj, one_mul, map_one] at this
        exact this
      rw [hcomm.mul_pow] at h1
      have hd2 : mk (dualAut 3 K) ^ 2 = 1 := by rw [sq, ← map_mul, hδ2, map_one]
      have hodd : mk (dualAut 3 K) ^ (3 ^ m) = mk (dualAut 3 K) := by
        obtain ⟨t, ht⟩ : Odd (3 ^ m) := Odd.pow (by decide)
        rw [ht, pow_succ, pow_mul, hd2, one_pow, one_mul]
      rw [hodd] at h1
      have hδC : mk (dualAut 3 K) ∈ C1 := by
        rw [eq_inv_of_mul_eq_one_right h1]
        exact C1.inv_mem (C1.pow_mem hf _)
      exact C1.mul_mem hf hδC
  let HC : Subgroup C1 := (H.map mk).subgroupOf C1
  have hHC : IsCyclic HC := inferInstance
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := HC)
  have hgenmem : ((gen : C1) : MulAut (projectiveSL 3 K) ⧸ D) ∈ H.map mk := gen.2
  obtain ⟨x, hxH, hx⟩ := hgenmem
  refine ⟨x, hxH, fun h hh => ?_⟩
  have hy : (⟨⟨mk h, hmem h (hHP hh)⟩, Subgroup.mem_map_of_mem mk hh⟩ : HC) ∈ Subgroup.zpowers gen :=
    hgen _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hk' : (mk x) ^ k = mk h := by
    have := congrArg (fun z : HC => ((z : C1) : MulAut (projectiveSL 3 K) ⧸ D)) hk
    simp only [Subgroup.coe_zpow] at this
    rw [← this]
    simp only [← hx]
  have : mk (x ^ k * h⁻¹) = 1 := by rw [map_mul, map_inv, map_zpow, hk', mul_inv_cancel]
  exact ⟨k, (QuotientGroup.eq_one_iff _).1 this⟩

theorem not_hasElemSection3_four_projectiveSL (hK : Nat.card K % 3 = 1)
    (P : Subgroup (MulAut (projectiveSL 3 K))) (hP : IsPGroup 3 P) :
    ¬ HasElemSection3 P 4 := by
  refine not_hasElemSection3_four_of_reduction (conjAut 3 K).range P (lin_hcyc P hP) ?_
  intro H0 N0 hH0P hH0D hN0 hcomm hcube
  let c : (⊤ : Subgroup (GL (Fin 3) K)) →* MulAut (projectiveSL 3 K) :=
    (conjAut 3 K).comp Subgroup.topEquiv.toMonoidHom
  have hrange : (conjAut 3 K).range ≤ c.range := by
    rintro _ ⟨A, rfl⟩
    exact ⟨⟨A, trivial⟩, rfl⟩
  refine relIndex_le_nine_of_hom hK ⊤ c ?_ (hH0D.trans hrange) (hP.to_le hH0P) hN0 hcomm hcube
  rintro g ⟨c0, hc0⟩
  show conjAut 3 K (g : GL (Fin 3) K) = 1
  rw [hc0, conjAut_scalar]

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
