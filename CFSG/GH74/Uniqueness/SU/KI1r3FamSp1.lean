module

public import CFSG.GH74.Uniqueness.SU.KI1r3FamDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter
public import CFSG.Sporadic.J1

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open CFSG CFSG.Blueprint

namespace FamSp1

theorem exists_noncomm_of_simple {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hp : ¬ (Nat.card K).Prime) : ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup K := { ‹Group K› with mul_comm := h }
  exact hp IsSimpleGroup.prime_card

theorem fourFix_of_equiv_inner {K S : Type} [Group K] [Finite K] [Group S] [IsSimpleGroup S]
    (e : K ≃* S) (hS : ¬ (Nat.card S).Prime)
    (hinn : ∀ β : MulAut K, ∃ l : K, ∀ x : K, β x = l⁻¹ * x * l) : FourFix K := by
  have : IsSimpleGroup K := e.isSimpleGroup
  refine FourFix.of_inner (exists_noncomm_of_simple ?_) fun α _ => ?_
  · rwa [Nat.card_congr e.toEquiv]
  · obtain ⟨l, hl⟩ := hinn α
    exact ⟨l⁻¹, MulEquiv.ext fun x => by simp [hl x]⟩

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover in
theorem fourFix_M12
    : FourFix NativeSporadic.M12 := by
  have : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  intro α hα
  by_cases hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M12
  · obtain ⟨g, rfl⟩ := hin
    left
    exact four_group_fixed_of_inner
      (exists_noncomm_of_simple (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)) g hα
  · left
    have h1 : α ≠ 1 := fun h => hin (h ▸ Subgroup.one_mem _)
    have h2 : orderOf α = 2 := orderOf_eq_prime hα h1
    obtain ⟨g, rfl⟩ := exists_conj_beta_of_outer h2 hin
    obtain ⟨hD, -, -, -, -, -, -, hWD, hW4, -, -, -, hWsq, hWc, -⟩ :=
      fusionData_pinned.map (MulAut.conj g)
    refine ⟨fusionW.map (MulAut.conj g).toMonoidHom, ?_, ?_, hW4⟩
    · intro v hv
      have hv' := hWD hv
      rw [hD] at hv'
      have hle : ⁅fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹),
          fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹)⁆ ≤
          fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
          (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
      exact mem_fixSub.1 (hle hv')
    · rw [SU1.isElemAbelian_iff]
      exact ⟨hWc, hWsq⟩

end FamSp1

theorem famSp_M11 :
    FamSp .M11 := by
  intro K _ _ ⟨e⟩
  have : IsSimpleGroup (NativeSporadic.Carrier .M11) :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  refine FamSp1.fourFix_of_equiv_inner e ?_ fun β => ?_
  · show ¬ (Nat.card NativeSporadic.M11).Prime
    rw [CFSG.Sporadic.Mathieu.card_M11]
    norm_num
  · exact CFSG.QuasithinUnique.Ch1.autInner_of_equiv_of_inner e
      CFSG.QuasithinUnique.Ch1.m11_all_inner β

theorem famSp_J1 : FamSp .J1 := by
  intro K _ _ ⟨e⟩
  have : IsSimpleGroup (NativeSporadic.Carrier .J1) :=
    CFSG.Sporadic.J1.fam_j1_simplicity.2.2
  refine FamSp1.fourFix_of_equiv_inner e ?_ fun β => ?_
  · show ¬ (Nat.card NativeSporadic.J1).Prime
    rw [CFSG.Sporadic.J1.card_J1]
    norm_num
  · exact CFSG.QuasithinUnique.Ch1.isInnerAut_of_carrierJ1 e β

theorem famSp_M23 :
    FamSp .M23 := by
  intro K _ _ ⟨e⟩
  have : IsSimpleGroup (NativeSporadic.Carrier .M23) :=
    CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  refine FamSp1.fourFix_of_equiv_inner e ?_ fun β => ?_
  · show ¬ (Nat.card NativeSporadic.M23).Prime
    rw [CFSG.Sporadic.Schreier.m23_card]
    norm_num
  · exact CFSG.QuasithinUnique.Ch1.autInner_of_equiv_of_inner e
      CFSG.QuasithinUnique.Ch1.m23_all_inner β

theorem famSp_M12
    : FamSp .M12 := by
  intro K _ _ ⟨e⟩
  exact FourFix.of_mulEquiv (K := NativeSporadic.M12) (e.symm : NativeSporadic.M12 ≃* K)
    FamSp1.fourFix_M12

end CFSG.GH74.Uniqueness.SU.K.R3
