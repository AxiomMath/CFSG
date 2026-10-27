module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutComplete
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import Certificates.Kernel.SporCovBase.Fi22Glue

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.Open

namespace MulAutSimple

variable {A U : Type*} [Group A] [Group U]

theorem center_eq_bot_of_mulEquiv [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (e : A ≃* MulAut U) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have hc : e a ∈ Subgroup.center (MulAut U) := by
    rw [Subgroup.mem_center_iff]
    intro b
    have h := congrArg e (Subgroup.mem_center_iff.mp ha (e.symm b))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  rw [center_mulAut_eq_bot hna, Subgroup.mem_bot] at hc
  exact e.injective (hc.trans (map_one e).symm)

theorem exists_conj_eq_of_mulEquiv [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (e : A ≃* MulAut U) (φ : MulAut A) : ∃ a : A, φ = MulAut.conj a := by
  obtain ⟨a', ha'⟩ := mulAut_complete hna (MulAut.congr e φ)
  refine ⟨e.symm a', MulEquiv.ext fun x => e.injective ?_⟩
  have h := congrArg (fun ψ : MulAut (MulAut U) => ψ (e x)) ha'
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h

theorem normal_eq_bot_or_index_two_or_top_of_mulEquiv [IsSimpleGroup U]
    (hna : ∃ a b : U, a * b ≠ b * a) (h2 : (inn U).index = 2) (e : A ≃* MulAut U)
    (N : Subgroup A) (hN : N.Normal) : N = ⊥ ∨ N.index = 2 ∨ N = ⊤ := by
  haveI : (N.map (e : A →* MulAut U)).Normal := hN.map (e : A →* MulAut U) e.surjective
  rcases normal_eq_bot_or_index_two_or_top hna h2 (N.map (e : A →* MulAut U)) with h | h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective N e.injective).1 h)
  · refine Or.inr (Or.inl ?_)
    rwa [Subgroup.index_map_equiv] at h
  · refine Or.inr (Or.inr (eq_top_iff.2 fun x _ => ?_))
    have hx : e x ∈ N.map (e : A →* MulAut U) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    exact (e.injective hyx) ▸ hy

theorem commutator_eq_comap_inn_of_mulEquiv [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (h2 : (inn U).index = 2) (e : A ≃* MulAut U) :
    commutator A = (inn U).comap (e : A →* MulAut U) := by
  have h1 : (commutator A).map (e : A →* MulAut U) = commutator (MulAut U) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← commutator_eq_inn hna h2, ← h1, Subgroup.comap_map_eq_self_of_injective e.injective]

end MulAutSimple

theorem exists_statedClassicalModel_psu42 :
    ∃ (U : Type) (_ : Group U), StatedClassicalModel U .PSU 4 2 1 := by
  refine ⟨StatedProj (StatedSU 4 (2 ^ 1) (GaloisField 2 2)), inferInstance,
    ⟨Nat.prime_two, le_rfl, by omega, ?_⟩, GaloisField 2 2, inferInstance, inferInstance, ?_,
    ⟨MulEquiv.refl _⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · rw [GaloisField.card 2 2 (by norm_num)]
    norm_num

theorem card_mulAut_of_statedPSU42 {U : Type} [Group U]
    (hU : StatedClassicalModel U .PSU 4 2 1) : Nat.card (MulAut U) = 51840 :=
  (CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42
    (Or.inl ⟨by decide, hU⟩)).1

theorem index_inn_eq_two_of_statedPSU42 {U : Type} [Group U]
    (hU : StatedClassicalModel U .PSU 4 2 1) : (MulAutSimple.inn U).index = 2 := by
  haveI := isSimpleGroup_of_statedPSU42 hU
  haveI : Finite U := Nat.finite_of_card_ne_zero (by rw [card_of_statedPSU42 hU]; norm_num)
  refine MulAutSimple.index_inn_eq_two (exists_mul_ne_of_statedPSU42 hU) ?_
  have h1 := card_mulAut_of_statedPSU42 hU
  have h2 := card_of_statedPSU42 hU
  omega

theorem commutator_eq_comap_inn_of_statedPSU42 {A U : Type}
    [Group A] [Group U] (hU : StatedClassicalModel U .PSU 4 2 1) (e : A ≃* MulAut U) :
    commutator A = (MulAutSimple.inn U).comap (e : A →* MulAut U) := by
  haveI := isSimpleGroup_of_statedPSU42 hU
  exact MulAutSimple.commutator_eq_comap_inn_of_mulEquiv (exists_mul_ne_of_statedPSU42 hU)
    (index_inn_eq_two_of_statedPSU42 hU) e

namespace IsU42Two

theorem center_eq_bot {A : Type} [Group A] (h : IsU42Two A) : Subgroup.center A = ⊥ := by
  obtain ⟨U, _, -, hs, hna, ⟨e⟩⟩ := h.exists_simple
  haveI := hs
  exact MulAutSimple.center_eq_bot_of_mulEquiv hna e

theorem complete {A : Type} [Group A] (h : IsU42Two A) (φ : MulAut A) :
    ∃ a : A, φ = MulAut.conj a := by
  obtain ⟨U, _, -, hs, hna, ⟨e⟩⟩ := h.exists_simple
  haveI := hs
  exact MulAutSimple.exists_conj_eq_of_mulEquiv hna e φ

theorem card_eq {A : Type} [Group A] (h : IsU42Two A) :
    Nat.card A = 2 ^ 7 * 3 ^ 4 * 5 := by
  obtain ⟨U, _, hU, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_mulAut_of_statedPSU42 hU]
  norm_num

theorem normal_eq {A : Type} [Group A] (h : IsU42Two A)
    (N : Subgroup A) (hN : N.Normal) : N = ⊥ ∨ N.index = 2 ∨ N = ⊤ := by
  obtain ⟨U, _, hU, hs, hna, ⟨e⟩⟩ := h.exists_simple
  haveI := hs
  exact MulAutSimple.normal_eq_bot_or_index_two_or_top_of_mulEquiv hna
    (index_inn_eq_two_of_statedPSU42 hU) e N hN

theorem exists_commutator_eq {A : Type} [Group A]
    (h : IsU42Two A) :
    ∃ (U : Type) (_ : Group U) (e : A ≃* MulAut U), StatedClassicalModel U .PSU 4 2 1 ∧
      commutator A = (MulAutSimple.inn U).comap (e : A →* MulAut U) := by
  obtain ⟨U, _, hU, ⟨e⟩⟩ := h
  exact ⟨U, inferInstance, e, hU, commutator_eq_comap_inn_of_statedPSU42 hU e⟩

end IsU42Two

open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 equiv_of_lieModel exists_model)
open CFSG.GH74.Exceptional (lieModel_PSp_two_three_of_lieModel_PSU_four_two)

theorem isU42Two_QA45 : IsU42Two ↥QA45.originalSubgroup := by
  obtain ⟨U, _, hU⟩ := exists_statedClassicalModel_psu42
  obtain ⟨e⟩ := equiv_of_lieModel
    (lieModel_PSp_two_three_of_lieModel_PSU_four_two (Or.inl ⟨by decide, hU⟩))
  obtain ⟨M, -, hA⟩ := exists_model e
  exact ⟨U, inferInstance, hU, ⟨(M.Φ.trans (MulEquiv.subgroupCongr hA)).symm⟩⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
