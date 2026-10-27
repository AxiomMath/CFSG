module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.HallImageQuotient

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X]

section Disjoint

variable {N J : Subgroup X} [N.Normal]

theorem injective_mk'_comp_subtype (h : N ⊓ J = ⊥) :
    Function.Injective ((QuotientGroup.mk' N).comp J.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_mk'_comp_subtype, h, Subgroup.bot_subgroupOf]

noncomputable def mulEquivMapMk'OfDisjoint (h : N ⊓ J = ⊥) :
    J ≃* J.map (QuotientGroup.mk' N) :=
  (MonoidHom.ofInjective (injective_mk'_comp_subtype h)).trans
    (MulEquiv.subgroupCongr (range_mk'_comp_subtype J N))

@[simp]
theorem coe_mulEquivMapMk'OfDisjoint (h : N ⊓ J = ⊥) (x : J) :
    (mulEquivMapMk'OfDisjoint h x : X ⧸ N) = QuotientGroup.mk (x : X) := by
  rw [mulEquivMapMk'OfDisjoint, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]
  rfl

@[simp]
theorem coe_mulEquivMapMk'OfDisjoint_symm (h : N ⊓ J = ⊥) (y : J.map (QuotientGroup.mk' N)) :
    QuotientGroup.mk (((mulEquivMapMk'OfDisjoint h).symm y : J) : X) = (y : X ⧸ N) := by
  rw [← coe_mulEquivMapMk'OfDisjoint h, MulEquiv.apply_symm_apply]

end Disjoint

theorem fittingRaw_quotient_piCore_le_piCore_compl (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    fittingRaw (X ⧸ piCore π X) ≤ piCore πᶜ (X ⧸ piCore π X) := by
  refine fittingRaw_le fun N hN hN' => ?_
  obtain ⟨p, -, hpi⟩ := isPrimePowerOrder_iff_isPiSubgroup.1 hN'
  by_cases hpπ : p ∈ π
  ·
    have h : N ≤ piCore π (X ⧸ piCore π X) :=
      le_piCore hN (hpi.mono (Set.singleton_subset_iff.2 hpπ))
    rw [piCore_quotient_piCore] at h
    exact h.trans bot_le
  · exact le_piCore hN (hpi.mono (Set.singleton_subset_iff.2 hpπ))

theorem isPiSubgroup_compl_fittingRaw_quotient_piCore (π : Set ℕ) (X : Type*) [Group X]
    [Finite X] : IsPiSubgroup πᶜ (fittingRaw (X ⧸ piCore π X)) :=
  (isPiSubgroup_piCore πᶜ (X ⧸ piCore π X)).of_le
    (fittingRaw_quotient_piCore_le_piCore_compl π X)

theorem not_dvd_natCard_fittingRaw_quotient_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π) :
    ¬ p ∣ Nat.card (fittingRaw (X ⧸ piCore π X)) := fun hdvd =>
  isPiSubgroup_iff.1 (isPiSubgroup_compl_fittingRaw_quotient_piCore π X) p
    (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩) hpπ

theorem exists_inf_piCore_eq_bot_map_mk'_eq_fittingRaw (π : Set ℕ) (X : Type*) [Group X]
    [Finite X] [Group.IsSolvable X] :
    ∃ J : Subgroup X, piCore π X ⊓ J = ⊥ ∧
      J.map (QuotientGroup.mk' (piCore π X)) = fittingRaw (X ⧸ piCore π X) := by
  set A := piCore π X with hAdef
  set F := fittingRaw (X ⧸ A) with hFdef
  set T := F.comap (QuotientGroup.mk' A) with hTdef
  have hApi : IsPiNumber π (Nat.card A) :=
    isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_piCore π X)
  have hFpi : IsPiNumber πᶜ (Nat.card F) :=
    isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_compl_fittingRaw_quotient_piCore π X)
  have hTcard : Nat.card T = Nat.card A * Nat.card F := natCard_comap_mk' A F
  obtain ⟨J', hJ'⟩ := exists_isHallSubgroup (X := (T : Type _)) πᶜ
  have hJ'index : IsPiNumber π J'.index := by
    have := hJ'.index; rwa [compl_compl] at this
  have hcopA : Nat.Coprime (Nat.card J') (Nat.card A) :=
    (hApi.coprime_of_compl hJ'.natCard Nat.card_pos.ne' Nat.card_pos.ne').symm
  have hprod : Nat.card J' * J'.index = Nat.card A * Nat.card F := by
    rw [Subgroup.card_mul_index, hTcard]
  obtain ⟨k, hk⟩ : Nat.card J' ∣ Nat.card F := hcopA.dvd_of_dvd_mul_left ⟨J'.index, hprod.symm⟩
  obtain ⟨m, hm⟩ : J'.index ∣ Nat.card A :=
    (hJ'index.coprime_of_compl hFpi Subgroup.index_ne_zero_of_finite
      Nat.card_pos.ne').dvd_of_dvd_mul_right ⟨Nat.card J', by rw [← hprod]; ring⟩
  have hmk : m * k = 1 := by
    have h1 : Nat.card J' * J'.index * (m * k) = Nat.card J' * J'.index * 1 :=
      calc Nat.card J' * J'.index * (m * k) = J'.index * m * (Nat.card J' * k) := by ring
        _ = Nat.card A * Nat.card F := by rw [← hm, ← hk]
        _ = Nat.card J' * J'.index * 1 := by rw [mul_one, hprod]
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)) h1
  have hJ'F : Nat.card J' = Nat.card F := by
    rw [hk, Nat.dvd_one.1 ⟨m, ((mul_comm k m).trans hmk).symm⟩, mul_one]
  set J := J'.map T.subtype with hJdef
  have hJcard : Nat.card J = Nat.card J' := Subgroup.card_map_of_injective T.subtype_injective
  have hinf : A ⊓ J = ⊥ := by
    refine Subgroup.card_eq_one.1 (Nat.Coprime.eq_one_of_dvd ?_
      (Subgroup.card_dvd_of_le (inf_le_left : A ⊓ J ≤ A)))
    refine Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le (inf_le_right : A ⊓ J ≤ J)) ?_
    rw [hJcard]; exact hcopA
  refine ⟨J, hinf, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rw [Subgroup.map_le_iff_le_comap]; exact Subgroup.map_subtype_le J'
  · rw [natCard_map_mk'_eq_natCard_div J A, hinf, Subgroup.card_bot, Nat.div_one, hJcard, hJ'F]

theorem exists_subgroup_mulEquiv_fittingRaw_quotient_piCore (π : Set ℕ) (X : Type*) [Group X]
    [Finite X] [Group.IsSolvable X] :
    ∃ (J : Subgroup X) (e : J ≃* fittingRaw (X ⧸ piCore π X)),
      ∀ x : J, (e x : X ⧸ piCore π X) = QuotientGroup.mk (x : X) := by
  have : (piCore π X).Normal := piCore_normal π X
  obtain ⟨J, hinf, hmap⟩ := exists_inf_piCore_eq_bot_map_mk'_eq_fittingRaw π X
  refine ⟨J, (mulEquivMapMk'OfDisjoint hinf).trans (MulEquiv.subgroupCongr hmap), fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, coe_mulEquivMapMk'OfDisjoint]

theorem exists_subgroup_mulEquiv_fittingRaw_quotient_of_eq_piCore (π : Set ℕ) (X : Type*)
    [Group X] [Finite X] [Group.IsSolvable X] {A : Subgroup X} [A.Normal] (hA : A = piCore π X) :
    ∃ (J : Subgroup X) (e : J ≃* fittingRaw (X ⧸ A)),
      ∀ x : J, (e x : X ⧸ A) = QuotientGroup.mk (x : X) := by
  subst hA
  exact exists_subgroup_mulEquiv_fittingRaw_quotient_piCore π X

end

end CFSG.FeitThompson
