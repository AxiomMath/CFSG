module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormality
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem exists_isSylowSubgroupOf_ge_of_isPGroup [Finite G] {p : ℕ} {M Q : Subgroup G}
    (hQM : Q ≤ M) (hQ : IsPGroup p Q) :
    ∃ P : Subgroup G, _root_.CFSG.FeitThompson.IsSylowIn p M P ∧ Q ≤ P := by
  have hQ' : IsPGroup p ↥(Q.subgroupOf M) := hQ.of_equiv (subgroupOfEquivOfLe hQM).symm
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup ↥M).map M.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQM hx⟩, hS (show (⟨x, hQM hx⟩ : ↥M) ∈ Q.subgroupOf M from hx), rfl⟩

theorem normalizer_le_normalizer_of_eq_pow_torsion {p : ℕ} {P A : Subgroup G}
    (hA : (A : Set G) = {x ∈ (P : Set G) | x ^ p = 1}) :
    normalizer (P : Set G) ≤ normalizer (A : Set G) := by
  have hmem : ∀ x : G, x ∈ A ↔ x ∈ P ∧ x ^ p = 1 := by
    intro x; rw [← SetLike.mem_coe, hA]; exact Iff.rfl
  intro g hg
  have hgP := mem_normalizer_iff.1 hg
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨hhP, hhp⟩ := (hmem h).1 hh
    refine (hmem _).2 ⟨(hgP h).1 hhP, ?_⟩
    rw [conj_pow, hhp, mul_one, mul_inv_cancel]
  · obtain ⟨hhP, hhp⟩ := (hmem _).1 hh
    refine (hmem h).2 ⟨(hgP h).2 hhP, ?_⟩
    rw [conj_pow] at hhp
    simpa [mul_inv_eq_one] using hhp

theorem inf_normalizer_eq_bot_of_inf_centralizer_eq_bot {S A M : Subgroup G}
    (hSM : M ≤ normalizer (S : Set G)) (hAM : A ≤ M)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hSA : S ⊓ centralizer (A : Set G) = ⊥) :
    S ⊓ normalizer (A : Set G) = ⊥ := by
  have hAC : A ≤ centralizer (A : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => hAcomm y hy x hx
  refine le_antisymm (fun s hs => ?_) bot_le
  obtain ⟨hsS, hsN⟩ := mem_inf.1 hs
  have hsC : s ∈ centralizer (A : Set G) := by
    refine mem_centralizer_iff.2 fun a ha => ?_
    have hA : s * a * s⁻¹ * a⁻¹ ∈ A :=
      mul_mem ((mem_normalizer_iff.1 hsN a).1 ha) (inv_mem ha)
    have hS : s * a * s⁻¹ * a⁻¹ ∈ S := by
      have h1 : a * s⁻¹ * a⁻¹ ∈ S := by
        have := (mem_normalizer_iff.1 (hSM (hAM ha)) s⁻¹).1 (inv_mem hsS)
        simpa [mul_assoc] using this
      have : s * (a * s⁻¹ * a⁻¹) ∈ S := mul_mem hsS h1
      simpa [mul_assoc] using this
    have h1 : s * a * s⁻¹ * a⁻¹ = 1 := mem_bot.1 (hSA ▸ mem_inf.2 ⟨hS, hAC hA⟩)
    have h2 : s * a * s⁻¹ = a := mul_inv_eq_one.1 h1
    calc a * s = (s * a * s⁻¹) * s := by rw [h2]
      _ = s * a := by group
  exact mem_bot.2 (mem_bot.1 (hSA ▸ mem_inf.2 ⟨hsS, hsC⟩))

theorem FNI_outside_sigma_plane_complement_normalizer
    (h₁ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₂ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FNI_outside_sigma_plane_complement_normalizer.{u} := by
  intro G _ _ hG p M A E hAplane hE hAE
  obtain ⟨hM, hp, hpσ, hAM, hAeap⟩ := hAplane
  have hG' : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hplane : CFSG.FeitThompson.Prep08.IsPlaneAt p A :=
    ⟨isElementaryAbelian_iff_isElementaryAbelianSubgroup.2
      hAeap.isElementaryAbelianSubgroup, hAeap.natCard'⟩
  have hsemi := hE.isInternalSemidirectProduct
  have hEM : E ≤ M := hE.le
  have hnorm : E ≤ normalizer (A : Set G) :=
    FTS_outside_sigma_plane_complement_normality h₂ G hG' M A E p hM hp hpσ hAM hplane hEM
      hsemi hAE
  have hSC : sigmaCore M ⊓ centralizer (A : Set G) = ⊥ :=
    (h₂ G hG' M A p hM hp hpσ hAM hplane).2.1
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hAeap.isElementaryAbelianSubgroup.mul_comm
  have hSN : sigmaCore M ⊓ normalizer (A : Set G) = ⊥ :=
    inf_normalizer_eq_bot_of_inf_centralizer_eq_bot hsemi.le_normalizer hAM hAcomm hSC
  have hNM : normalizer (A : Set G) ⊓ M = E := by
    refine le_antisymm (fun x hx => ?_) (le_inf hnorm hEM)
    obtain ⟨hxN, hxM⟩ := mem_inf.1 hx
    obtain ⟨s, hs, e, he, rfl⟩ := hsemi.exists_mul hxM
    have hsN : s ∈ normalizer (A : Set G) := by
      have h : s = s * e * e⁻¹ := by group
      rw [h]
      exact mul_mem hxN (inv_mem (hnorm he))
    have hs1 : s = 1 := mem_bot.1 (hSN ▸ mem_inf.2 ⟨hs, hsN⟩)
    simpa [hs1] using he
  have hApg : IsPGroup p ↥A := IsPGroup.of_card hAeap.natCard'
  obtain ⟨P, hP, hAP⟩ := exists_isSylowSubgroupOf_ge_of_isPGroup hAM hApg
  obtain ⟨-, hPimp⟩ := (h₁ G hG p M A ⟨hM, hp, hpσ, hAM, hAeap⟩).2.2.1 P hP
  obtain ⟨hAtor, hPnot⟩ := hPimp hAP
  refine ⟨hnorm, ?_, ?_, hNM, fun hcon => hPnot ((normalizer_le_normalizer_of_eq_pow_torsion
    hAtor).trans hcon)⟩
  ·
    intro X hXE hXcard
    have hXpg : IsPGroup p ↥X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
    have hsup : IsPGroup p ↥(A ⊔ X : Subgroup G) :=
      hApg.to_sup_of_normal_left' hXpg fun x hx => hnorm (hXE hx)
    obtain ⟨Q, hQ, hAXQ⟩ :=
      exists_isSylowSubgroupOf_ge_of_isPGroup (sup_le hAM (hXE.trans hEM)) hsup
    obtain ⟨-, hQimp⟩ := (h₁ G hG p M A ⟨hM, hp, hpσ, hAM, hAeap⟩).2.2.1 Q hQ
    obtain ⟨hAtorQ, -⟩ := hQimp (le_sup_left.trans hAXQ)
    intro x hx
    have hxQ : x ∈ Q := hAXQ ((le_sup_right : X ≤ A ⊔ X) hx)
    have hxp : x ^ p = 1 := by
      rw [← hXcard]
      exact orderOf_dvd_iff_pow_eq_one.1 (X.orderOf_dvd_natCard hx)
    rw [← SetLike.mem_coe, hAtorQ]
    exact ⟨hxQ, hxp⟩
  ·
    have hCM : centralizer (A : Set G) ≤ M := (h₃ G hG' M A p hM hp hAM hplane).1
    rw [← hNM]
    exact le_inf (centralizer_le_normalizer (A : Set G)) hCM

end

end CFSG.FeitThompson.Proofs
