module

public import CFSG.Open.LocalVocabulary
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem le_normalizer_of_commutator_le {L A : Subgroup G}
    (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) : A ≤ normalizer (L : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  exact hAL.trans (Subgroup.map_subtype_le _)

private def conjAction {L A : Subgroup G} (hAL : A ≤ normalizer (L : Set G)) :
    ↥A →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)

private theorem conjAction_coe {L A : Subgroup G} (hAL : A ≤ normalizer (L : Set G))
    (a : ↥A) (l : ↥L) :
    ((conjAction hAL a l : ↥L) : G) = (a : G) * (l : G) * (a : G)⁻¹ := rfl

private theorem mem_pCore_iff_mem_pCoreOf {L : Subgroup G} (l : ↥L) :
    l ∈ CFSG.pCore 2 ↥L ↔ (l : G) ∈ pCoreOf 2 L := by
  constructor
  · intro hl
    exact ⟨l, hl, rfl⟩
  · rintro ⟨n, hn, hnl⟩
    have hnl' : n = l := Subtype.ext hnl
    rwa [← hnl']

private theorem conjAction_mem_pCore {L A : Subgroup G}
    (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) (a : ↥A) {n : ↥L}
    (hn : n ∈ CFSG.pCore 2 ↥L) :
    conjAction (le_normalizer_of_commutator_le hAL) a n ∈ CFSG.pCore 2 ↥L := by
  rw [mem_pCore_iff_mem_pCoreOf] at hn ⊢
  rw [conjAction_coe]
  have h := hAL (Subgroup.commutator_mem_commutator a.2 n.2)
  have e : (a : G) * (n : G) * (a : G)⁻¹ = ⁅(a : G), (n : G)⁆ * (n : G) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (pCoreOf 2 L).mul_mem h hn

private theorem quotientAction_eq_of_commutator_le {L A : Subgroup G}
    (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) (a : ↥A) {x : G} (hx : x ∈ L) :
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
      (conjAction (le_normalizer_of_commutator_le hAL)) (CFSG.pCore 2 ↥L)
      (fun a n hn => conjAction_mem_pCore hAL a hn) a
      ((⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
    ((⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) := by
  rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, QuotientGroup.eq,
    mem_pCore_iff_mem_pCoreOf]
  have h := hAL (Subgroup.commutator_mem_commutator a.2 (L.inv_mem hx))
  have h2 : ((((conjAction (le_normalizer_of_commutator_le hAL) a) ⟨x, hx⟩)⁻¹ *
      ⟨x, hx⟩ : ↥L) : G) = (a : G) * x⁻¹ * (a : G)⁻¹ * x⁻¹⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAction_coe, mul_inv_rev, inv_inv,
      mul_assoc]
  rw [h2]
  simpa [commutatorElement_def] using h

private theorem not_dvd_card_pCore_two {L : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (CFSG.pCore 2 ↥L) := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hk]
  intro h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))

private theorem exists_centralizing_mul_mem_pCoreOf {L A : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hA : IsPGroup r A)
    (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) {x : G} (hx : x ∈ L) :
    ∃ (c : ↥L) (n : G), (c : G) ∈ centralizer (A : Set G) ∧
      n ∈ pCoreOf 2 L ∧ x = (c : G) * n := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hinv : ∀ a : ↥A, ∀ n ∈ CFSG.pCore 2 ↥L,
      conjAction (le_normalizer_of_commutator_le hAL) a n ∈ CFSG.pCore 2 ↥L := by
    intro a n hn
    exact conjAction_mem_pCore hAL a hn
  have hcard : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥L) :=
    not_dvd_card_pCore_two (L := L) hr hr2
  have key := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting r hA
    (conjAction (le_normalizer_of_commutator_le hAL)) (CFSG.pCore 2 ↥L) hinv hcard
  have hq : ∀ a : ↥A,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
        (conjAction (le_normalizer_of_commutator_le hAL)) (CFSG.pCore 2 ↥L)
        (fun a n hn => conjAction_mem_pCore hAL a hn) a
        ((⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
      ((⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) :=
    fun a => quotientAction_eq_of_commutator_le hAL a hx
  have hmem : ((⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
      {q : ↥L ⧸ CFSG.pCore 2 ↥L | ∀ a : ↥A,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
          (conjAction (le_normalizer_of_commutator_le hAL)) (CFSG.pCore 2 ↥L)
          (fun a n hn => conjAction_mem_pCore hAL a hn) a q = q} := hq
  rw [key] at hmem
  obtain ⟨c, hc, hcq⟩ := hmem
  have hcx : c⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.1 hcq
  have hcC : (c : G) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have h' := congrArg (fun y : ↥L => (y : G)) (hc ⟨a, ha⟩)
    simp only [conjAction_coe] at h'
    exact mul_inv_eq_iff_eq_mul.1 h'
  have hnp : ((c⁻¹ * ⟨x, hx⟩ : ↥L) : G) ∈ pCoreOf 2 L :=
    (mem_pCore_iff_mem_pCoreOf _).1 hcx
  refine ⟨c, (c : G)⁻¹ * x, hcC, ?_, by group⟩
  simpa using hnp

private theorem inf_centralizer_sup_pCoreOf_eq_aux {L A : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hA : IsPGroup r A)
    (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) :
    (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L := by
  refine le_antisymm (sup_le inf_le_left (Subgroup.map_subtype_le _)) ?_
  intro x hx
  obtain ⟨c, n, hcC, hn, rfl⟩ := exists_centralizing_mul_mem_pCoreOf hr hr2 hA hAL hx
  exact ((L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L).mul_mem
    (Subgroup.mem_sup_left ⟨c.2, hcC⟩) (Subgroup.mem_sup_right hn)

theorem inf_centralizer_sup_pCoreOf_eq_of_commutator_le {L A : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hA : IsPGroup r A)
    (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) :
    (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L :=
  inf_centralizer_sup_pCoreOf_eq_aux hr hr2 hA hAL

end CFSG.GroupTheory
