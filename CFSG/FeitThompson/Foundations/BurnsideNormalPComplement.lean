module

import CFSG.FeitThompson.Foundations.TrivialFocalNormalPComplement
import CFSG.FeitThompson.Foundations.CentralSylowFocalTrivial
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
public import Mathlib.GroupTheory.Focal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}

theorem ker_transferFocal_isComplement'_of_normalizer_comm
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) :
    P.transferFocal.ker.IsComplement' P := by
  have h : (↑(Sylow.ofCard P hP) : Subgroup G).focalSubgroup = ⊥ := by
    rw [Sylow.coe_ofCard]; exact focalSubgroup_eq_bot_of_normalizer_comm hP hcomm
  have h2 := ker_transferFocal_isComplement' (Sylow.ofCard P hP) h
  rwa [Sylow.coe_ofCard] at h2

theorem index_ker_transferFocal_of_normalizer_comm
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) :
    P.transferFocal.ker.index = Nat.card P :=
  (ker_transferFocal_isComplement'_of_normalizer_comm hP hcomm).symm.index_eq_card

theorem coprime_card_ker_transferFocal_of_normalizer_comm
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) :
    Nat.Coprime (Nat.card P.transferFocal.ker) p := by
  have h : (↑(Sylow.ofCard P hP) : Subgroup G).focalSubgroup = ⊥ := by
    rw [Sylow.coe_ofCard]; exact focalSubgroup_eq_bot_of_normalizer_comm hP hcomm
  have h2 := coprime_card_ker_transferFocal (Sylow.ofCard P hP) h
  rwa [Sylow.coe_ofCard] at h2

theorem exists_normal_pComplement_of_normalizer_comm
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.Coprime (Nat.card K) p ∧ K.index = Nat.card P ∧
      (K : Set G) * (P : Set G) = Set.univ ∧ K ⊓ P = ⊥ :=
  ⟨P.transferFocal.ker, inferInstance,
    coprime_card_ker_transferFocal_of_normalizer_comm hP hcomm,
    index_ker_transferFocal_of_normalizer_comm hP hcomm,
    (ker_transferFocal_isComplement'_of_normalizer_comm hP hcomm).mul_eq,
    disjoint_iff.mp (ker_transferFocal_isComplement'_of_normalizer_comm hP hcomm).disjoint⟩

theorem exists_normal_pComplement_of_conj_comm
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n : G, MulAut.conj n⁻¹ • P = P → ∀ x ∈ P, n * x = x * n) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.Coprime (Nat.card K) p ∧ K.index = Nat.card P ∧
      (K : Set G) * (P : Set G) = Set.univ ∧ K ⊓ P = ⊥ :=
  exists_normal_pComplement_of_normalizer_comm hP fun n hn =>
    hcomm n (mem_normalizer_iff_conj_inv_smul_eq.mp hn)

theorem exists_normal_pComplement_sylow_of_normalizer_comm (P : Sylow p G)
    (hcomm : ∀ n ∈ normalizer ((P : Subgroup G) : Set G), ∀ x ∈ (P : Subgroup G), n * x = x * n) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.Coprime (Nat.card K) p ∧
      K.index = Nat.card (P : Subgroup G) ∧
      (K : Set G) * ((P : Subgroup G) : Set G) = Set.univ ∧ K ⊓ (P : Subgroup G) = ⊥ :=
  exists_normal_pComplement_of_normalizer_comm P.card_eq_multiplicity hcomm

end CFSG.FeitThompson
