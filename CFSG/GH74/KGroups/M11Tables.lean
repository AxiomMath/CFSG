module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.M11
public import CFSG.RankThree.Asc83Table.GL23
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.M11
public import CFSG.GH74.KGroups.M11TablesInputs
public meta import CFSG.GH74.KGroups.M11TablesInputs
public import Certificates.Certificate5125
public import Certificates.Certificate5126

public section

namespace CFSG.GH74.KGroups.M11

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem QS_valid :
    QS.check = true ∧ QS.orderCertificate = 16 :=
  Certificates.certificate5126.1

theorem QS_ok : ValidSchreier QS := QS_valid.1

theorem QS_closure : QS.originalSubgroup = Subgroup.closure {sR, sT} := by
  rw [QS, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QS_le_check : leCheck QS Q = true :=
  Certificates.certificate5126.2.2.2.2

theorem QS_le :
    QS.originalSubgroup ≤ Q.originalSubgroup :=
  leCheck_sound QS Q Q_ok QS_le_check

theorem inv_ok :
    invConjCheck (elemsT Q) t0 = true :=
  Certificates.certificate5126.2.1

theorem small_ok :
    smallCheck (elemsT QS) s0 = true :=
  Certificates.certificate5126.2.2.1

theorem sd16_rels :
    sR ^ 8 = 1 ∧ sT ^ 2 = 1 ∧ sT * sR * sT⁻¹ = sR ^ 3 ∧
    (∀ i : Fin 8, ∀ e : Fin 2, sR ^ (i : ℕ) * sT ^ (e : ℕ) = 1 → i = 0 ∧ e = 0) :=
  Certificates.certificate5126.2.2.2.1

theorem card_S : Nat.card QS.originalSubgroup = 2 ^ 4 := by
  rw [card_group QS QS_ok, QS_valid.2]
  norm_num

theorem equiv_of_sporadic {K : Type} [Group K] (h : NativeSporadic.IsSporadic K .M11) :
    Nonempty (K ≃* Q.originalSubgroup) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (MulEquiv.subgroupCongr Q_subgroup.symm)⟩

theorem out_trivial
    {K : Type} [Group K] (h : NativeSporadic.IsSporadic K .M11) (φ : MulAut K) :
    ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨M, hP, hA⟩ := autModel h
  exact M.inner_of_le (by rw [hA, hP]) φ

section Tables

variable {K : Type} [Group K] (e : K ≃* Q.originalSubgroup)

include e

theorem card_K : Nat.card K = 2 ^ 4 * 495 := by
  rw [Nat.card_congr e.toEquiv, card_group Q Q_ok, Q_valid.2]
  norm_num

theorem finite_K' : Finite K := Finite.of_equiv Q.originalSubgroup e.symm.toEquiv

theorem one_class :
    ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v :=
  one_class_of_model Q.originalSubgroup e t0 (invConjCheck_sound Q Q_ok inv_ok)

theorem sylow_sd16 : ∀ T : Sylow 2 K,
    Nonempty (↥(T : Subgroup K) ≃* CFSG.Open.SemidihedralGroup 4) := by
  have : Finite K := finite_K' e
  have hrel := sd16_rels
  have hsR : sR ∈ QS.originalSubgroup := by
    rw [QS_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hsT : sT ∈ QS.originalSubgroup := by
    rw [QS_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨eS⟩ := CFSG.RankThree.Asc83Table.nonempty_mulEquiv_semidihedral
    (H := QS.originalSubgroup) (by rw [card_S]; norm_num) hsR hsT hrel.1 hrel.2.1 hrel.2.2.1
    hrel.2.2.2
  intro T
  obtain ⟨eT⟩ := sylow_equiv_of_model Q.originalSubgroup e QS.originalSubgroup QS_le card_S
    (card_K e) (by decide) (T : Subgroup K) T.isPGroup' T.not_dvd_index
  exact ⟨eT.trans eS⟩

theorem smallTable
    (T : Subgroup K) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    (∀ x ∈ T, x ^ 2 = 1 → ∃ k : K, k⁻¹ * x * k ∈ T ∧
      ∀ y ∈ T, y * (k⁻¹ * x * k) = (k⁻¹ * x * k) * y) ∧
    (∀ a ∈ T, (∀ y ∈ T, y * a = a * y) → a ^ 2 = 1 → a ∈ ⁅T, T⁆) ∧
    (∃ s : K, ∀ a ∈ T, (∀ y ∈ T, y * a = a * y) → a ^ 2 = 1 → a = 1 ∨ a = s) := by
  have : Finite K := finite_K' e
  have hs := smallCheck_sound QS QS_ok small_ok
  exact smallTable_of_model Q.originalSubgroup e QS.originalSubgroup QS_le card_S (card_K e)
    (by decide) (one_class e) s0 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 T hT hTi

end Tables

end CFSG.GH74.KGroups.M11
