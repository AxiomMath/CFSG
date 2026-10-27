module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.NativeChecks
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.GH74.KGroups.Generic3
public import CFSG.GH74.KGroups.Sz8
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.NativeChecks
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.Sz8TablesInputs
public meta import CFSG.GH74.KGroups.Sz8TablesInputs
public import Certificates.Certificate5128
public import Certificates.Certificate5130
public import Certificates.Certificate113

public section

namespace CFSG.GH74.KGroups.Sz8

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem QS_valid :
    QS.check = true ∧ QS.orderCertificate = 64 :=
  Certificates.certificate5130.1

theorem QS_ok : ValidSchreier QS := QS_valid.1

theorem QS_le_check : leCheck QS QP = true :=
  Certificates.certificate5130.2.2.2.1

theorem QS_le :
    QS.originalSubgroup ≤ QP.originalSubgroup :=
  leCheck_sound QS QP QP_ok QS_le_check

theorem tt_mem_check : QP.sift tt 0 = true :=
  Certificates.certificate5130.2.2.2.2

theorem tt_mem :
    tt ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok tt).2 tt_mem_check

theorem bender_ok : benderCheck (elemsT QS) tt 7 = true :=
  Certificates.certificate5130.2.1

theorem card_S : Nat.card QS.originalSubgroup = 2 ^ 6 := by
  rw [card_group QS QS_ok, QS_valid.2]
  norm_num

theorem center_count :
    ((elemsT QS).filter (fun g => decide (centralIn (elemsT QS) g = true))).length = 8 :=
  Certificates.certificate5130.2.2.1

theorem center_card_S : Nat.card {g : Equiv.Perm (Fin 65) //
    g ∈ QS.originalSubgroup ∧ ∀ y ∈ QS.originalSubgroup, y * g = g * y} = 8 := by
  rw [card_subtype_mem, Nat.card_congr (Equiv.subtypeEquivRight
    (fun g : QS.originalSubgroup => (centralIn_iff QS QS_ok (g : Equiv.Perm (Fin 65))).symm)),
    card_filter QS QS_ok (fun g => centralIn (elemsT QS) g = true), center_count]

theorem QP_le_QA :QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, QA, certificate_originalSubgroup, Subgroup.closure_le]
  intro x hx
  apply Subgroup.subset_closure
  rcases hx with rfl | hx
  · simp
  · rw [Set.mem_singleton_iff] at hx
    simp [hx]

theorem QA_le_normalizer :
    QA.originalSubgroup ≤ Subgroup.normalizer (QP.originalSubgroup : Set (Equiv.Perm (Fin 65))) := by
  rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro σ hσ
  have h1 := List.all_eq_true.1 norm_ok σ hσ
  simp only [Bool.and_eq_true] at h1
  apply mem_normalizer_of_conj_mem
  intro x hx
  have hle : Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 65))) ≤
      QP.originalSubgroup.comap (MulAut.conj σ).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact (mem_iff_sift QP QP_ok _).2 h1.1
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (mem_iff_sift QP QP_ok _).2 h1.2
  exact hle (QP_closure ▸ hx)

theorem inner_two :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 64 = 1 → τ ∈ QP.originalSubgroup := by
  intro τ hτ h64
  have : (QP.originalSubgroup.subgroupOf QA.originalSubgroup).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer QP_le_QA).2 QA_le_normalizer
  have hidx : (QP.originalSubgroup.subgroupOf QA.originalSubgroup).index = 3 := by
    have h1 := Subgroup.card_mul_index (QP.originalSubgroup.subgroupOf QA.originalSubgroup)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QP_le_QA).toEquiv, card_group QP QP_ok,
      QP_valid.2, card_group QA QA_ok, QA_valid.2] at h1
    omega
  set t : QA.originalSubgroup := ⟨τ, hτ⟩
  have h3 := Subgroup.pow_index_mem (QP.originalSubgroup.subgroupOf QA.originalSubgroup) t
  rw [hidx] at h3
  have ht : t ^ 64 = 1 := Subtype.ext (by simpa [t] using h64)
  have he : t = t ^ 64 * ((t ^ 3)⁻¹) ^ 21 := by group
  have hmem : t ∈ QP.originalSubgroup.subgroupOf QA.originalSubgroup := by
    rw [he, ht, one_mul]
    exact pow_mem (inv_mem h3) _
  exact Subgroup.mem_subgroupOf.1 hmem

section Tables

variable {K : Type} [Group K]

theorem card_K'
    (e : K ≃* QP.originalSubgroup) : Nat.card K = 2 ^ 6 * 455 := by
  rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  norm_num

theorem bender_card
    (h : LieModel K .twistedB2 0 2 3) (T : Subgroup K) (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) : Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set K)) = 8 := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  have : Finite K := finite_K e
  exact card_center_of_model QP.originalSubgroup e QS.originalSubgroup QS_le card_S (card_K' e)
    (by decide) 8 center_card_S T hT hTi

theorem out_inner
    (h : LieModel K .twistedB2 0 2 3) (φ : MulAut K) (n : ℕ)
    (hφ : φ ^ 2 ^ n = 1) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  obtain ⟨M, hP, hA⟩ := autModel e
  have hs := inner_two
  have hN : Nat.card (MulAut K) = 2 ^ 6 * 1365 := by rw [card_mulAut e]; norm_num
  exact M.out_inner_two hN (by decide) (fun τ hτ h2 => by
    rw [hP]; rw [hA] at hτ; exact hs τ hτ h2) φ n hφ

theorem bender
    (h : LieModel K .twistedB2 0 2 3) (T : Subgroup K) (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) :
    (∀ x ∈ T, x ^ 2 = 1 → ∀ y ∈ T, y * x = x * y) ∧
    (∀ a ∈ T ⊓ Subgroup.centralizer (T : Set K), a ^ 2 = 1) ∧
    (T ⊓ Subgroup.centralizer (T : Set K) ≤ ⁅T, T⁆) ∧
    (∃ x : K, x ∈ Subgroup.normalizer (T : Set K) ∧
      ∀ a ∈ T ⊓ Subgroup.centralizer (T : Set K), ∀ b ∈ T ⊓ Subgroup.centralizer (T : Set K),
        a ≠ 1 → b ≠ 1 → ∃ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = b) := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  have : Finite K := finite_K e
  have hs := benderCheck_sound QS QS_ok bender_ok
  exact benderTable_of_model QP.originalSubgroup e QS.originalSubgroup QS_le card_S (card_K' e)
    (by decide)
    hs.1 hs.2.1 hs.2.2.1 tt tt_mem hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 T hT hTi

end Tables

end CFSG.GH74.KGroups.Sz8
