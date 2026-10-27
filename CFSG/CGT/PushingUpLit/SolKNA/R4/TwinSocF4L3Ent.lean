module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Two
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Elt

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal]
  (hC : Subgroup.centralizer (T : Set A) = ⊥) {R : Subgroup A} {S : Sylow 2 R} {z : A}
  (hd : TightDatum R S z) {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
  (h4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) {e : ↥T ≃* projectiveSL 3 K} (F : L3Frame T z K e)

include hC hd hodd h4 h2

theorem l3_entry {r : ℕ} (hr : 4 ≤ r) (hcls : TightClsR r A R S z) :
    ∃ l ν : Kˣ, orderOf l = 2 ^ (r - 1) ∧ ¬ 2 ^ r ∣ Nat.card Kˣ ∧ F.scal l ∈ sylowSet S ∧
      ∃ b ∈ sylowSet S, F.ι b = conjAut 3 K (sigMat ν) * dualAut 3 K := by
  obtain ⟨a, b, haS, hbS, hao, hba, hbb⟩ := exists_quat_full_of_datum (by omega) hcls
  have haR : a ∈ R := mem_sylowSet_le S haS
  have hbR : b ∈ R := mem_sylowSet_le S hbS
  obtain ⟨-, c, hac⟩ := a_form hC hd hodd h4 h2 F haR (by omega : 3 ≤ r - 1) hao
  have hasq : a * a ≠ 1 := by
    intro h
    have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hao] at h1
    have h3 : 2 ^ 3 ∣ 2 ^ (r - 1) := pow_dvd_pow 2 (by omega)
    have := Nat.le_of_dvd (by norm_num) (h3.trans h1)
    omega
  have hb4 : b ^ 4 = 1 := by
    have h1 : b ^ 4 = (b * b) * (b * b) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [h1, hbb, ← pow_add, ← two_mul, ← pow_succ', show r - 2 + 1 = r - 1 by omega, ← hao,
      pow_orderOf_eq_one]
  obtain ⟨-, ν, hbν⟩ := b_form hC hd hodd h4 h2 F hac hbR hba hasq hb4
  have hac' : F.scal c = a := hac
  refine ⟨c ^ 3, ν, ?_, not_dvd_card_units hC hd F hr hcls hbS hbν, ?_, b, hbS, hbν⟩
  · apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      have h1 : F.scal (c ^ 2 ^ (r - 1)) = 1 := by
        rw [map_pow, hac', ← hao, pow_orderOf_eq_one]
      obtain ⟨ω, hω3, hω⟩ := F.scal_eq_one h1
      rw [← pow_mul, mul_comm, pow_mul, hω, hω3]
    · have h1 : orderOf (F.scal (c ^ 3)) ∣ orderOf (c ^ 3) := orderOf_map_dvd F.scal _
      rwa [map_pow, hac', Nat.Coprime.orderOf_pow (by rw [hao]; exact Nat.Coprime.pow_left _ (by norm_num)),
        hao] at h1
  · rw [map_pow, hac']
    exact pow_mem haS 3

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
