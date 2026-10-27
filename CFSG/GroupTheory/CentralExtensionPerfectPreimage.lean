module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.GroupTheory.PerfectCoverProduct

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem commute_of_commute_map_of_conj_inv {Γ X : Type*} [Group Γ] [Group X]
    (φ : Γ →* X) (hcen : φ.ker ≤ Subgroup.center Γ) {n : ℕ} (hn : Odd n) {a b t : Γ}
    (hab : Commute (φ a) (φ b)) (ha : φ a ^ n = 1)
    (hta : φ t * φ a * (φ t)⁻¹ = (φ a)⁻¹) (htb : φ t * φ b * (φ t)⁻¹ = φ b) :
    Commute a b := by
  have hcK : ⁅a, b⁆ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hab.commutator_eq
  have hcZ : ⁅a, b⁆ ∈ Subgroup.center Γ := hcen hcK
  have hcn : ⁅a, b⁆ ^ n = 1 := by
    have hcomm : Commute a ⁅a, b⁆ := Subgroup.mem_center_iff.mp hcZ a
    refine (hcomm.commutatorElement_pow_left n).trans ?_
    have hz : a ^ n ∈ Subgroup.center Γ := by
      refine hcen ?_
      rw [MonoidHom.mem_ker, map_pow, ha]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz b).symm
  have hk1 : t * a * t⁻¹ * a ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hta, inv_mul_cancel]
  have hk2 : t * b * t⁻¹ * b⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [htb, mul_inv_cancel]
  have hcinv : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    have h' : ⁅a, b⁆⁻¹ * a = a * ⁅a, b⁆⁻¹ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hcZ) a).symm
    rw [mul_assoc, h', ← mul_assoc, inv_mul_cancel, one_mul]
  have hzconj : t * ⁅a, b⁆ * t⁻¹ = ⁅a, b⁆⁻¹ := by
    rw [conjugate_commutatorElement,
      show t * a * t⁻¹ = (t * a * t⁻¹ * a) * a⁻¹ from by group,
      show t * b * t⁻¹ = (t * b * t⁻¹ * b⁻¹) * b from by group,
      show (t * a * t⁻¹ * a) * a⁻¹ = a⁻¹ * (t * a * t⁻¹ * a) from
        (Subgroup.mem_center_iff.mp (hcen hk1) a⁻¹).symm,
      show (t * b * t⁻¹ * b⁻¹) * b = b * (t * b * t⁻¹ * b⁻¹) from
        (Subgroup.mem_center_iff.mp (hcen hk2) b).symm,
      PerfectCover.commutatorElement_mul_mul_of_mem_center (hcen hk1) (hcen hk2), hcinv]
  have h2 : ⁅a, b⁆ ^ 2 = 1 := by
    have hzc : t * ⁅a, b⁆ * t⁻¹ = ⁅a, b⁆ := by
      have hc : t * ⁅a, b⁆ = ⁅a, b⁆ * t := Subgroup.mem_center_iff.mp hcZ t
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have hzeq : ⁅a, b⁆ = ⁅a, b⁆⁻¹ := hzc.symm.trans hzconj
    rw [pow_two]
    nth_rewrite 2 [hzeq]
    exact mul_inv_cancel _
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hcn
  exact commutatorElement_eq_one_iff_mul_comm.mp hcn

theorem isPerfect_comap_of_isCyclic_quotient {E X : Type*} [Group E] [Group X]
    (φ : E →* X) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center E) (hcom : φ.ker ≤ commutator E)
    {L : Subgroup X} [L.Normal] (hL : ⁅L, L⁆ = L) [IsCyclic (X ⧸ L)] :
    Group.IsPerfect ↥(L.comap φ) := by
  classical
  have hMperf : Group.IsPerfect ↥⁅L.comap φ, L.comap φ⁆ :=
    PerfectCover.isPerfect_commutator_comap φ hφ hcen hL
  have hMR : ⁅L.comap φ, L.comap φ⁆ ≤ L.comap φ :=
    Subgroup.commutator_le_right (H₁ := L.comap φ) (H₂ := L.comap φ)
  have hMker : ⁅L.comap φ, L.comap φ⁆ ≤ ((QuotientGroup.mk' L).comp φ).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (N := L) (φ x)).mpr (hMR hx)
  set Φ : E ⧸ ⁅L.comap φ, L.comap φ⁆ →* X ⧸ L :=
    QuotientGroup.lift ⁅L.comap φ, L.comap φ⁆ ((QuotientGroup.mk' L).comp φ) hMker with hΦdef
  have hΦker : Φ.ker ≤ Subgroup.center (E ⧸ ⁅L.comap φ, L.comap φ⁆) := by
    have hker : ((QuotientGroup.mk' L).comp φ).ker = L.comap φ := by
      ext x
      simp [QuotientGroup.eq_one_iff]
    rw [hΦdef, QuotientGroup.ker_lift, hker]
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨m, hm, k, hk, rfl⟩ := PerfectCover.exists_mul_of_mem_comap φ hφ hL hr
    have hm1 : QuotientGroup.mk' ⁅L.comap φ, L.comap φ⁆ m = 1 := by
      simpa using (QuotientGroup.eq_one_iff (N := ⁅L.comap φ, L.comap φ⁆) m).mpr hm
    rw [map_mul, hm1, one_mul]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' _) (hcen hk))
  have hE' : commutator E ≤ ⁅L.comap φ, L.comap φ⁆ := by
    have hcomm : IsMulCommutative (E ⧸ ⁅L.comap φ, L.comap φ⁆) :=
      Φ.isMulCommutative_of_isCyclic_of_ker_le_center hΦker
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have hKM : φ.ker ≤ ⁅L.comap φ, L.comap φ⁆ := hcom.trans hE'
  have hRM : L.comap φ = ⁅L.comap φ, L.comap φ⁆ := by
    refine le_antisymm ?_ hMR
    intro x hx
    obtain ⟨q, hq, z, hz, rfl⟩ := PerfectCover.exists_mul_of_mem_comap φ hφ hL hx
    exact Subgroup.mul_mem _ hq (hKM hz)
  rw [hRM]
  exact hMperf

end CFSG.GroupTheory
