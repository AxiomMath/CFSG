module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSzEight
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

theorem exists_omega_of_isCoverOverTwo_sz {Y : Type*} [Group Y] [Finite Y]
    (h : IsCoverOverTwo Y (Open.Sz 1)) (T : Sylow 2 Y) :
    ∃ A : Subgroup Y, A ≤ (T : Subgroup Y) ∧ Nat.card A = 16 ∧ (∀ x ∈ A, x ^ 2 = 1) ∧
      ∀ x ∈ (T : Subgroup Y), x ^ 2 = 1 → x ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπs, hKZ, hKC, hK2⟩ := h
  have : Finite (Open.Sz 1) := Finite.of_surjective π hπs
  obtain ⟨hsimp, hna⟩ := sz_one_simple_nonabelian
  obtain ⟨-, hker⟩ := isQuasisimple_of_isCoverOverTwo (hX := hsimp) hna hπs hKZ hKC
  have hZ2 : ∀ z ∈ center Y, z ^ 2 = 1 := by
    intro z hz
    rw [← hker] at hz
    have h1 := Subgroup.orderOf_dvd_natCard π.ker hz
    rw [hK2] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hB := Open.bender_suzuki_borel_full 1 le_rfl
  set Q : Sylow 2 (Open.Sz 1) := T.mapSurjective hπs with hQ
  obtain ⟨-, -, hZcard, -⟩ := AschbacherToolkit.Bender.benderBorel_sylowCenter hB Q
  have hkerp : IsPGroup 2 π.ker := IsPGroup.of_card (n := 1) (by rw [hK2, pow_one])
  have hkerT : π.ker ≤ (T : Subgroup Y) := by
    have hp : IsPGroup 2 ↥((T : Subgroup Y) ⊔ π.ker) :=
      T.isPGroup'.to_sup_of_normal_right hkerp
    rw [← T.3 hp le_sup_left]
    exact le_sup_right
  set A := (sylowCenter (Q : Subgroup (Open.Sz 1))).comap π with hA
  have hAT : A ≤ (T : Subgroup Y) := by
    intro x hx
    have hxQ : π x ∈ (Q : Subgroup (Open.Sz 1)) := (mem_sylowCenter.mp hx).1
    obtain ⟨t, ht, htx⟩ := mem_map.mp hxQ
    have h1 : t⁻¹ * x ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, htx, inv_mul_cancel]
    rw [show x = t * (t⁻¹ * x) by group]
    exact mul_mem ht (hkerT h1)
  have hb : ∀ x ∈ A, ∀ y ∈ (T : Subgroup Y), x * y * x⁻¹ * y⁻¹ ∈ center Y := by
    intro x hx y hy
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hyQ : π y ∈ (Q : Subgroup (Open.Sz 1)) := mem_map_of_mem π hy
    rw [((mem_sylowCenter.mp hx).2 (π y) hyQ).symm]
    group
  refine ⟨A, hAT, ?_, fun x hx => (Goldschmidt.MFSz8.comm_and_sq_of_benderBorel hB
    (by norm_num) π hπs hker hZ2 T (hAT hx) (hAT hx) (hb x hx) (hb x hx)).2, ?_⟩
  · rw [hA, CFSG.ClassicalInvolution.QuaternionStructure.natCard_comap_eq π hπs, hK2, hZcard]
    norm_num
  · intro x hx hx2
    have hxQ : π x ∈ (Q : Subgroup (Open.Sz 1)) := mem_map_of_mem π hx
    exact AschbacherToolkit.Goldschmidt.mem_sylowCenter_of_sq_eq_one hB (by norm_num) Q hxQ
      (by rw [← map_pow, hx2, map_one])

end CFSG.ComponentClassification.FooteLit
