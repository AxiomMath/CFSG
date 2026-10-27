module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem inv_mul_eq_inv_mul_of_mul_eq {l k c d : G}
    (h : l * c = k * d) (hcomm : k * l = l * k) :
    l⁻¹ * d = k⁻¹ * c := by
  have hd : d = k⁻¹ * (l * c) := by
    rw [h, inv_mul_cancel_left]
  have hcomm' : l⁻¹ * k⁻¹ = k⁻¹ * l⁻¹ := by
    have h2 := congrArg (fun z : G => z⁻¹) hcomm
    rwa [mul_inv_rev, mul_inv_rev] at h2
  rw [hd]
  calc l⁻¹ * (k⁻¹ * (l * c)) = (l⁻¹ * k⁻¹) * (l * c) := (mul_assoc _ _ _).symm
    _ = (k⁻¹ * l⁻¹) * (l * c) := by rw [hcomm']
    _ = k⁻¹ * (l⁻¹ * (l * c)) := mul_assoc _ _ _
    _ = k⁻¹ * c := by rw [inv_mul_cancel_left]

theorem mul_mem_centralizer_inf_of_eq {L K : Subgroup G}
    (hLK : L ≤ Subgroup.centralizer (K : Set G)) {l k c d : G} (hl : l ∈ L) (hk : k ∈ K)
    (hc : c ∈ Subgroup.centralizer (L : Set G))
    (hd : d ∈ Subgroup.centralizer (K : Set G)) (h : l * c = k * d) :
    l⁻¹ * d ∈ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  have hkl : k * l = l * k := Subgroup.mem_centralizer_iff.mp (hLK hl) k hk
  have heq : l⁻¹ * d = k⁻¹ * c := inv_mul_eq_inv_mul_of_mul_eq h hkl
  have hkC : k ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hLK hy) k hk).symm
  have hlK : l⁻¹ ∈ Subgroup.centralizer (K : Set G) := Subgroup.inv_mem _ (hLK hl)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkC) hc
  · exact Subgroup.mul_mem _ hlK hd

theorem inf_centralizer_sup_eq_bot {L K : Subgroup G}
    (hLK : L ≤ Subgroup.centralizer (K : Set G))
    (hZL : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hZK : K ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    (L ⊔ K) ⊓ (Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (K : Set G)) = ⊥ := by
  have hKL : K ≤ Subgroup.centralizer (L : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hLK hy) k hk).symm
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzLK, hzC⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨hzCL, hzCK⟩ := Subgroup.mem_inf.mp hzC
  have hprod : (↑(L ⊔ K) : Set G) = (L : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L K
      (hKL.trans (Subgroup.centralizer_le_normalizer (L : Set G)))
  have hz' : z ∈ (L : Set G) * (K : Set G) := by rw [← hprod]; exact hzLK
  obtain ⟨l, hl, k, hk, rfl⟩ := hz'
  have hlC : l ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : y * (l * k) = (l * k) * y := Subgroup.mem_centralizer_iff.mp hzCL y hy
    have h2 : y * k = k * y := Subgroup.mem_centralizer_iff.mp (hKL hk) y hy
    have h3 : y * l * k = l * y * k := by
      calc y * l * k = y * (l * k) := mul_assoc _ _ _
        _ = (l * k) * y := h1
        _ = l * (k * y) := mul_assoc _ _ _
        _ = l * (y * k) := by rw [h2]
        _ = l * y * k := (mul_assoc _ _ _).symm
    exact mul_right_cancel h3
  have hl1 : l = 1 := by
    have hmem : l ∈ L ⊓ Subgroup.centralizer (L : Set G) := ⟨hl, hlC⟩
    rw [hZL, Subgroup.mem_bot] at hmem
    exact hmem
  have hkC : k ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : y * (l * k) = (l * k) * y := Subgroup.mem_centralizer_iff.mp hzCK y hy
    rw [hl1] at h1
    simpa using h1
  have hk1 : k = 1 := by
    have hmem : k ∈ K ⊓ Subgroup.centralizer (K : Set G) := ⟨hk, hkC⟩
    rw [hZK, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hl1, hk1]
  simp

end CFSG.GroupTheory

end
