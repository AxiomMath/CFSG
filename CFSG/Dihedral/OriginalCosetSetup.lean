module

public import CFSG.Dihedral.OriginalInvolutions
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem original_reflection_mem (j : Fin 2) :
    d.s * d.r ^ j.val ∈ d.N :=
  d.centralizer_le_normalizer (d.sylow_le_centralizer
    (d.S.mul_mem d.s_mem_sylow (d.S.pow_mem d.r_mem_sylow _)))

theorem original_reflection_order (j : Fin 2) :
    orderOf (d.s * d.r ^ j.val) = 2 := by
  have hsnot : d.s ∉ Subgroup.zpowers d.r := by
    rintro ⟨k, hk⟩
    have hcomm : Commute d.s d.r := by
      rw [← hk]
      exact (Commute.self_zpow d.r k).symm
    have heq : d.r = d.r⁻¹ := by
      calc
        d.r = d.s * d.r * d.s := by rw [hcomm.eq]; rw [mul_assoc, ← pow_two, d.s_sq]; simp
        _ = d.r⁻¹ := d.dihedral
    have hsq : d.r ^ 2 = 1 := by
      simpa only [pow_two] using mul_eq_one_iff_eq_inv.mpr heq
    have hle := Nat.le_of_dvd (by decide : 0 < 2)
      (orderOf_dvd_of_pow_eq_one hsq)
    rw [d.order_r] at hle
    have hlarge : 4 ≤ 2 ^ (d.n - 1) := by
      calc
        4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ (d.n - 1) := Nat.pow_le_pow_right (by decide) (by have := d.three_le; omega)
    omega
  have hne : d.s * d.r ^ j.val ≠ 1 := by
    intro heq
    apply hsnot
    have heq' : d.s = (d.r ^ j.val)⁻¹ := mul_eq_one_iff_eq_inv.mp heq
    rw [heq']
    exact (Subgroup.zpowers d.r).inv_mem
      ((Subgroup.zpowers d.r).pow_mem (Subgroup.mem_zpowers _) _)
  have hsq : (d.s * d.r ^ j.val) ^ 2 = 1 := by
    fin_cases j
    · simpa using d.s_sq
    · simp only [pow_one, pow_two]
      calc
        (d.s * d.r) * (d.s * d.r) = (d.s * d.r * d.s) * d.r := by group
        _ = 1 := by rw [d.dihedral]; simp
  exact orderOf_eq_prime hsq hne

theorem original_reflection_fixed (j : Fin 2) :
    d.R ⊓ Subgroup.centralizer ({d.s * d.r ^ j.val} : Set G) = d.E j := by
  rw [E, V, Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hcomm⟩
    refine ⟨hx, ?_⟩
    intro y hy
    rcases hy with rfl | rfl
    · have hxC : x ∈ Subgroup.centralizer ({d.t} : Set G) := by
        simpa only [d.centralizer, t] using d.R_le hx
      exact Subgroup.mem_centralizer_iff.mp hxC d.t (by simp)
    · exact hcomm _ rfl
  · rintro ⟨hx, hcomm⟩
    exact ⟨hx, fun y hy => hcomm y (Or.inr hy)⟩

theorem original_opposite_reflection_fixed (hp : d.PureProjectiveNormalizer)
    (i j : Fin 2) (hij : i ≠ j) (hi : Cycles d.N (d.V i)) :
    d.R ⊓ Subgroup.centralizer ({d.s * d.r ^ j.val} : Set G) = d.commonE := by
  obtain ⟨k, _, hother, _⟩ := hp.2.2.2.2
  have hik : i = k := by
    by_contra h
    exact (hother i h).1 hi
  rw [d.original_reflection_fixed, (hother j (by simpa [← hik] using hij.symm)).2]

end CFSG.DihedralBlueprint.OriginalData
