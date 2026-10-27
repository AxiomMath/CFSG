module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUKey
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightBUnitaryRow

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Perm

variable {K : Type} [Field K] {N : ℕ}

theorem permSp_mul_eightU (π ρ : Equiv.Perm (Fin N)) :
    permSp K (π * ρ) = permSp K π * permSp K ρ := by
  apply mat_injective
  rw [map_mul, mat_permSp, mat_permSp, mat_permSp]
  ext a b
  rw [spIncl_apply, Matrix.mul_apply, Finset.sum_eq_single (Sum.map ρ ρ b)]
  · rw [spIncl_apply, spIncl_apply, ite_eq_left rfl, mul_one]
    rcases b with j | j <;> rfl
  · intro c _ hc
    rw [spIncl_apply (σ := (ρ : Fin N → Fin N)) c b, ite_eq_right hc, mul_zero]
  · simp

theorem permSp_one_eightU : permSp K (1 : Equiv.Perm (Fin N)) = 1 := by
  apply mat_injective
  rw [mat_permSp, map_one]
  ext a b
  rw [spIncl_apply, Matrix.one_apply]
  rcases b with j | j <;> rfl

theorem permSp_inv_eightU (π : Equiv.Perm (Fin N)) : permSp K π⁻¹ = (permSp K π)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← permSp_mul_eightU, inv_mul_cancel, permSp_one_eightU]

theorem permSp_conj_swap (π : Equiv.Perm (Fin N)) (a b : Fin N) :
    permSp K π * permSp K (Equiv.swap a b) * (permSp K π)⁻¹ =
      permSp K (Equiv.swap (π a) (π b)) := by
  rw [Equiv.swap_apply_apply, permSp_mul_eightU, permSp_mul_eightU, permSp_inv_eightU]

theorem exists_perm_eq_zero_one_eightU {k l : Fin 4} (hkl : k ≠ l) :
    ∃ π : Equiv.Perm (Fin 4), π 0 = k ∧ π 1 = l := by
  refine ⟨Equiv.swap 0 k * Equiv.swap 1 (Equiv.swap 0 k l), ?_, ?_⟩
  · have h1 : Equiv.swap 0 k l ≠ 0 := by
      intro h
      apply hkl
      have := congrArg (Equiv.swap 0 k) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact this.symm
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm h1),
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

end Perm

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem commute_permSp_swap_zero_one_of_mem (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* StatedSp 4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin 4, NsKindSp e t k .unitaryEven) {z : G}
    (hz : z ∈ centralizerPerfectCore (modelToG e (nsTorusSp K (0 : Fin 4) ⊔ nsTorusSp K 1))) :
    ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * z =
      z * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) := by
  obtain ⟨F, _, _, _, hF, ι, hι, hpar⟩ :=
    exists_nsUniParam_even_of_three_le hset 3 hK le_rfl e ht hKt hroot
  obtain ⟨x, hx, rfl⟩ := (hpar 0).some.exists_eq_of_mem_overlap hF (by decide) hz
  exact commute_permSp_swap_zero_one hset hK hF (hpar 0).some (hpar 2).some ht hKt x hx

theorem commute_permSp_swap_of_mem_overlap (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* StatedSp 4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin 4, NsKindSp e t k .unitaryEven) {k l : Fin 4} (hkl : k ≠ l) {z : G}
    (hz : z ∈ centralizerPerfectCore (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l))) :
    ((e.symm (permSp K (Equiv.swap k l)) : L) : G) * z =
      z * ((e.symm (permSp K (Equiv.swap k l)) : L) : G) := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_perm_eq_zero_one_eightU hkl
  have hmap : (nsTorusSp K (0 : Fin 4) ⊔ nsTorusSp K 1).map (MulAut.conj (permSp K π)).toMonoidHom =
      nsTorusSp K k ⊔ nsTorusSp K l := by
    rw [Subgroup.map_sup, map_conj_permSp_nsTorusSp, map_conj_permSp_nsTorusSp, hπ0, hπ1]
  rw [← hmap, UnitaryPilot.centralizerPerfectCore_modelToG_map_conj] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hc := commute_permSp_swap_zero_one_of_mem hset hK e ht hKt hroot hz₀
  have hw : permSp K (Equiv.swap k l) =
      permSp K π * permSp K (Equiv.swap (0 : Fin 4) 1) * (permSp K π)⁻¹ := by
    rw [permSp_conj_swap, hπ0, hπ1]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hw, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  calc ((e.symm (permSp K π) : L) : G) * ((e.symm (permSp K (Equiv.swap 0 1)) : L) : G) *
        ((e.symm (permSp K π) : L) : G)⁻¹ *
          (((e.symm (permSp K π) : L) : G) * z₀ * ((e.symm (permSp K π) : L) : G)⁻¹) =
      ((e.symm (permSp K π) : L) : G) *
        (((e.symm (permSp K (Equiv.swap 0 1)) : L) : G) * z₀) *
          ((e.symm (permSp K π) : L) : G)⁻¹ := by group
    _ = ((e.symm (permSp K π) : L) : G) *
        (z₀ * ((e.symm (permSp K (Equiv.swap 0 1)) : L) : G)) *
          ((e.symm (permSp K π) : L) : G)⁻¹ := by rw [hc]
    _ = _ := by group

end Swap

end CFSG.SeitzReduction.SymplecticPilot
