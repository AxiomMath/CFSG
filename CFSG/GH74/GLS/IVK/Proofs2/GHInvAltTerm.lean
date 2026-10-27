module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltMain
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Equiv Equiv.Perm

section Z

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem terminal_map {N : Type*} [Group N] (ι : N →* Perm Ω) (hι : Function.Injective ι)
    (hA : alternatingGroup Ω ≤ ι.range) (K : Subgroup N)
    (hsub : ∀ y : N, orderOf y = 2 → (∀ k ∈ K, k * y = y * k) →
      (K.subgroupOf (Subgroup.centralizer {y})).IsSubnormal) :
    Terminal ι.range (K.map ι) := by
  intro y' hy' hy2 hy1 hyK F hF5 hyF hKF hK1
  obtain ⟨y, rfl⟩ := hy'
  have hyy : y * y = 1 := hι (by rw [map_mul, map_one]; exact hy2)
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1'
  have hcomm : ∀ k ∈ K, k * y = y * k := by
    intro k hk
    apply hι
    rw [map_mul, map_mul]
    exact (hyK (ι k) (Subgroup.mem_map_of_mem ι hk)).symm
  have hK1' : K ≠ ⊥ := fun h => hK1 (by rw [h, Subgroup.map_bot])
  have hsubK := hsub y hord hcomm
  let H : Subgroup N := (altOn F).comap ι
  have hHC : H ≤ Subgroup.centralizer {y} := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := commute_of_symOn_of_fixes (altOn_le_symOn F hh) hyF
    apply hι
    rw [map_mul, map_mul]
    exact this
  have hKH : K ≤ H := fun k hk => hKF (Subgroup.mem_map_of_mem ι hk)
  have hsubH : (K.subgroupOf H).IsSubnormal := by
    have h1 := hsubK.comap (Subgroup.inclusion hHC)
    have h2 : (K.subgroupOf (Subgroup.centralizer {y})).comap (Subgroup.inclusion hHC) =
        K.subgroupOf H := by
      ext h
      rfl
    rwa [h2] at h1
  let ψ : H →* altOn F := (ι.comp H.subtype).codRestrict (altOn F) (fun h => h.2)
  have hψ : Function.Bijective ψ := by
    constructor
    · intro h₁ h₂ h
      exact Subtype.ext (hι (congrArg Subtype.val h))
    · intro g
      obtain ⟨x, hx⟩ := hA (altOn_le_alternatingGroup F g.2)
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      show ι x ∈ altOn F
      rw [hx]
      exact g.2
  have hsimple : IsSimpleGroup H :=
    (MulEquiv.ofBijective ψ hψ).isSimpleGroup_congr.2 (isSimpleGroup_altOn hF5)
  rcases hsubH.eq_bot_or_top_of_isSimpleGroup hsimple with h | h
  · exfalso
    apply hK1'
    rw [eq_bot_iff]
    intro k hk
    have : (⟨k, hKH hk⟩ : H) ∈ K.subgroupOf H := hk
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext_iff.1 this
  · have hHK : H ≤ K := by
      intro k hk
      have : (⟨k, hk⟩ : H) ∈ K.subgroupOf H := by rw [h]; trivial
      exact this
    have hKeq : K = H := le_antisymm hKH hHK
    rw [hKeq, Subgroup.map_comap_eq]
    exact inf_eq_right.2 (altOn_le_alternatingGroup F |>.trans hA)

end Z

end CFSG.GH74.GLS.IVK.GHInv
