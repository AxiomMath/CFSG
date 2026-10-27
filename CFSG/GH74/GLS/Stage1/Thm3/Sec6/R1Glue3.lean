module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue1

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace Std4r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem Z_inv (h : Std4r1 G z S K F) {x : G} (hxS : x ∈ S) (hxc : ∀ s ∈ S, x * s = s * x)
    (hx2 : x * x = 1) : x = 1 ∨ x = z := by
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  obtain ⟨S', hS'⟩ := hcl.2.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'top : M.Syl2In (S' : Subgroup G) ⊤ :=
    ⟨le_top, S'.isPGroup', by simpa [Subgroup.relIndex_top_right] using Sylow.not_dvd_index S'⟩
  obtain ⟨c, -, hc⟩ := h.S_top.exists_conj hS'top
  have key : ∀ y ∈ S, (∀ s ∈ S, y * s = s * y) → y * y = 1 → c⁻¹ * y * c ∈ zpowers z := by
    intro y hy hyc hy2
    rw [← hS']
    refine ⟨?_, ?_, ?_⟩
    · rw [hc, M.mem_cj]
      have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
      rw [e]; exact hy
    · intro s' hs'
      rw [hc, M.mem_cj] at hs'
      have h1 := hyc _ hs'
      calc s' * (c⁻¹ * y * c) = c⁻¹ * ((c * s' * c⁻¹) * y) * c := by group
        _ = c⁻¹ * (y * (c * s' * c⁻¹)) * c := by rw [h1]
        _ = c⁻¹ * y * c * s' := by group
    · calc (c⁻¹ * y * c) ^ 2 = (c⁻¹ * y * c) * (c⁻¹ * y * c) := pow_two _
        _ = c⁻¹ * (y * y) * c := by group
        _ = 1 := by rw [hy2]; group
  have hzc : ∀ s ∈ S, z * s = s * z := fun s hs => h.z_cent hs
  have hz2 := h.z_sq
  have hcz : c⁻¹ * z * c = z := by
    rcases (M.mem_zpowers_of_sq hz2).1 (key z h.z_mem_S hzc hz2) with e | e
    · exfalso
      apply h.z_ne
      calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
        _ = 1 := by rw [e]; group
    · exact e
  rcases (M.mem_zpowers_of_sq hz2).1 (key x hxS hxc hx2) with e | e
  · left
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [e]; group
  · right
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [e]
      _ = c * (c⁻¹ * z * c) * c⁻¹ := by rw [hcz]
      _ = z := by group

theorem Z_cyc (h : Std4r1 G z S K F) : IsCyclic ↥(center ↥S) := by
  have hS : IsPGroup 2 ↥S := h.S_pgroup
  have hZ : IsPGroup 2 ↥(center ↥S) := hS.to_subgroup (center ↥S)
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      ↥(center ↥S) := by
    intro first second _
    have key : ∀ w : CFSG.DisconnectedInvolutionGraph.Helpers.Involution ↥(center ↥S),
        ((w : ↥(center ↥S)) : ↥S).1 = z := by
      intro w
      have hw2 : ((w : ↥(center ↥S)) : ↥S).1 * ((w : ↥(center ↥S)) : ↥S).1 = 1 := by
        have h1 := w.2
        rw [← orderOf_coe (w : ↥(center ↥S)), ← orderOf_coe ((w : ↥(center ↥S)) : ↥S)] at h1
        exact mul_self_eq_one_of_orderOf_eq_two h1
      have hw1 : ((w : ↥(center ↥S)) : ↥S).1 ≠ 1 := by
        have h1 := w.2
        rw [← orderOf_coe (w : ↥(center ↥S)), ← orderOf_coe ((w : ↥(center ↥S)) : ↥S)] at h1
        exact ne_one_of_orderOf_eq_two h1
      refine (h.Z_inv ((w : ↥(center ↥S)) : ↥S).2 ?_ hw2).resolve_left hw1
      intro s hs
      have := Subgroup.mem_center_iff.mp (w : ↥(center ↥S)).2 ⟨s, hs⟩
      exact (congrArg Subtype.val this).symm
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [key first, key second]
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hZ hrank with
    hc | ⟨e, he, ⟨φ⟩⟩
  · exact hc
  · exfalso
    have hcomm : (QuaternionGroup.a (1 : ZMod (2 * 2 ^ e))) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
      apply φ.injective
      rw [map_mul, map_mul]
      have hc : ∀ u v : ↥(center ↥S), u * v = v * u := fun u v =>
        Subtype.ext (Subgroup.mem_center_iff.mp v.2 u)
      exact hc _ _
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
    have h2 : ((0 : ZMod (2 * 2 ^ e)) - 1) = 0 + 1 := QuaternionGroup.xa.inj hcomm
    have h3 : (2 : ZMod (2 * 2 ^ e)) = 0 := by
      linear_combination (-1 : ZMod (2 * 2 ^ e)) * h2
    have h4 : (2 * 2 ^ e : ℕ) ∣ 2 := by
      have := (ZMod.natCast_eq_zero_iff 2 (2 * 2 ^ e)).mp (by exact_mod_cast h3)
      exact this
    have h5 := Nat.le_of_dvd (by norm_num) h4
    have h6 : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega

end Std4r1

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
