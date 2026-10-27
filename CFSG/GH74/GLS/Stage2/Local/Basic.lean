module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

section Basic

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem Stage1Data.base (h : Stage1Data G z S k) : Stage1Base G z S := by
  cases h with
  | g2 h => exact h.base
  | m12 h => exact h.base
  | psp4 h => obtain ⟨q, L₁, L₂, h⟩ := h; exact h.pair.base
  | l4 ε h => obtain ⟨q, L₁, L₂, h⟩ := h; exact h.pair.base
  | mcl h => obtain ⟨n, _, h⟩ := h; exact h.base
  | ly h => obtain ⟨n, _, h⟩ := h; exact h.base

theorem Stage2Ctx.S_le_Cen (h : Stage2Ctx G z k S) : S ≤ Cen z := h.sylow.le

theorem Stage2Ctx.S_comm_z (h : Stage2Ctx G z k S) {s : G} (hs : s ∈ S) : s * z = z * s := by
  have := h.S_le_Cen hs
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem Stage2Ctx.orderOf_z (h : Stage2Ctx G z k S) : orderOf z = 2 := h.central.1

theorem Stage2Ctx.z_mem (h : Stage2Ctx G z k S) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.sylow
  have hzC : z ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let g : Cen z := ⟨z, hzC⟩
  have hcomm : ∀ c : Cen z, Commute c g := by
    intro c
    apply Subtype.ext
    have := c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have : (zpowers g).Normal := ⟨fun n hn c => by
    obtain ⟨m, rfl⟩ := hn
    have h1 : Commute c (g ^ m) := (hcomm c).zpow_right m
    rw [h1.eq, mul_inv_cancel_right]
    exact mem_zpowers_iff.mpr ⟨m, rfl⟩⟩
  have hord : orderOf g = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h.orderOf_z
  have hN : IsPGroup 2 (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hle := hN.le_sylow_of_normal Q
  have hgQ : g ∈ (Q : Subgroup (Cen z)) := hle (mem_zpowers g)
  rw [← hQ]
  exact ⟨g, hgQ, rfl⟩

theorem Stage2Ctx.sylow_top (h : Stage2Ctx G z k S) : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, S', hzS', hzc⟩ := h.central
  have hS'le : (S' : Subgroup G) ≤ Cen z := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs)
  have hS'G : CFSG.ABGLocalTools.IsSylowOf 2 (S' : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S'.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S'.not_dvd_index
  have hS'C := hS'G.of_le hS'le le_top
  have h1 := h.sylow.card_eq
  have h2 := hS'C.card_eq
  have h3 := hS'G.card_eq
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [h1, ← h2, h3]

theorem Stage2Ctx.center_cyclic (h : Stage2Ctx G z k S) : IsCyclic ↥(center ↥S) := by
  have hS : IsPGroup 2 ↥S := h.sylow.isPGroup
  have hZ : IsPGroup 2 ↥(center ↥S) := hS.to_subgroup (center ↥S)
  have hbase := h.data.base
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      ↥(center ↥S) := by
    intro first second _
    have key : ∀ w : CFSG.DisconnectedInvolutionGraph.Helpers.Involution ↥(center ↥S), ((w : ↥(center ↥S)) : ↥S).1 = z := by
      intro w
      refine hbase.zcen _ ((w : ↥(center ↥S)) : ↥S).2 ?_ ?_
      · intro s hs
        have := Subgroup.mem_center_iff.mp (w : ↥(center ↥S)).2 ⟨s, hs⟩
        exact congrArg Subtype.val this
      · have h1 := w.2
        rw [← orderOf_coe (w : ↥(center ↥S)), ← orderOf_coe ((w : ↥(center ↥S)) : ↥S)] at h1
        exact h1
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

end Basic

end CFSG.GH74.GLS.Stage2.Local
