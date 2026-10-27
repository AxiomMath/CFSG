module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem comm_of_isCyclic {H : Type*} [Group H] (hc : IsCyclic H) (x y : H) : x * y = y * x := by
  obtain ⟨g, hg⟩ := hc
  obtain ⟨m, rfl⟩ := hg x
  obtain ⟨n, rfl⟩ := hg y
  exact ((Commute.refl g).zpow_zpow m n).eq

theorem quat_noncomm (m : ℕ) (hm : 2 ≤ m) :
    QuaternionGroup.a (1 : ZMod (2 * m)) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  intro h
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h
  have h2 : ((0 : ZMod (2 * m)) - 1) = 0 + 1 := QuaternionGroup.xa.inj h
  have h3 : (2 : ZMod (2 * m)) = 0 := by linear_combination (-1 : ZMod (2 * m)) * h2
  have h4 : (2 * m : ℕ) ∣ 2 := by
    have := (ZMod.natCast_eq_zero_iff 2 (2 * m)).mp (by exact_mod_cast h3)
    exact this
  have h5 := Nat.le_of_dvd (by norm_num) h4
  omega

theorem quat_noncomm_group {Y : Type} [Group Y] {n : ℕ} (hY : IVK.IsQuaternionTwoGroup Y n) :
    ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨hn, ⟨φ⟩⟩ := hY
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨φ.symm (QuaternionGroup.a 1), φ.symm (QuaternionGroup.xa 0), fun h => ?_⟩
  have h2 : QuaternionGroup.a (1 : ZMod (2 * 2 ^ (n - 2))) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
    apply φ.symm.injective
    rw [map_mul, map_mul]
    exact h
  exact quat_noncomm _ hm h2

theorem quat_of_unique_invol {G : Type} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (hp : IsPGroup 2 ↥Q) (hz : ∀ a ∈ Q, a * a = 1 → a ≠ 1 → a = z) (hnc : ¬ IsCyclic ↥Q) :
    ∃ n, IVK.IsQuaternionTwoGroup ↥Q n := by
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥Q := by
    intro first second _
    have key : ∀ w : CFSG.DisconnectedInvolutionGraph.Helpers.Involution ↥Q, ((w : ↥Q) : G) = z := by
      intro w
      have hw2 : ((w : ↥Q) : G) * ((w : ↥Q) : G) = 1 := by
        have h1 := w.2
        rw [← orderOf_coe (w : ↥Q)] at h1
        exact mul_self_eq_one_of_orderOf_eq_two h1
      have hw1 : ((w : ↥Q) : G) ≠ 1 := by
        have h1 := w.2
        rw [← orderOf_coe (w : ↥Q)] at h1
        exact ne_one_of_orderOf_eq_two h1
      exact hz _ (w : ↥Q).2 hw2 hw1
    apply Subtype.ext
    apply Subtype.ext
    rw [key first, key second]
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hp hrank
    with hc | ⟨e, he, ⟨φ⟩⟩
  · exact absurd hc hnc
  · refine ⟨e + 2, by omega, ?_⟩
    rw [show e + 2 - 2 = e by omega]
    exact ⟨φ.symm⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
