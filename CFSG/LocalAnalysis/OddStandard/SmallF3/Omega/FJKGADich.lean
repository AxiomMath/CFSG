module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGABlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_exists_quaternion_pair {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsSL23Mod K) {y : G} (hyK : y ∈ K) (hy : orderOf y = 2) :
    ∃ q r : G, q ∈ K ∧ r ∈ K ∧ q * q = y ∧ r * r = y ∧ r * q = q⁻¹ * r := by
  obtain ⟨f, -, hf2, hfK⟩ := exists_quaternion_of_isSL23Mod hK hyK hy
  have ha1 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide +kernel
  have hx0 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide +kernel
  have hconj : (QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide +kernel
  refine ⟨f (QuaternionGroup.a 1), f (QuaternionGroup.xa 0),
    hfK (MonoidHom.mem_range.2 ⟨_, rfl⟩), hfK (MonoidHom.mem_range.2 ⟨_, rfl⟩), ?_, ?_, ?_⟩
  · rw [← map_mul, ha1, hf2]
  · rw [← map_mul, hx0, hf2]
  · rw [← map_inv, ← map_mul, ← map_mul, hconj]

theorem fj_pocket_dichotomy (hQ : Q.Nondegenerate) (hn : Module.finrank (ZMod 3) V ≤ 8)
    {s : OGroup Q} (hs : s * s = 1) {K : Subgroup (omegaGroup hQ)} (hK : K ≤ cOmega hQ s)
    (hKsl : IsSL23Mod K) {z : omegaGroup hQ} (hzK : z ∈ K) (hz : orderOf z = 2)
    (hzπ : (z : OGroup Q) ≠ piOrth Q) (hzs : (z : OGroup Q) ≠ s)
    (hzsπ : s ≠ piOrth Q * (z : OGroup Q)) :
    ∃ (a : OGroup (Q.restrict (fixSp s))) (c : OGroup (Q.restrict (commSp s))),
      blockHom hs (a, c) = (z : OGroup Q) ∧
        ((c = 1 ∧ 5 ≤ Module.finrank (ZMod 3) (fixSp s)) ∨
          (a = 1 ∧ 5 ≤ Module.finrank (ZMod 3) (commSp s))) := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  obtain ⟨q, r, hqK, hrK, hqq, hrr, hrq⟩ := fj_exists_quaternion_pair hKsl hzK hz
  have hzz : z * z = 1 := by
    rw [← pow_two]
    exact hz ▸ pow_orderOf_eq_one z
  have hqq' : (q : OGroup Q) * q = (z : OGroup Q) := congrArg Subtype.val hqq
  have hrr' : (r : OGroup Q) * r = (z : OGroup Q) := congrArg Subtype.val hrr
  have hzz' : (z : OGroup Q) * z = 1 := congrArg Subtype.val hzz
  have hrq' : (r : OGroup Q) * q = (q : OGroup Q)⁻¹ * r := congrArg Subtype.val hrq
  have hqc : (q : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := hK hqK
  have hrc : (r : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := hK hrK
  obtain ⟨a, c, hac, haa, hcc, ha4, hc4⟩ := fj_block_quaternion hQ hs hqc hrc
    (hqq'.trans hrr'.symm) (by rw [hqq']; exact hzz') hrq'
  rw [hqq'] at hac
  have hz1 : (z : OGroup Q) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact absurd hz (by decide)
  exact ⟨a, c, hac, fj_block_cases hn hs hac haa hcc ha4 hc4 hz1 hzπ hzs hzsπ⟩

end CFSG.OddStandard.SmallF3.Omega
