module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GorensteinWalter

universe u

theorem map_centralizer_singleton_conj
    {G : Type u} [Group G] (g x : G) :
    Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  let e : G ≃* G := MulAut.conj g
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hyz⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    have hzx : z * x = x * z :=
      (Subgroup.mem_centralizer_iff.mp hz x (by simp)).symm
    have hmap' : e z * e x = e x * e z := by
      simpa [map_mul] using congrArg e.toMonoidHom hzx
    change e z = y at hyz
    rw [hyz] at hmap'
    simpa [e, MulAut.conj_apply] using hmap'.symm
  · intro y hy
    let z : G := e.symm y
    have he_x : e x = g * x * g⁻¹ := by simp [e]
    have hzC : z ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      have heq : y * e x = e x * y :=
        (Subgroup.mem_centralizer_iff.mp hy (e x) (by simpa using he_x)).symm
      have hmap' : e.symm y * e.symm (e x) = e.symm (e x) * e.symm y := by
        simpa [map_mul] using congrArg e.symm.toMonoidHom heq
      simp [e, he_x] at hmap'
      group at hmap'
      simpa [z, e, he_x, mul_assoc] using hmap'.symm
    refine Subgroup.mem_map.mpr ⟨z, hzC, ?_⟩
    change e (e.symm y) = y
    exact e.apply_symm_apply y

end CFSG.GorensteinWalter
