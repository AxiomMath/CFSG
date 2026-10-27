module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs

import CFSG.GroupTheory.SimpleTrivialOnSmallF2Module
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Lift
import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

theorem eq_one_of_finrank_le_five {X U : Type*} [Group X] [Finite X] [AddCommGroup U]
    [Module (ZMod 2) U] [Module.Finite (ZMod 2) U] (π : X →* (U ≃ₗ[ZMod 2] U))
    (hU : Module.finrank (ZMod 2) U ≤ 5) (hperf : commutator X = ⊤)
    (hs : IsSimpleGroup (X ⧸ Subgroup.center X)) (h81 : 81 ∣ Nat.card (X ⧸ Subgroup.center X))
    (x : X) : π x = 1 := by
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have htop := ker_sup_ker_eq_top_of_dvd_card_of_not_dvd
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _) π (n := 3 ^ 4)
    (by norm_num [h81]) (not_three_pow_four_dvd_card_linearEquiv_of_finrank_le_five hU)
  rw [QuotientGroup.ker_mk'] at htop
  have hK := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_top_of_sup_center_eq_top
    hperf htop
  exact MonoidHom.mem_ker.mp (hK ▸ Subgroup.mem_top x)

end CFSG.GroupTheory
