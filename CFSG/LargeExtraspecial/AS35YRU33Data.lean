module

public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.LargeExtraspecial.AS35YR

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

@[expose] def u33d0 : Equiv.Perm (Fin 28) :=
  Equiv.swap 4 7 * Equiv.swap 5 8 * Equiv.swap 6 9 * Equiv.swap 10 19 * Equiv.swap 11 20 *
  Equiv.swap 12 21 * Equiv.swap 13 25 * Equiv.swap 14 26 * Equiv.swap 15 27 * Equiv.swap 16 22 *
  Equiv.swap 17 23 * Equiv.swap 18 24

@[expose] def u33d1 : Equiv.Perm (Fin 28) :=
  Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 13 * Equiv.swap 5 8 * Equiv.swap 6 24 *
  Equiv.swap 7 25 * Equiv.swap 9 18 * Equiv.swap 10 16 * Equiv.swap 11 20 * Equiv.swap 12 15 *
  Equiv.swap 19 22 * Equiv.swap 21 27

@[expose] def u33d2 : Equiv.Perm (Fin 28) :=
  Equiv.swap 0 9 * Equiv.swap 1 21 * Equiv.swap 2 12 * Equiv.swap 3 6 * Equiv.swap 4 14 *
  Equiv.swap 5 22 * Equiv.swap 7 8 * Equiv.swap 11 17 * Equiv.swap 15 18 * Equiv.swap 16 26 *
  Equiv.swap 19 25 * Equiv.swap 24 27

@[expose] def u33d3 : Equiv.Perm (Fin 28) :=
  Equiv.swap 1 19 * Equiv.swap 2 20 * Equiv.swap 3 21 * Equiv.swap 4 26 * Equiv.swap 5 27 *
  Equiv.swap 6 25 * Equiv.swap 7 24 * Equiv.swap 8 22 * Equiv.swap 9 23 * Equiv.swap 13 17 *
  Equiv.swap 14 18 * Equiv.swap 15 16

@[expose] def u33InvConjCheck : Bool :=
  (elemsT QP).all fun g =>
    !(g * g == 1) || g == 1 || (elemsT QP).any fun c => c * g * c⁻¹ == u33d0

set_option maxRecDepth 10000 in
theorem u33d0_eq : u33d0 = [pb, pa, pb, pa, pb, pa, pb, pb, pa, pa, pb, pa, pa, pb, pb, pa,
    pb].prod := by decide

set_option maxRecDepth 10000 in
theorem u33d1_eq : u33d1 = [pb, pa, pa, pb, pb, pa, pb, pa, pb, pa, pb, pb, pa, pb, pb, pa,
    pa].prod := by decide

set_option maxRecDepth 10000 in
theorem u33d2_eq : u33d2 = [pb, pb, pa, pa, pb, pa, pb, pa, pb, pb, pa, pb, pa, pb, pa,
    pa].prod := by decide

set_option maxRecDepth 10000 in
theorem u33d3_eq : u33d3 = [pa, pa, pb, pb, pa, pb, pb, pa, pb, pa, pb, pb, pa, pb, pb, pa, pb,
    pa, pb].prod := by decide

set_option maxRecDepth 10000 in
theorem pa_eq_word : pa = [u33d3, u33d1, u33d2, u33d0, u33d1, u33d3, u33d2, u33d0, u33d1,
    u33d2].prod := by decide

set_option maxRecDepth 10000 in
theorem pb_eq_word : pb = [u33d0, u33d2, u33d1, u33d3, u33d0, u33d2, u33d1, u33d3].prod := by
  decide

set_option maxRecDepth 10000 in
theorem u33d0_mul_u33d1 : u33d0 * u33d1 = u33d1 * u33d0 := by decide

theorem u33d0_mul_self : u33d0 * u33d0 = 1 := by decide

theorem u33d1_mul_self : u33d1 * u33d1 = 1 := by decide

theorem u33d2_mul_self : u33d2 * u33d2 = 1 := by decide

theorem u33d3_mul_self : u33d3 * u33d3 = 1 := by decide

set_option maxRecDepth 10000 in
theorem u33d01_mul_self : u33d0 * u33d1 * (u33d0 * u33d1) = 1 := by decide

theorem u33d0_ne_one : u33d0 ≠ 1 := by decide

theorem u33d1_ne_one : u33d1 ≠ 1 := by decide

theorem u33d2_ne_one : u33d2 ≠ 1 := by decide

theorem u33d3_ne_one : u33d3 ≠ 1 := by decide

set_option maxRecDepth 10000 in
theorem u33d01_ne_one : u33d0 * u33d1 ≠ 1 := by decide

end CFSG.LargeExtraspecial.AS35YR
