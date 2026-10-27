module

public import Certificates.Data.T84S4
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.T84P (Elt mulE oneE M0l Jl)
open Certificates.T84S4 (elt Ml mulT invT jT)

structure Sec8T84TS4Coord {Y : Type} [Group Y] (J : Subgroup Y) (rr : Y → Elt) : Prop where
  mul : ∀ x y, rr (x * y) = mulE (rr x) (rr y)
  one : rr 1 = oneE
  inj : Function.Injective rr
  mem : ∀ x, rr x ∈ M0l
  surj : ∀ z ∈ M0l, ∃ x, rr x = z
  card : Nat.card Y = 5760
  J_iff : ∀ x, x ∈ J ↔ rr x ∈ Jl

variable {Y : Type} [Group Y] {J : Subgroup Y} {rr : Y → Elt}
  (S : Certificates.T84S4.Facts) (C : Sec8T84TS4Coord J rr)

noncomputable def sec8t84ts4_el (i : ℕ) : Y :=
  if h : i < 192 then Classical.choose (C.surj (elt i) (S.mem i h)) else 1

theorem sec8t84ts4_rr_el {i : ℕ} (hi : i < 192) : rr (sec8t84ts4_el S C i) = elt i := by
  unfold sec8t84ts4_el
  rw [dif_pos hi]
  exact Classical.choose_spec (C.surj (elt i) (S.mem i hi))

theorem sec8t84ts4_el_mul {i j : ℕ} (hi : i < 192) (hj : j < 192) :
    mulT i j < 192 ∧
      sec8t84ts4_el S C (mulT i j) = sec8t84ts4_el S C i * sec8t84ts4_el S C j := by
  obtain ⟨hlt, heq⟩ := S.tab i hi j hj
  refine ⟨hlt, C.inj ?_⟩
  rw [C.mul, sec8t84ts4_rr_el S C hi, sec8t84ts4_rr_el S C hj, sec8t84ts4_rr_el S C hlt, heq]

theorem sec8t84ts4_el_inj {i j : ℕ} (hi : i < 192) (hj : j < 192)
    (h : sec8t84ts4_el S C i = sec8t84ts4_el S C j) : i = j :=
  S.inj i hi j hj (by rw [← sec8t84ts4_rr_el S C hi, ← sec8t84ts4_rr_el S C hj, h])

theorem sec8t84ts4_el_zero : sec8t84ts4_el S C 0 = 1 :=
  C.inj (by rw [sec8t84ts4_rr_el S C (by norm_num), S.one, C.one])

theorem sec8t84ts4_exists_el {y : Y} (hy : rr y ∈ Ml ()) :
    ∃ i, i < 192 ∧ sec8t84ts4_el S C i = y := by
  obtain ⟨i, hi, hiy⟩ := List.mem_map.mp (show rr y ∈ (List.range 192).map elt from hy)
  have hi' : i < 192 := List.mem_range.mp hi
  exact ⟨i, hi', C.inj (by rw [sec8t84ts4_rr_el S C hi', hiy])⟩

theorem sec8t84ts4_rr_mem_Ml {i : ℕ} (hi : i < 192) : rr (sec8t84ts4_el S C i) ∈ Ml () := by
  rw [sec8t84ts4_rr_el S C hi]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem sec8t84ts4_el_J {i : ℕ} (hi : i < 192) : sec8t84ts4_el S C i ∈ J ↔ jT i = true := by
  rw [C.J_iff, sec8t84ts4_rr_el S C hi]
  exact (S.jT_iff i hi).symm

include S C in
theorem sec8t84ts4_J_rr {x : Y} (hx : x ∈ J) : rr x ∈ Ml () :=
  S.jl_sub _ ((C.J_iff x).mp hx)

theorem sec8t84ts4_el_inv {i : ℕ} (hi : i < 192) :
    invT i < 192 ∧ (sec8t84ts4_el S C i)⁻¹ = sec8t84ts4_el S C (invT i) := by
  obtain ⟨hlt, h0⟩ := S.inv i hi
  refine ⟨hlt, inv_eq_of_mul_eq_one_right ?_⟩
  rw [← (sec8t84ts4_el_mul S C hi hlt).2, h0, sec8t84ts4_el_zero S C]

end CFSG.OddStandard.SmallF3.Omega
