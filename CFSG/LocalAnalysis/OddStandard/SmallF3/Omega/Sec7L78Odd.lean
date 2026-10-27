module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Side
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l78_odd_cent [Finite G] (hP : Asc82Tab6P) {L P B A : Subgroup G} {c x : G}
    (hs : Sec7L78Side L P B A c) (hxA : x ∈ normalizer (A : Set G))
    (hxL : x ∈ normalizer (L : Set G)) (hxc : x * c = c * x) (hodd : Odd (orderOf x)) {u : G}
    (hu : u ∈ A) (huN : ∀ n ∈ L ⊓ normalizer (B : Set G), u * n = n * u) :
    x * u = u * x := by
  classical
  have hL : IsOm6P L := hs.om
  obtain ⟨l, hlL, y, hyC, hxly⟩ :=
    innerOn_decompose (L := L) (s := x) (hP.out_two G L hL x hxL hodd)
  have hmemB : ∀ z : G, z ∈ B ↔ z ∈ A ⊓ L := fun z => by rw [hs.inf_eq]
  have hymy : ∀ m ∈ L, y * m * y⁻¹ = m := by
    intro m hm
    have h := Subgroup.mem_centralizer_iff.mp hyC m hm
    rw [← h]; group
  have hconj : ∀ m ∈ L, l * m * l⁻¹ = x * m * x⁻¹ := by
    intro m hm
    have h : x * m * x⁻¹ = l * m * l⁻¹ := by
      rw [hxly]
      calc (l * y) * m * (l * y)⁻¹ = l * (y * m * y⁻¹) * l⁻¹ := by group
        _ = l * m * l⁻¹ := by rw [hymy m hm]
    exact h.symm
  have hlB : l ∈ normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have hb' := (hmemB b).mp hb
      have hxB : x * b * x⁻¹ ∈ B :=
        (hmemB _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hxA b).mp hb'.1,
          (Subgroup.mem_normalizer_iff.mp hxL b).mp hb'.2⟩
      rw [hconj b hb'.2]
      exact hxB
    · intro hb
      have hbL : b ∈ L := by
        have hbL' : l * b * l⁻¹ ∈ L := ((hmemB _).mp hb).2
        have hb_eq : b = l⁻¹ * (l * b * l⁻¹) * l := by group
        rw [hb_eq]
        exact L.mul_mem (L.mul_mem (L.inv_mem hlL) hbL') hlL
      have hxB : x * b * x⁻¹ ∈ B := by rwa [← hconj b hbL]
      exact (hmemB b).mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hxA b).mpr ((hmemB _).mp hxB).1,
         (Subgroup.mem_normalizer_iff.mp hxL b).mpr ((hmemB _).mp hxB).2⟩
  have hul : u * l = l * u := huN l ⟨hlL, hlB⟩
  have hcomm_ul : Commute u l := hul
  set w : G := u⁻¹ * (x * u * x⁻¹) with hw
  have hwA : w ∈ A := by
    rw [hw]
    exact A.mul_mem (A.inv_mem hu) ((Subgroup.mem_normalizer_iff.mp hxA u).mp hu)
  have hf1 : ∀ m ∈ L, x * m * x⁻¹ = l * m * l⁻¹ := fun m hm => (hconj m hm).symm
  have hxinv : ∀ m ∈ L, x⁻¹ * m * x = l⁻¹ * m * l := by
    intro m hm
    have hmL : x⁻¹ * m * x ∈ L := (Subgroup.mem_normalizer_iff''.mp hxL m).mp hm
    have h2 : m = l * (x⁻¹ * m * x) * l⁻¹ := by
      have h := hconj (x⁻¹ * m * x) hmL
      rw [h]; group
    have h3 : l⁻¹ * m * l = x⁻¹ * m * x := by
      conv_lhs => rw [h2]
      group
    exact h3.symm
  have hstep : ∀ n : G, u * (l⁻¹ * n * l) * u⁻¹ = l⁻¹ * (u * n * u⁻¹) * l := by
    intro n
    have h1 : u * l⁻¹ = l⁻¹ * u := hcomm_ul.inv_right.eq
    have h2 : l * u⁻¹ = u⁻¹ * l := hcomm_ul.symm.inv_right.eq
    calc u * (l⁻¹ * n * l) * u⁻¹ = (u * l⁻¹) * n * (l * u⁻¹) := by group
      _ = (l⁻¹ * u) * n * (u⁻¹ * l) := by rw [h1, h2]
      _ = l⁻¹ * (u * n * u⁻¹) * l := by group
  have hwconj : ∀ n ∈ L, w * n * w⁻¹ = n := by
    intro n hn
    have hnL : u * n * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hs.A_N hu) n).mp hn
    have hf2 : x * (l⁻¹ * (u * n * u⁻¹) * l) * x⁻¹ = u * n * u⁻¹ := by
      have := hconj (l⁻¹ * (u * n * u⁻¹) * l)
        (L.mul_mem (L.mul_mem (L.inv_mem hlL) hnL) hlL)
      rw [← this]; group
    calc w * n * w⁻¹
        = u⁻¹ * (x * (u * (x⁻¹ * n * x) * u⁻¹) * x⁻¹) * u := by rw [hw]; group
      _ = u⁻¹ * (x * (u * (l⁻¹ * n * l) * u⁻¹) * x⁻¹) * u := by rw [hxinv n hn]
      _ = u⁻¹ * (x * (l⁻¹ * (u * n * u⁻¹) * l) * x⁻¹) * u := by rw [hstep n]
      _ = u⁻¹ * (u * n * u⁻¹) * u := by rw [hf2]
      _ = n := by group
  have hwC : w ∈ centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
    have h : w * n * w⁻¹ = n := hwconj n hn
    exact ((mul_inv_eq_iff_eq_mul).mp h).symm
  rcases hs.A_cent w hwA hwC with hw1 | hwc
  · have h : u⁻¹ * (x * u * x⁻¹) = 1 := by rw [← hw]; exact hw1
    have hxux : x * u * x⁻¹ = u := by
      calc x * u * x⁻¹ = u * (u⁻¹ * (x * u * x⁻¹)) := by group
        _ = u * 1 := by rw [h]
        _ = u := mul_one u
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [hxux]
  · have h : u⁻¹ * (x * u * x⁻¹) = c := by rw [← hw]; exact hwc
    have hux : x * u * x⁻¹ = u * c := by
      calc x * u * x⁻¹ = u * (u⁻¹ * (x * u * x⁻¹)) := by group
        _ = u * c := by rw [h]
    have hcsq : c * c = 1 := hs.A_sq c hs.c_mem
    have hxcx : x * c * x⁻¹ = c := by rw [hxc]; group
    have hx2 : x ^ 2 * u * (x ^ 2)⁻¹ = u := by
      calc x ^ 2 * u * (x ^ 2)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * (u * c) * x⁻¹ := by rw [hux]
        _ = (x * u * x⁻¹) * (x * c * x⁻¹) := by group
        _ = (u * c) * c := by rw [hux, hxcx]
        _ = u * (c * c) := by group
        _ = u := by rw [hcsq, mul_one]
    have hx2comm : Commute (x ^ 2) u := (mul_inv_eq_iff_eq_mul).mp hx2
    obtain ⟨m, hm⟩ := hodd
    have hxpow : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one x
    have hxeq : x = (x ^ 2) ^ (m + 1) := by
      rw [← pow_mul]
      have h2m : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h2m, pow_succ, hxpow, one_mul]
    have hcommx : Commute x u := by
      rw [hxeq]
      exact hx2comm.pow_left (m + 1)
    have hxueq : x * u = u * x := hcommx.eq
    have huc : u * c = u := by rw [← hux, hxueq]; group
    have hc1 : c = 1 := mul_left_cancel (show u * c = u * 1 by rw [mul_one]; exact huc)
    exfalso
    have h1 : orderOf c = 1 := by rw [hc1, orderOf_one]
    rw [hs.c_ord] at h1
    omega

end CFSG.OddStandard.SmallF3.Omega