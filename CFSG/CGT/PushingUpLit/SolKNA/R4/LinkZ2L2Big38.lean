module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big37

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ}

theorem z2BigT1_of_xplus (hX : Z2BigXPlusA r n) : Z2BigT1 r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 hall hno b hbP hbA hab g he
  have hb1 : b ≠ 1 := fun h => hbA (by rw [h]; exact Subgroup.one_mem _)
  have hb2 : b * b ≠ 1 := fun h => hno ⟨b, hbP, hbA, h⟩
  obtain ⟨L, hL⟩ := exists_orderOf_eq_two_pow P hbP
  have hL2 : 2 ≤ L := two_le_of_orderOf_eq_two_pow hL hb1 hb2
  have hbL : b ^ 2 ^ (L - 1) = t * u :=
    pow_half_eq_of_mem_zpowers (by omega) hL (Subgroup.mem_zpowers b) hab hs.tu_mul_self
      hs.tu_ne_one
  have heL : (g⁻¹ * b * g) ^ 2 ^ L = 1 := by
    rw [conj_pow', ← hL, pow_orderOf_eq_one]
    group
  have he0 : (g⁻¹ * b * g) ^ 2 ^ (L - 1) = g⁻¹ * (t * u) * g := by
    rw [conj_pow', hbL]
  have hx := hs.eq_tu_of_pi4 hr hX h1 hall hno he hL2 heL (g := g) (by rw [he0]; group)
  rw [he0] at hx
  exact hbA ((hs.mem_edgeCent_conj_iff_of_fix h1 hbP hx he.1.1).mpr he)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
