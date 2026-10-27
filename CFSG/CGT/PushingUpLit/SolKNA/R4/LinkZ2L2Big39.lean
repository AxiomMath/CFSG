module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big36
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

theorem z2BigT2_of_xplus_split (hX : Z2BigXPlusA r n) (hSplit : Z2BigSplit r n) :
    Z2BigT2 r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 hall hno b hbP hbA hab g k hg
  by_contra hyA
  have hbb : b * b ∈ edgeCent (P : Subgroup Y) t u := hs.mul_self_mem_edgeCent hbP
  have hcA : b ^ (2 * k) ∈ edgeCent (P : Subgroup Y) t u := by
    rw [pow_mul, sq]
    exact Subgroup.pow_mem _ hbb k
  have hczp : b ^ (2 * k) ∈ Subgroup.zpowers b := Subgroup.pow_mem _ (Subgroup.mem_zpowers b) _
  generalize b ^ (2 * k) = c at hg hyA hcA hczp
  have hcP : c ∈ (P : Subgroup Y) := hcA.1.1
  obtain ⟨y, hy⟩ : ∃ y : Y, y = g⁻¹ * c * g := ⟨_, rfl⟩
  have hg' : g⁻¹ * c * g ∈ (P : Subgroup Y) := hg
  rw [← hy] at hg hyA
  have hypow : ∀ m : ℕ, y ^ m = g⁻¹ * c ^ m * g := fun m => by rw [hy, conj_pow']
  have hsqpow : ∀ m : ℕ, (y * y) ^ m = y ^ (2 * m) := fun m => by rw [pow_mul, sq]
  have hy1 : y ≠ 1 := fun h => hyA (by rw [h]; exact Subgroup.one_mem _)
  have hy2 : y * y ≠ 1 := fun h => hno ⟨y, hg, hyA, h⟩
  have hc1 : c ≠ 1 := fun h => hy1 (by rw [hy, h]; group)
  have hc2 : c * c ≠ 1 := fun h => hy2 (by
    rw [hy, show g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g by group, h]
    group)
  obtain ⟨L, hL⟩ := exists_orderOf_eq_two_pow P hcP
  have hL2 : 2 ≤ L := two_le_of_orderOf_eq_two_pow hL hc1 hc2
  have hcL : c ^ 2 ^ (L - 1) = t * u :=
    pow_half_eq_of_mem_zpowers (by omega) hL hczp hab hs.tu_mul_self hs.tu_ne_one
  have hyL : y ^ 2 ^ L = 1 := by
    rw [hypow, ← hL, pow_orderOf_eq_one]
    group
  have hy0 : y ^ 2 ^ (L - 1) = g⁻¹ * (t * u) * g := by
    rw [hypow, hcL]
  have hx : y * y ∈ edgeCent (P : Subgroup Y) t u := hs.mul_self_mem_edgeCent hg
  have hfix : g⁻¹ * (t * u) * g = t * u := by
    rcases Nat.lt_or_ge L 3 with hL3 | hL3
    ·
      obtain rfl : L = 2 := by omega
      have hyy : y * y = g⁻¹ * (t * u) * g := by
        rw [← sq]
        exact hy0
      have hx2 : (y * y) * (y * y) = 1 := by
        rw [hyy, show g⁻¹ * (t * u) * g * (g⁻¹ * (t * u) * g) = g⁻¹ * (t * u * (t * u)) * g by group,
          hs.tu_mul_self]
        group
      have hsq := hs.sq_outer_of_not_invOutsideA hSplit hr hall hno hg hyA
      have h2 := hs.eq_tu_of_tri hr hX h1 hall hno hx hx2 (Or.inr (Or.inr hsq.1))
        (Or.inr (Or.inr hsq.2)) (g := g) (by rw [hyy]; group)
      rw [← hyy]
      exact h2
    ·
      obtain ⟨M, rfl⟩ : ∃ M, L = M + 3 := ⟨L - 3, by omega⟩
      have e1 : M + 3 - 1 = M + 2 := by omega
      have e2 : M + 2 - 1 = M + 1 := by omega
      rw [e1] at hy0
      have h3 : y ^ 2 ^ (M + 1 + 1) = g⁻¹ * (t * u) * g := hy0
      have hxL : (y * y) ^ 2 ^ (M + 2) = 1 := by
        rw [hsqpow, ← pow_succ']
        exact hyL
      have hg2 : g * (y * y) ^ 2 ^ (M + 2 - 1) * g⁻¹ = t * u := by
        rw [e2, hsqpow, ← pow_succ', h3]
        group
      have h2 := hs.eq_tu_of_pi4 hr hX h1 hall hno hx (L := M + 2) (by omega) hxL (g := g) hg2
      rw [e2, hsqpow, ← pow_succ', h3] at h2
      exact h2
  have h3 := (hs.mem_edgeCent_conj_iff_of_fix h1 hcP hfix hg').mp hcA
  exact hyA (by rw [hy]; exact h3)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
