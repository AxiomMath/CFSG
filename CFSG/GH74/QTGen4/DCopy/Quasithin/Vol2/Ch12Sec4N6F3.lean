module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6F3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4N6F1

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V]

namespace Cyc

variable {c : Ctx T L V E z v} {g : G} (hg : c.Cyc g)
include hg

theorem comm_cube_F4 (h12210 : Stmt12_2_10_F4) {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    {P : Subgroup G} (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P)
    {s s' : G} (hs : s ∈ P) (hs' : s' ∈ P) :
    s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∧
      s * s * s ∈ Subgroup.centralizer (B6.conjSub h V : Set G) := by
  have hP'K := hg.conjSub_inv_le_CE hh hPK
  have hP'3 : IsPGroup 3 (B6.conjSub h⁻¹ P) := hP3.map _
  obtain ⟨h1, h2, -⟩ := c.three_sub_facts_F4 h12210 hP'K hP'3
  have hmem : ∀ x ∈ P, h⁻¹ * x * h ∈ B6.conjSub h⁻¹ P := fun x hx => by
    rw [B6.mem_conjSub, inv_inv]; simpa [mul_assoc] using hx
  rw [centralizer_conjSub, B6.mem_conjSub, B6.mem_conjSub]
  refine ⟨?_, ?_⟩
  · have := h1 _ (hmem s hs) _ (hmem s' hs')
    convert this using 1
    group
  · have := h2 _ (hmem s hs)
    convert this using 1
    group

theorem idx3_F4 (h12210 : Stmt12_2_10_F4) {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    {P : Subgroup G} (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P)
    {s y : G} (hs : s ∈ P) (hy : y ∈ P)
    (hsV : s ∉ Subgroup.centralizer (B6.conjSub h V : Set G)) :
    y ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∨
      s⁻¹ * y ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∨
      (s * s)⁻¹ * y ∈ Subgroup.centralizer (B6.conjSub h V : Set G) := by
  have hP'K := hg.conjSub_inv_le_CE hh hPK
  have hP'3 : IsPGroup 3 (B6.conjSub h⁻¹ P) := hP3.map _
  obtain ⟨-, -, h3⟩ := c.three_sub_facts_F4 h12210 hP'K hP'3
  have hmem : ∀ x ∈ P, h⁻¹ * x * h ∈ B6.conjSub h⁻¹ P := fun x hx => by
    rw [B6.mem_conjSub, inv_inv]; simpa [mul_assoc] using hx
  rw [centralizer_conjSub] at hsV ⊢
  rw [B6.mem_conjSub] at hsV
  rw [B6.mem_conjSub, B6.mem_conjSub, B6.mem_conjSub]
  rcases h3 _ (hmem s hs) hsV _ (hmem y hy) with h4 | h4 | h4
  · exact Or.inl h4
  · refine Or.inr (Or.inl ?_)
    convert h4 using 1
    group
  · refine Or.inr (Or.inr ?_)
    convert h4 using 1
    group

theorem isElemAbelian_F4 (h12210 : Stmt12_2_10_F4) (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    {P : Subgroup G} (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hP3 : IsPGroup 3 P) :
    IsElemAbelian 3 P := by
  have hgE := hg.NR1_le_NE hg.mem
  have hggE : g * g ∈ Subgroup.normalizer (E : Set G) := Subgroup.mul_mem _ hgE hgE
  have hodd : ∀ x ∈ P, Odd (orderOf x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    have h1 : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h1)
  have key : ∀ s ∈ P, ∀ s' ∈ P, s * s' * s⁻¹ * s'⁻¹ = 1 ∧ s * s * s = 1 := by
    intro s hs s' hs'
    obtain ⟨h0, h0'⟩ := hg.comm_cube_F4 h12210 (Subgroup.one_mem _) hPK hP3 hs hs'
    obtain ⟨h1, h1'⟩ := hg.comm_cube_F4 h12210 hgE hPK hP3 hs hs'
    obtain ⟨h2, h2'⟩ := hg.comm_cube_F4 h12210 hggE hPK hP3 hs hs'
    rw [B6.conjSub_one] at h0 h0'
    have hm : s * s' * s⁻¹ * s'⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hs hs') (P.inv_mem hs)) (P.inv_mem hs')
    have hm' : s * s * s ∈ P := P.mul_mem (P.mul_mem hs hs) hs
    exact ⟨hg.eq_one_of_odd hcomm h0 h1 h2 (hodd _ hm),
      hg.eq_one_of_odd hcomm h0' h1' h2' (hodd _ hm')⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := (key a a.2 b b.2).1
    show (a : G) * b = b * a
    calc (a : G) * b = ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by
          group
      _ = b * a := by rw [h1, one_mul]
  · rw [pow_three']
    exact (key x hx x hx).2

end Cyc

end Ctx

end N1246

end CFSG.Quasithin.H13
