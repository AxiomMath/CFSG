module

public import CFSG.ClassicalInvolution.Q3.Q3ZFrbLocal
public import CFSG.ClassicalInvolution.Q3.Q3ZFraFrame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup longInv stdPlane form
  isHyperbolicPlane_stdPlane IsHyperbolicPlane)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

section Involution

variable {G : Type} [Group G]

theorem eq_of_sq_eq_one_of_isClassicalMember3 {K : Subgroup G} {z : G}
    (hz : Q3.IsClassicalMember3 K z) (hex : classicalInvolutionOddCore K = ⊥) {y : G} (hy : y ∈ K)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) : y = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hex
  have key : ∀ a : SL(2, ZMod 3), a * a = 1 → a = 1 ∨ a = -1 := by decide +kernel
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := hz.ne_one
  have hsq : ∀ (x : G) (hx : x ∈ K), x * x = 1 → x ≠ 1 → e ⟨x, hx⟩ = -1 := by
    intro x hx hx2 hx1
    have hxx : (⟨x, hx⟩ : K) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    have hsq1 : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by rw [← map_mul, hxx, map_one]
    rcases key _ hsq1 with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))) hx1
    · exact h
  have h1 := hsq y hy hy2 hy1
  have h2 := hsq z hz.mem hz2 hz1
  exact congrArg Subtype.val (e.injective (h1.trans h2.symm))

end Involution

section NoTwins

namespace Layer3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
  {c : CCore3 Ω K z} (l : Layer3 c)

include l

theorem injective (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) : Function.Injective l.Θ := by
  refine injective_of_longInv_ne l.Θ l.ker_le fun hab => ?_
  have hmemP : ∀ k : Fin 2, longInv (GaloisField 3 1) 2 k ∈
      planeGroup (stdPlane (GaloisField 3 1) 2 k) := by
    intro k
    rw [Models.SymplecticPairs.planeGroup_stdPlane]
    exact ⟨-1, rfl⟩
  obtain ⟨hK₁, -⟩ := l.plane _ (isHyperbolicPlane_stdPlane (K := GaloisField 3 1) (n := 2) 0)
  obtain ⟨hK₂, -⟩ := l.plane _ (isHyperbolicPlane_stdPlane (K := GaloisField 3 1) (n := 2) 1)
  set K₁ := (planeGroup (stdPlane (GaloisField 3 1) 2 0)).map l.Θ with hK₁def
  set K₂ := (planeGroup (stdPlane (GaloisField 3 1) 2 1)).map l.Θ with hK₂def
  set w := l.Θ (longInv (GaloisField 3 1) 2 0) with hw
  have hw1 : w ∈ K₁ := ⟨_, hmemP 0, rfl⟩
  have hw2 : w ∈ K₂ := hab ▸ ⟨_, hmemP 1, rfl⟩
  have hww : w * w = 1 := by
    rw [hw, ← map_mul, longInv_mul_self, map_one]
  have hw1' : w ≠ 1 := map_longInv_ne_one Q3W.two_ne_zero_gf3 le_rfl l.Θ l.ker_le 0
  have hcomm : Commutes K₂ K₁ := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, commutes_planeGroup_stdPlane x hx y hy]
  obtain ⟨g, hg⟩ := hsingle K₁ hK₁.1
  have hzg : g * z * g⁻¹ ∈ K₁ := hg ▸ conj_mem_conjSub c.hz.mem
  have hL' : conjSub g⁻¹ K₂ ∈ centralizingMembers Ω {z} :=
    conjSub_inv_mem_centralizingMembers c.hΩ.conjInvariant hK₂.1 hzg hcomm
  have hL'K : conjSub g⁻¹ K₂ ≠ K := by
    intro h
    have : K₂ = K₁ := by
      calc K₂ = conjSub g (conjSub g⁻¹ K₂) := (conjSub_conjSub_inv g K₂).symm
        _ = conjSub g K := by rw [h]
        _ = K₁ := hg.symm
    exact ne_of_commutes_member c.hΩ hK₂.1 hcomm this
  obtain ⟨P, hP, hLP⟩ := c.exists_plane_of_ne hL' hL'K
  have hyK : g⁻¹ * w * g ∈ K := mem_conjSub_iff.1 (hg ▸ hw1)
  have hyL' : g⁻¹ * w * g ∈ conjSub g⁻¹ K₂ := by
    have := conj_mem_conjSub (n := g⁻¹) hw2
    rwa [inv_inv] at this
  have hyy : g⁻¹ * w * g * (g⁻¹ * w * g) = 1 := by
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hww]; group
  have hy1 : g⁻¹ * w * g ≠ 1 := by
    intro h1
    apply hw1'
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hyz := eq_of_sq_eq_one_of_isClassicalMember3 c.hz (c.hex K c.hK) hyK hyy hy1
  rw [hyz] at hyL'
  exact false_of_involution_mem_plane_member c.d (le_centralizingLayer hL') hyL'
    c.hz.orderOf_eq_two hP hLP

theorem commutes_map_planeGroup_iff (hinj : Function.Injective l.Θ)
    {P P' : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1)}
    (hP : IsHyperbolicPlane P) (hP' : IsHyperbolicPlane P') :
    Commutes ((planeGroup P).map l.Θ) ((planeGroup P').map l.Θ) ↔
      ∀ u ∈ P, ∀ v ∈ P', form u v = 0 := by
  rw [← commute_planeGroup_iff Q3W.two_ne_zero_gf3 le_rfl hP hP']
  constructor
  · intro h x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

end Layer3

end NoTwins

end CFSG.ClassicalInvolution.Q3.Q3Z
