module

public import CFSG.GH74.GLS.Stage2.Local.P34S5Frat
public import CFSG.GH74.GLS.Stage2.Local.Prop27W
public import CFSG.GH74.GLS.Stage2.Local.P34S5Clo
public import CFSG.GH74.GLS.Stage2.Local.P34S5SE

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open CFSG.ComponentClassification.LBalance (SchreierSections)

section Dih

variable {G : Type} [Group G] {z : G} {k : Kind}

theorem dihJ_of_prop27W {x : G} (hk : IsClassicalKind k ∨ k = Kind.m12)
    (hJ : IsClassicalKind k → Prop27WJ z x) (hm : k = Kind.m12 → Prop27WM12 z x) :
    DihJ (HBar (Jx x)) := by
  rcases hk with hcl | hmk
  · obtain ⟨hhat, -, -⟩ := hJ hcl
    rcases hhat with ⟨r, hr, -, ⟨F, iF, fF, hF, e⟩⟩ | hA
    · exact Or.inl ⟨F, iF, fF, by rw [hF]; exact hr, e⟩
    · exact Or.inr hA
  · subst hmk
    obtain ⟨q, hq, ⟨F, iF, fF, hF, e⟩, -⟩ := hm rfl
    exact Or.inl ⟨F, iF, fF, by rw [hF]; exact hq, e⟩

end Dih

section Closure

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind}

theorem closure_J0_w (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H) (hFUS : FUS H) {x : G}
    (hx : x ∈ Cen z) (hx2 : orderOf x = 2) (hk : IsClassicalKind k ∨ k = Kind.m12)
    (hJ : IsClassicalKind k → Prop27WJ z x) (hm : k = Kind.m12 → Prop27WM12 z x) :
    ∀ u ∈ Jx x, u ∈ H → orderOf u = 2 →
      centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) ≤ H := by
  intro u huJ huH hu2
  have hxH : x ∈ H := hCH hx
  have huN : u ∈ centralizer ({x} : Set G) := Jx_le_centralizer x huJ
  rcases hk with hcl | hmk
  · obtain ⟨-, hxJ, hcls⟩ := hJ hcl
    have hcomm : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 huN
    have hne : u ≠ x := fun h => hxJ (h ▸ huJ)
    have hx1 : x * x = 1 := by
      have h' := pow_orderOf_eq_one x
      rw [hx2] at h'
      simpa [pow_two] using h'
    have hu1 : u * u = 1 := by
      have h' := pow_orderOf_eq_one u
      rw [hu2] at h'
      simpa [pow_two] using h'
    have hxu2 : orderOf (x * u) = 2 := by
      refine orderOf_eq_two_of_sq ?_ ?_
      · calc x * u * (x * u) = x * (u * x) * u := by group
          _ = x * (x * u) * u := by rw [hcomm]
          _ = (x * x) * (u * u) := by group
          _ = 1 := by rw [hx1, hu1, one_mul]
      · intro h
        apply hne
        have : u = x⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]
        exact inv_eq_of_mul_eq_one_right hx1
    have hconj : IsConj z (x * u) := hcls u huJ hu2
    have hxuH : x * u ∈ H := H.mul_mem hxH huH
    have hC := centralizer_le_of_fus hFUS hCH hz2 hxuH hxu2 hconj
    intro y hy
    obtain ⟨hyx, hyu⟩ := Subgroup.mem_inf.1 hy
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff] at hyx hyu ⊢
    calc y * (x * u) = (y * x) * u := by group
      _ = (x * y) * u := by rw [hyx]
      _ = x * (y * u) := by group
      _ = x * (u * y) := by rw [hyu]
      _ = x * u * y := by group
  · subst hmk
    obtain ⟨q, -, -, hI⟩ := hm rfl
    have hC := centralizer_le_of_fus hFUS hCH hz2 huH hu2 (hI u huJ hu2)
    intro y hy
    exact hC (Subgroup.mem_inf.1 hy).2

theorem step5_core_w
    (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H) (hFUS : FUS H) {x : G}
    (hxC : x ∈ Cen z) (hx2 : orderOf x = 2) (hk : IsClassicalKind k ∨ k = Kind.m12)
    (hJ : IsClassicalKind k → Prop27WJ z x) (hm : k = Kind.m12 → Prop27WM12 z x)
    (hDih : DihJ (HBar (Jx x))) (hns : ¬ Group.IsSolvable ↥(Jx x ⊓ H)) :
    centralizer ({x} : Set G) ≤ H := by
  have hclo := closure_J0_w hz2 hCH hFUS hxC hx2 hk hJ hm
  have hJle : Jx x ⊓ H ≤ Jx x := inf_le_left
  have hSE : Jx x ≤ Jx x ⊓ H := J_le_J0 hJle hDih hns (fun u hu hu2 y hy => by
    obtain ⟨hyu, hyJ⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨hyJ, hclo u (Subgroup.mem_inf.1 hu).1 (Subgroup.mem_inf.1 hu).2 hu2
      (Subgroup.mem_inf.2 ⟨Jx_le_centralizer x hyJ, hyu⟩)⟩)
  have hJH : Jx x ≤ H := hSE.trans inf_le_right
  have hJns : ¬ Group.IsSolvable ↥(Jx x) := fun hs =>
    hns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJle)
      (Subgroup.inclusion_injective hJle))
  obtain ⟨u₀', hu₀'⟩ := exists_involution_of_not_solvable hJns
  have hu₀J : (u₀' : G) ∈ Jx x := u₀'.2
  have hu₀2 : orderOf (u₀' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu₀'
  intro n hn
  obtain ⟨j, hj, c, hc, rfl⟩ := frattini_involution (Jx_le_centralizer x) (Jx_normalized x) hu₀J hu₀2
    (fun u hu hu2 => exists_conj_of_involutions hDih hu₀J hu hu₀2 hu2) n hn
  exact H.mul_mem (hJH hj) (hclo (u₀' : G) hu₀J (hJH hu₀J) hu₀2 hc)

end Closure

end CFSG.GH74.GLS.Stage2.Local.P34
