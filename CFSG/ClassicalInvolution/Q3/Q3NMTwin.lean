module

public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51
public import CFSG.ClassicalInvolution.Q3.Q3NMAut

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Generic

section Twin

variable {H : Type} [Group H]

theorem toInducedAutOn_mem_innSubgroup (L : Subgroup H) (u : H)
    (hun : u ∈ Subgroup.normalizer (L : Set H)) (hu : u ∈ L) :
    ((toInducedAutOn L ⟨u, hun⟩ : ↥(inducedAutOn L)) : MulAut ↥L) ∈ innSubgroup ↥L := by
  refine ⟨⟨u, hu⟩, ?_⟩
  ext y
  rfl

theorem mul_self_eq_one_of_mem_closure_pair {G : Type} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set G), g * g = 1 := by
  set A := Subgroup.closure ({a, b} : Set G) with hA
  have h1 : ∀ c : G, c * a = a * c → c * b = b * c → ∀ g ∈ A, g * c = c * g := by
    intro c hca hcb g hg
    have : A ≤ Subgroup.centralizer ({c} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases hy with rfl | hy
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hca.symm
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcb.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hg)
  have hcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := by
    intro g hg h hh
    have hga : g * a = a * g := h1 a rfl hab g hg
    have hgb : g * b = b * g := h1 b hab.symm rfl g hg
    exact (h1 g hga hgb h hh).symm
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hb
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyz : y * z = z * y := hcomm y hy z hz
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← hyz]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [ihy, ihz, one_mul]
  | inv y hy ihy =>
    rw [← mul_inv_rev, ihy, inv_one]

end Twin

end CFSG.ClassicalInvolution.Q3.Q3NM
