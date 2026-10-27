module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.I142N
open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

theorem isComponentOf_iff_of_commutator_le {X Y : Subgroup G} (hYX : Y ≤ X)
    (hn : (Y.subgroupOf X).Normal) (hc : ⁅X, X⁆ ≤ Y) {K : Subgroup G} :
    IsComponentOf K Y ↔ IsComponentOf K X := by
  constructor
  · intro hK
    exact isComponentOf_trans hK (IsSubnormal.step hYX hn (IsSubnormal.refl X))
  · intro hK
    have hperf : ⁅K, K⁆ = K := comm_self_eq_of_commutator_top hK.2.2.1
    have hKY : K ≤ Y :=
      calc K = ⁅K, K⁆ := hperf.symm
        _ ≤ ⁅X, X⁆ := Subgroup.commutator_mono hK.1 hK.1
        _ ≤ Y := hc
    exact isComponentOf_of_le hK hKY hYX

theorem glaLayer_eq_of_commutator_le {X Y : Subgroup G} (hYX : Y ≤ X)
    (hn : (Y.subgroupOf X).Normal) (hc : ⁅X, X⁆ ≤ Y) : GLALayer Y = GLALayer X := by
  rw [GLALayer_eq_sSup, GLALayer_eq_sSup]
  congr 1
  ext K
  exact isComponentOf_iff_of_commutator_le hYX hn hc

theorem isComponentOf_glaLayer_iff_of_commutator_le {X Y : Subgroup G} (hYX : Y ≤ X)
    (hn : (Y.subgroupOf X).Normal) (hc : ⁅X, X⁆ ≤ Y) :
    IsComponentOf (GLALayer Y) Y ↔ IsComponentOf (GLALayer X) X := by
  rw [glaLayer_eq_of_commutator_le hYX hn hc]
  exact isComponentOf_iff_of_commutator_le hYX hn hc

theorem glaLayer_map_eq (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G)
    (X : Subgroup G) : GLALayer (X.map f) = (GLALayer X).map f := by
  refine le_antisymm ?_ (GLALayer_map_le f hf X)
  refine GLALayer_le_of fun Kb hKb => ?_
  obtain ⟨K, hKc, rfl⟩ := exists_component_lift f hf hKb
  exact Subgroup.map_mono (le_GLALayer hKc)

theorem le_of_map_le_of_perfect (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G)
    {P K : Subgroup G} (hP : ⁅P, P⁆ = P) (h : P.map f ≤ K.map f) : P ≤ K := by
  have hcomm : ⁅P, P⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.1 (h (Subgroup.mem_map_of_mem f hx))
    obtain ⟨l', hl', hl'y⟩ := Subgroup.mem_map.1 (h (Subgroup.mem_map_of_mem f hy))
    have hc : l⁻¹ * x ∈ Subgroup.center G := hf _ (by rw [map_mul, map_inv, hlx]; simp)
    have hc' : l'⁻¹ * y ∈ Subgroup.center G := hf _ (by rw [map_mul, map_inv, hl'y]; simp)
    have e : ⁅x, y⁆ = ⁅l * (l⁻¹ * x), l' * (l'⁻¹ * y)⁆ := by simp only [mul_inv_cancel_left]
    rw [e, comm_mul_central_left hc, comm_mul_central_right hc']
    exact commutatorElement_mem_of hl hl'
  rwa [hP] at hcomm

theorem isComponentOf_glaLayer_map_iff (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G)
    (X : Subgroup G) :
    IsComponentOf (GLALayer (X.map f)) (X.map f) ↔ IsComponentOf (GLALayer X) X := by
  constructor
  · intro hL
    obtain ⟨K, hK, hKmap⟩ := exists_component_lift f hf hL
    have hKL : GLALayer X = K := by
      refine le_antisymm ?_ (le_GLALayer hK)
      refine GLALayer_le_of fun K' hK' => ?_
      refine le_of_map_le_of_perfect f hf (comm_self_eq_of_commutator_top hK'.2.2.1) ?_
      rw [hKmap]
      exact le_GLALayer (isComponentOf_map f hf hK')
    rw [hKL]
    exact hK
  · intro hL
    rw [glaLayer_map_eq f hf X]
    exact isComponentOf_map f hf hL

theorem isSolvable_of_map_le (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G)
    {X : Subgroup G} {Y : Subgroup H} [Group.IsSolvable ↥Y] (h : X.map f ≤ Y) :
    Group.IsSolvable ↥X := by
  let g : ↥X →* ↥Y := (f.comp X.subtype).codRestrict Y fun x => h (Subgroup.mem_map_of_mem f x.2)
  haveI : Group.IsSolvable ↥g.ker := by
    refine isSolvable_of_comm fun a b => ?_
    have ha : f (a : G) = 1 := congrArg Subtype.val a.2
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (hf _ ha) (b : G)).symm
  exact solvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
