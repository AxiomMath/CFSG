module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open

variable {G : Type*} [Group G]

theorem map_eq_one_of_perfect {C P : Subgroup G} (hPC : P ≤ C) (hP : ⁅P, P⁆ = P)
    {Q : Type*} [Group Q] [Group.IsSolvable Q] (φ : ↥C →* Q) (x : G) (hx : x ∈ P) :
    φ ⟨x, hPC hx⟩ = 1 := by
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  let ψ : ↥P →* Q := φ.comp (Subgroup.inclusion hPC)
  have : Group.IsPerfect ↥ψ.range := Group.IsPerfect.ofSurjective ψ.rangeRestrict_surjective
  have hss : Subsingleton ↥ψ.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) inferInstance
  have h1 : (⟨ψ ⟨x, hx⟩, ⟨_, rfl⟩⟩ : ↥ψ.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem perfect_le_of_solvable_quotient {C N P : Subgroup G} (hNC : N ≤ C)
    [(N.subgroupOf C).Normal] (hsol : Group.IsSolvable (↥C ⧸ N.subgroupOf C)) (hPC : P ≤ C)
    (hP : ⁅P, P⁆ = P) : P ≤ N := by
  intro x hx
  have h := map_eq_one_of_perfect hPC hP (QuotientGroup.mk' (N.subgroupOf C)) x hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  exact h

theorem perfect_le_glaLayer_of_series {C N M : Subgroup G} (hNC : N ≤ C)
    [(N.subgroupOf C).Normal] (hCN : Group.IsSolvable (↥C ⧸ N.subgroupOf C)) (hMN : M ≤ N)
    [(M.subgroupOf N).Normal] (hNM : Group.IsSolvable (↥N ⧸ M.subgroupOf N))
    (hM : M ≤ GLALayer C) :
    ∀ P : Subgroup G, P ≤ C → ⁅P, P⁆ = P → P ≤ GLALayer C := fun P hPC hP =>
  (perfect_le_of_solvable_quotient hMN hNM (perfect_le_of_solvable_quotient hNC hCN hPC hP)
    hP).trans hM

theorem perfectInLayer_of_series {S : Type*} [Group S] {β : MulAut S} {N M : Subgroup S}
    (hNC : N ≤ fixSubgroup β) [(N.subgroupOf (fixSubgroup β)).Normal]
    (hCN : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β))) (hMN : M ≤ N)
    [(M.subgroupOf N).Normal] (hNM : Group.IsSolvable (↥N ⧸ M.subgroupOf N))
    (hM : M ≤ GLALayer (fixSubgroup β)) : PerfectInLayer β :=
  perfect_le_glaLayer_of_series hNC hCN hMN hNM hM

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
