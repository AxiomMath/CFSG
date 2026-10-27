module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G]

theorem mem_centralizer_of_mem_altFix [Finite G] {U V M A : Subgroup G} {d n : ℕ}
    {π : ↥U →* Multiplicative (altHeart d)} (hπ : Function.Surjective π)
    {θ : ↥M →* Perm (Fin d)} (hequiv : SectionEquiv U M π θ) (hUV : U ≤ V)
    (hV : (Subgroup.centralizer (A : Set G)).relIndex V ≤ n)
    (hlow : n ≤ (altFix d ((A.subgroupOf M).map θ)).index) {h : altHeart d}
    (hh : h ∈ altFix d ((A.subgroupOf M).map θ)) :
    ∀ u : ↥U, π u = Multiplicative.ofAdd h → (u : G) ∈ Subgroup.centralizer (A : Set G) := by
  classical
  set E := (A.subgroupOf M).map θ with hE
  let K : Subgroup (Multiplicative (altHeart d)) := AddSubgroup.toSubgroup (altFix d E)
  let C : Subgroup ↥U := K.comap π
  have hidx : C.index = (altFix d E).index := by
    rw [Subgroup.index_comap_of_surjective K hπ, AddSubgroup.index_toSubgroup]
  have hle : (Subgroup.centralizer (A : Set G)).subgroupOf U ≤ C := by
    intro u hu
    have hu' : u ∈ (Subgroup.centralizer (A : Set G)).subgroupOf U := hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hu'
    show π u ∈ K
    show Multiplicative.toAdd (π u) ∈ altFix d E
    rw [mem_altFix_iff]
    rintro g ⟨a, ha, rfl⟩ x hx
    have haA : ((a : ↥M) : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have hax : ((a : ↥M) : G) * (u : G) * ((a : ↥M) : G)⁻¹ = (u : G) :=
      mul_inv_eq_iff_eq_mul.2 (hu' (a : G) haA)
    exact (hequiv a u u hax.symm x hx.symm).symm
  have h1 := altFix_index_le hπ hequiv (A := A)
  have hVne : (Subgroup.centralizer (A : Set G)).relIndex V ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h2 := Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer (A : Set G)) hUV hVne
  have h3 : (Subgroup.centralizer (A : Set G)).relIndex U = (altFix d E).index :=
    le_antisymm (h2.trans (hV.trans hlow)) h1
  have hCpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 := Subgroup.relIndex_mul_index hle
  have h5 : ((Subgroup.centralizer (A : Set G)).subgroupOf U).relIndex C = 1 := by
    have : ((Subgroup.centralizer (A : Set G)).subgroupOf U).index = C.index := by
      rw [hidx]; exact h3
    rw [this] at h4
    exact Nat.eq_of_mul_eq_mul_right hCpos (by rw [one_mul]; exact h4)
  have hCle : C ≤ (Subgroup.centralizer (A : Set G)).subgroupOf U := Subgroup.relIndex_eq_one.1 h5
  intro u hu
  have : u ∈ C := by
    show π u ∈ K
    rw [hu]; exact hh
  exact Subgroup.mem_subgroupOf.1 (hCle this)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
