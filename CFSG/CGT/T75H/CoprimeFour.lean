module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddFourActorFixedGeneration
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CommutingInvolutionClosure
public import CFSG.Dihedral.DisconnectedInvolutionGraph.SubgroupConjugationAction

public section

namespace CFSG.CGT.T75H

open CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_sylow_of_isPGroup_two {N S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hNodd : Odd (Nat.card N)) (hSN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (q : ℕ)
    [Fact q.Prime] :
    ∃ P : Subgroup G, P ≤ N ∧ IsPGroup q P ∧ ¬ q ∣ P.relIndex N ∧
      ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := subgroupConjugationAction S
  have hinv : InvariantSubgroup (A := S) N := fun s n hn => hSN s s.2 n hn
  let _ := invariantSubgroupAction N hinv
  have hcop : ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)
  obtain ⟨P, hP⟩ := coprime_pgroup_exists_invariant_sylow (G := N) (A := S) 2 q hS2 hcop
  refine ⟨(P : Subgroup N).map N.subtype, ?_, P.isPGroup'.map _, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have : ((P : Subgroup N).map N.subtype).subgroupOf N = (P : Subgroup N) :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    unfold Subgroup.relIndex
    rw [this]
    exact P.not_dvd_index
  · rintro s hs _ ⟨x, hx, rfl⟩
    have := hP ⟨s, hs⟩ x hx
    exact ⟨_, this, rfl⟩

theorem le_sup_fixed_of_commuting_involutions {P : Subgroup G} (hPodd : Odd (Nat.card P))
    {α β : G} (hα : α * α = 1) (hβ : β * β = 1) (hαβ : α * β = β * α) (hα1 : α ≠ 1)
    (hβ1 : β ≠ 1) (hne : α ≠ β) (hαP : ∀ p ∈ P, α * p * α⁻¹ ∈ P)
    (hβP : ∀ p ∈ P, β * p * β⁻¹ ∈ P) :
    P ≤ (P ⊓ Subgroup.centralizer ({α} : Set G)) ⊔ (P ⊓ Subgroup.centralizer ({β} : Set G)) ⊔
      (P ⊓ Subgroup.centralizer ({α * β} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let first : Involution G := ⟨α, orderOf_eq_prime (by rw [sq]; exact hα) hα1⟩
  let second : Involution G := ⟨β, orderOf_eq_prime (by rw [sq]; exact hβ) hβ1⟩
  have hcommute : (first : G) * second = (second : G) * first := hαβ
  let actor := Subgroup.closure ({(first : G), (second : G)} : Set G)
  have hgeneratorsCommute : ∀ firstElement ∈ ({(first : G), (second : G)} : Set G),
      ∀ secondElement ∈ ({(first : G), (second : G)} : Set G),
        firstElement * secondElement = secondElement * firstElement := by
    intro firstElement hfirst secondElement hsecond
    rcases Set.mem_insert_iff.mp hfirst with rfl | hfirst
    · rcases Set.mem_insert_iff.mp hsecond with rfl | hsecond
      · rfl
      · rw [Set.mem_singleton_iff.mp hsecond]
        exact hcommute
    · rw [Set.mem_singleton_iff.mp hfirst]
      rcases Set.mem_insert_iff.mp hsecond with rfl | hsecond
      · exact hcommute.symm
      · rw [Set.mem_singleton_iff.mp hsecond]
  let _ : IsMulCommutative actor := CFSG.subgroup_isMulCommutative_closure hgeneratorsCommute
  let _ : CommGroup actor := { (inferInstance : Group actor) with mul_comm := mul_comm' }
  let _ := subgroupConjugationAction actor
  have hnormα : (first : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hαP h, fun hh => ?_⟩
    have := hαP _ hh
    have e : α * (α * h * α⁻¹) * α⁻¹ = h := by
      calc α * (α * h * α⁻¹) * α⁻¹ = (α * α) * h * (α * α)⁻¹ := by group
        _ = h := by rw [hα]; group
    rwa [e] at this
  have hnormβ : (second : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hβP h, fun hh => ?_⟩
    have := hβP _ hh
    have e : β * (β * h * β⁻¹) * β⁻¹ = h := by
      calc β * (β * h * β⁻¹) * β⁻¹ = (β * β) * h * (β * β)⁻¹ := by group
        _ = h := by rw [hβ]; group
    rwa [e] at this
  have hactorLe : actor ≤ Subgroup.normalizer (P : Set G) := by
    apply (Subgroup.closure_le _).mpr
    intro element hmem
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem
    · exact hnormα
    · rw [Set.mem_singleton_iff.mp hmem]
      exact hnormβ
  let _ := invariantSubgroupAction P
    (subgroup_conjugation_invariant_of_le_normalizer P actor hactorLe)
  let firstActor : actor := ⟨first, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  let secondActor : actor := ⟨second, Subgroup.subset_closure
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  have hfirstSquare : firstActor * firstActor = 1 := Subtype.ext hα
  have hsecondSquare : secondActor * secondActor = 1 := Subtype.ext hβ
  set target := (P ⊓ Subgroup.centralizer ({α} : Set G)) ⊔
    (P ⊓ Subgroup.centralizer ({β} : Set G)) ⊔ (P ⊓ Subgroup.centralizer ({α * β} : Set G))
    with htarget
  have hfixed : ∀ (γ : G) (a : actor), (a : G) = γ →
      actorFixedSubgroup (G := P) a ≤ (P ⊓ Subgroup.centralizer ({γ} : Set G)).subgroupOf P := by
    intro γ a ha e he
    refine Subgroup.mem_subgroupOf.2 ⟨e.2, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.2
    have hconj := congrArg Subtype.val he
    change (a : G) * e.val * (a : G)⁻¹ = e.val at hconj
    rw [ha] at hconj
    exact ((mul_inv_eq_iff_eq_mul).mp hconj).symm
  have hgenerated := odd_two_group_action_commuting_involutions_fixed_generate
    (commuting_involution_closure_isPGroup first second hcommute) hPodd
    firstActor secondActor hfirstSquare hsecondSquare
  intro x hx
  have hmem : (⟨x, hx⟩ : P) ∈ (⊤ : Subgroup P) := Subgroup.mem_top _
  rw [← hgenerated] at hmem
  have hmono : ∀ A : Subgroup G, A ≤ target → A.subgroupOf P ≤ target.subgroupOf P :=
    fun A hA e he => Subgroup.mem_subgroupOf.2 (hA (Subgroup.mem_subgroupOf.1 he))
  have hle : actorFixedSubgroup (G := P) firstActor ⊔ actorFixedSubgroup (G := P) secondActor ⊔
      actorFixedSubgroup (G := P) (firstActor * secondActor) ≤ target.subgroupOf P := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (hfixed α firstActor rfl).trans (hmono _ (le_sup_of_le_left le_sup_left))
    · exact (hfixed β secondActor rfl).trans (hmono _ (le_sup_of_le_left le_sup_right))
    · exact (hfixed (α * β) (firstActor * secondActor) rfl).trans (hmono _ le_sup_right)
  exact Subgroup.mem_subgroupOf.1 (hle hmem)

end CFSG.CGT.T75H
