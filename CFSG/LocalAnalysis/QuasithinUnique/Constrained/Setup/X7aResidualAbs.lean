module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section Cover

variable {G₀ : Type*} {S : Type} [Group G₀] [Group S] {π : G₀ →* S}

theorem covBy_map_of_ker_le (hπ : Function.Surjective π) {B Q : Subgroup G₀}
    (hker : π.ker ≤ B) (h : B ⋖ Q) : B.map π ⋖ Q.map π := by
  have hkQ : π.ker ≤ Q := hker.trans h.le
  have hcB : (B.map π).comap π = B := Subgroup.comap_map_eq_self hker
  have hcQ : (Q.map π).comap π = Q := Subgroup.comap_map_eq_self hkQ
  refine ⟨lt_of_le_of_ne (Subgroup.map_mono h.le) fun he => h.ne ?_, fun C hBC hCQ => ?_⟩
  · rw [← hcB, he, hcQ]
  · have hC : (C.comap π).map π = C := Subgroup.map_comap_eq_self_of_surjective hπ C
    refine h.2 (c := C.comap π) ?_ ?_
    · refine lt_of_le_of_ne (by rw [← hcB]; exact Subgroup.comap_mono hBC.le) fun he => ?_
      have := congrArg (Subgroup.map π) he
      rw [hC] at this
      exact hBC.ne this
    · refine lt_of_le_of_ne (by rw [← hcQ]; exact Subgroup.comap_mono hCQ.le) fun he => ?_
      have := congrArg (Subgroup.map π) he
      rw [hC] at this
      exact hCQ.ne this

theorem residualOvergroupsAt_of_rank_two_data [Finite S] (hπ : Function.Surjective π)
    {V B : Subgroup G₀} {Q H : Fin 2 → Subgroup G₀}
    (hker : π.ker ≤ B) (hVB : V ≤ B) (hBQ : ∀ j, B ≤ Q j) (hne : Q 0 ≠ Q 1)
    (hcov : ∀ j, B ⋖ Q j)
    (hcont : ∀ A : Subgroup G₀, V ≤ A → A ≠ ⊤ → A ≤ Q 0 ∨ A ≤ Q 1)
    (hB : Group.IsSolvable ↥B) (hc : ∀ j, ⁅Q j, Q j⁆ ≤ H j)
    (hns : ∀ j, ∀ A : Subgroup G₀, V ≤ A → A ≤ Q j → ¬ Group.IsSolvable ↥A → H j ≤ A) :
    ResidualOvergroupsAt S (V.map π) (fun j => (Q j).map π) := by
  have hkQ : ∀ j, π.ker ≤ Q j := fun j => hker.trans (hBQ j)
  have hUP : ∀ j, V.map π ≤ (Q j).map π := fun j => Subgroup.map_mono (hVB.trans (hBQ j))
  have hne' : (Q 0).map π ≠ (Q 1).map π := fun h => hne (by
    rw [← Subgroup.comap_map_eq_self (hkQ 0), h, Subgroup.comap_map_eq_self (hkQ 1)])
  have hcov' : ∀ j, B.map π ⋖ (Q j).map π := fun j => covBy_map_of_ker_le hπ hker (hcov j)
  have hQtop : ∀ j, (Q j).map π ≠ ⊤ := by
    intro j h
    fin_cases j
    · have hlt : (Q 1).map π < (Q 0).map π :=
        lt_of_le_of_ne (h ▸ le_top) (Ne.symm hne')
      exact (hcov' 0).2 (hcov' 1).lt hlt
    · have hlt : (Q 0).map π < (Q 1).map π := lt_of_le_of_ne (h ▸ le_top) hne'
      exact (hcov' 1).2 (hcov' 0).lt hlt
  have hcont' : ∀ A : Subgroup S, V.map π ≤ A → A ≠ ⊤ → A ≤ (Q 0).map π ∨ A ≤ (Q 1).map π := by
    intro A hUA hAt
    have hV : V ≤ A.comap π := Subgroup.map_le_iff_le_comap.mp hUA
    have hAt' : A.comap π ≠ ⊤ := by
      intro h
      apply hAt
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ A, h,
        Subgroup.map_top_of_surjective _ hπ]
    rcases hcont _ hV hAt' with h | h
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ A]
      exact Subgroup.map_mono h
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ A]
      exact Subgroup.map_mono h
  have hmax : ∀ A : Subgroup S, V.map π ≤ A → (A ⋖ ⊤ ↔ ∃ j, A = (Q j).map π) := by
    intro A hUA
    have := maximal_overgroups_of_covers (C := ⊤) (U := V.map π) (B := B.map π)
      (hcov' 0) (hcov' 1) le_top le_top (hQtop 0) (hQtop 1)
      (fun A hUA _ hAt => hcont' A hUA hAt) A hUA le_top
    rw [this]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨j, hj⟩
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
  have hsolv : Group.IsSolvable ↥((Q 0).map π ⊓ (Q 1).map π) := by
    rw [inf_eq_of_covBy (hcov' 0) (hcov' 1) hne']
    exact Group.isSolvable_of_surjective (f := π.subgroupMap B) (MonoidHom.subgroupMap_surjective π B)
  have hc' : ∀ j, ⁅(Q j).map π, (Q j).map π⁆ ≤ (H j).map π := by
    intro j
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (hc j)
  have hns' : ∀ j, ∀ A : Subgroup S, V.map π ≤ A → A ≤ (Q j).map π → ¬ Group.IsSolvable ↥A →
      (H j).map π ≤ A := by
    intro j A hUA hAQ hAns
    have hV : V ≤ A.comap π := Subgroup.map_le_iff_le_comap.mp hUA
    have hAQ' : A.comap π ≤ Q j := by
      have := Subgroup.comap_mono (f := π) hAQ
      rwa [Subgroup.comap_map_eq_self (hkQ j)] at this
    have hAns' : ¬ Group.IsSolvable ↥(A.comap π) := by
      intro hs
      apply hAns
      have : Group.IsSolvable ↥((A.comap π).map π) :=
        Group.isSolvable_of_surjective (f := π.subgroupMap (A.comap π))
          (MonoidHom.subgroupMap_surjective π _)
      rwa [Subgroup.map_comap_eq_self_of_surjective hπ A] at this
    have := hns j _ hV hAQ' hAns'
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ A]
    exact Subgroup.map_mono this
  obtain ⟨h2, h3⟩ := residual_abstract (G := S) (U := V.map π) (P := fun j => (Q j).map π)
    (N := fun j => (H j).map π) hne' hUP hmax hsolv hc' hns'
  exact ⟨hne', hUP, hmax, hsolv, h2, h3⟩

end Cover

end CFSG.QuasithinUnique.Setup.X7a
