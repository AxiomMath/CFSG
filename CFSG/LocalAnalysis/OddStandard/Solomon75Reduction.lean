module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def Solomon75LocalStructure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], ∀ z : G, orderOf z = 2 →
    ∀ (L : Subgroup G) (n : ℕ), 8 ≤ n → L ≤ centralizer ({z} : Set G) →
      IsPComponent 2 (L.subgroupOf (centralizer ({z} : Set G))) → z ∈ L →
      Group.IsPerfect (L ⧸ pPrimeCore 2 L) → Nat.card (center (L ⧸ pPrimeCore 2 L)) = 2 →
      Nonempty ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃*
        alternatingGroup (Fin n)) →
      ∃ m : ℕ, 8 ≤ m ∧ m ≤ 11 ∧
        IsDoubleCoverOfAlt
          (↥(centralizer ({z} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({z} : Set G))) m

theorem alternatingGroup_nontrivial {n : ℕ} (hn : 3 ≤ n) :
    Nontrivial (alternatingGroup (Fin n)) := by
  refine ⟨⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩,
    ?_⟩, 1, ?_⟩⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · intro h
    have h2 := congrArg
      (fun p : alternatingGroup (Fin n) => (p : Equiv.Perm (Fin n)) ⟨0, by omega⟩) h
    simp [Equiv.swap_apply_def] at h2

theorem nonabelian_of_quotient_alt {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hquot : Nonempty ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃*
      alternatingGroup (Fin n))) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨e⟩ := hquot
  have := alternatingGroup_nontrivial hn
  obtain ⟨u, hu⟩ := exists_ne (1 : alternatingGroup (Fin n))
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm u)
  have hcen : ∀ y : L ⧸ pPrimeCore 2 L, y ∈ center (L ⧸ pPrimeCore 2 L) := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
    exact congrArg QuotientGroup.mk (Subtype.ext (hcomm _ _))
  have h1 : (x : (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)) = 1 :=
    (QuotientGroup.eq_one_iff x).mpr (hcen x)
  apply hu
  rw [← e.symm.injective.eq_iff, map_one, ← hx, h1]

theorem solomon2AnInput_of_localStructure (hMcL : Solomon44McL) (hLy : Solomon44Ly)
    (hNT : Solomon44NineTen) (hS : Solomon75LocalStructure) :
    ComponentClassification.GSThmB.Solomon2AnInput := by
  intro G _ _ _ z hz L n hn hLC hLpc hzL hperf hcard hquot
  obtain ⟨m, hm8, hm11, hcov⟩ := hS G z hz L n hn hLC hLpc hzL hperf hcard hquot
  have hnonab : ∃ a b : G, a * b ≠ b * a := nonabelian_of_quotient_alt (by omega) hquot
  interval_cases m
  · exact Or.inl (hMcL G hnonab z hz hcov)
  · exact absurd hcov (hNT G hnonab z hz 9 (Or.inl rfl))
  · exact absurd hcov (hNT G hnonab z hz 10 (Or.inr rfl))
  · exact Or.inr (hLy G hnonab z hz hcov)

end CFSG.OddStandard.Solomon75
