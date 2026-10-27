module

public import CFSG.ClassicalInvolution.Q3.Q3DBEdge
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem commutes_or_eq_at_involution (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : IsClassicalMember3 K z)
    (hW : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hIH : LocalLieSystems3 (CoreAssembly.conjClass K)) {N : Subgroup G}
    (hN : N ∈ CoreAssembly.conjClass K) {y : G} (hy : IsClassicalMember3 N y) {L : Subgroup G}
    (hL : L ∈ centralizingMembers (CoreAssembly.conjClass K) {y}) : Commutes N L ∨ L = N := by
  obtain ⟨g, hg⟩ := id hN
  have hyg : y = g * z * g⁻¹ := involution_unique3 hy (hg ▸ hK.conj g)
  have hWy : Balance.oddCoreIn (Subgroup.centralizer ({y} : Set G)) = ⊥ := by
    rw [hyg]
    exact oddCoreIn_centralizer_conj g hW
  have hΩ : InClass3 (CoreAssembly.conjClass K) := inClass3_conjugates hK
  obtain ⟨ι, hι, ⟨D⟩⟩ := hIH {y} (Q3W.not_subset_center_of_ne_one hnab hy.ne_one)
  exact Q3W.commutes_or_eq_of_involution3 (RouteD.Gaps.fundNoncentral 3) hΩ
    (exactMembers3_of_oddCentralizerFree hK hW)
    (localOddCentral_of_oddCentralizerFree hΩ.conjInvariant hWy)
    (localOddThreeFree3_of_oddCentralizerFree hΩ.conjInvariant hWy) D
    ⟨hN, isSubnormal_le hy.subnormal⟩ hL hy

theorem commutes_or_eq_of_dAdj (hnab : ∃ x y : G, x * y ≠ y * x) (hK : IsClassicalMember3 K z)
    (hW : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hIH : LocalLieSystems3 (CoreAssembly.conjClass K)) {M N : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass K) (hN : N ∈ CoreAssembly.conjClass K)
    (h : dAdj (CoreAssembly.conjClass K) M N) : Commutes M N ∨ N = M := by
  have key : ∀ {M N : Subgroup G}, M ∈ CoreAssembly.conjClass K →
      N ∈ omegaNbr (CoreAssembly.conjClass K) M → Commutes M N ∨ N = M := by
    intro M N hM hN
    have hΩ : InClass3 (CoreAssembly.conjClass K) := inClass3_conjugates hK
    obtain ⟨a, ha⟩ := hΩ.classical M hM
    have hcent := centralizes_of_mem_omegaNbr hK hW hN ha
    exact commutes_or_eq_at_involution hnab hK hW hIH hM ha
      ⟨hN.1, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcent x hx).symm⟩
  rcases h with h | h
  · exact key hM h
  · rcases key hN h with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm

theorem omegaConnected_of_dConnected (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : IsClassicalMember3 K z)
    (hW : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hIH : LocalLieSystems3 (CoreAssembly.conjClass K))
    (hD : DConnected (CoreAssembly.conjClass K)) : OmegaConnected (CoreAssembly.conjClass K) := by
  intro L hL L' hL'
  have key : ∀ X, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ dAdj (CoreAssembly.conjClass K) M N)
      L X → X ∈ CoreAssembly.conjClass K ∧ Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ Commutes M N) L X := by
    intro X hX
    induction hX with
    | refl => exact ⟨hL, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.1, ?_⟩
      rcases commutes_or_eq_of_dAdj hnab hK hW hIH ih.1 hbc.1 hbc.2 with h | h
      · exact ih.2.tail ⟨hbc.1, h⟩
      · rw [h]
        exact ih.2
  exact (key L' (hD L hL L' hL')).2

omit [Finite G] [IsSimpleGroup G] in
theorem deltaConnected_of_omegaConnected {K : Subgroup G}
    (h : OmegaConnected (CoreAssembly.conjClass K)) :
    CFSG.ClassicalInvolution.DeltaConnected K := by
  intro A hA B hB
  rw [CoreAssembly.conjugateSet_eq_range] at hA hB
  have key : ∀ X, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ Commutes M N) A X →
      X ∈ CoreAssembly.conjClass K ∧
        Relation.ReflTransGen (CFSG.ClassicalInvolution.commutingAdj K) A X := by
    intro X hX
    induction hX with
    | refl => exact ⟨hA, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.1, ?_⟩
      by_cases hne : b = c
      · rw [← hne]
        exact ih.2
      · refine ih.2.tail ⟨?_, ?_, hne, hbc.2⟩
        · rw [CoreAssembly.conjugateSet_eq_range]
          exact ih.1
        · rw [CoreAssembly.conjugateSet_eq_range]
          exact hbc.1
  exact (key B (h A hA B hB)).2

theorem deltaConnected_of_dConnected_of_oddCentralizerFree (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : IsClassicalMember3 K z)
    (hW : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hBelow : CIT3Below (Nat.card G)) (hD : DConnected (CoreAssembly.conjClass K)) :
    CFSG.ClassicalInvolution.DeltaConnected K :=
  deltaConnected_of_omegaConnected
    (omegaConnected_of_dConnected hnab hK hW
      (localLieSystems3_of_cit3Below (inClass3_conjugates hK) hBelow) hD)

end CFSG.ClassicalInvolution.Q3.Q3DB
