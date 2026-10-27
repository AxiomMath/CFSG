module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigDich

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem eq_bot_of_perfect_of_isSolvable {G : Type*} [Group G] [Group.IsSolvable G]
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) : (⊤ : Subgroup G) = ⊥ := by
  obtain ⟨k, hk⟩ := Group.IsSolvable.solvable (G := G)
  have h1 : ∀ j : ℕ, derivedSeries G j = ⊤ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [derivedSeries_succ, ih, hperf]
  rw [← h1 k, hk]

theorem eq_of_sup_core_of_perfect [Finite X] {N U : Subgroup X} (hUN : U ≤ N)
    (hnorm : N ≤ normalizer (U : Set X)) (hperf : ⁅N, N⁆ = N)
    (hsup : U ⊔ (pPrimeCore 2 ↥N).map N.subtype = N) : U = N := by
  set U' : Subgroup ↥N := U.subgroupOf N with hU'def
  set O' : Subgroup ↥N := pPrimeCore 2 ↥N with hO'def
  have hU'n : U'.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hU'def, mem_subgroupOf] at ha ⊢
    simpa using (mem_normalizer_iff.mp (hnorm g.2) a).mp ha
  have hsup' : U' ⊔ O' = ⊤ := by
    have h1 : (U ⊔ (pPrimeCore 2 ↥N).map N.subtype).subgroupOf N = ⊤ := by
      rw [hsup]
      exact subgroupOf_self N
    rwa [subgroupOf_sup hUN (map_subtype_le _), subgroupOf_map_subtype_self] at h1
  have hperf' : ⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆ = ⊤ := by
    apply map_injective N.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hperf]
  let π : ↥N →* ↥N ⧸ U' := QuotientGroup.mk' U'
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective U'
  have hOπ : O'.map π = ⊤ := by
    have h1 := congrArg (Subgroup.map π) hsup'
    have h2 : U'.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨u, hu, rfl⟩
      exact (QuotientGroup.eq_one_iff u).mpr hu
    rwa [Subgroup.map_sup, h2, bot_sup_eq, Subgroup.map_top_of_surjective _ hπ] at h1
  have hodd : Odd (Nat.card (↥N ⧸ U')) := by
    have h1 : Nat.card (O'.map π) ∣ Nat.card O' := Subgroup.card_map_dvd O' π
    rw [hOπ, Subgroup.card_top] at h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  have hsolv : Group.IsSolvable (↥N ⧸ U') := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hperfQ : ⁅(⊤ : Subgroup (↥N ⧸ U')), (⊤ : Subgroup (↥N ⧸ U'))⁆ = ⊤ := by
    rw [← Subgroup.map_top_of_surjective π hπ, ← map_commutator, hperf']
  have htriv := eq_bot_of_perfect_of_isSolvable hperfQ
  have hU'top : U' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (π x) ∈ (⊥ : Subgroup (↥N ⧸ U')) := htriv ▸ mem_top (π x)
    rw [mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  refine le_antisymm hUN fun x hx => ?_
  have h1 : (⟨x, hx⟩ : ↥N) ∈ U' := hU'top ▸ mem_top _
  exact h1

theorem le_core_or_eq_of_normal [Finite X] {N U : Subgroup X} {r : ℕ} (hr : 5 ≤ r)
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)) (hperf : ⁅N, N⁆ = N)
    (hUN : U ≤ N) (hnorm : N ≤ normalizer (U : Set X)) :
    U ≤ (pPrimeCore 2 ↥N).map N.subtype ∨ U = N := by
  classical
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin r)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  set U' : Subgroup ↥N := U.subgroupOf N with hU'def
  set O' : Subgroup ↥N := pPrimeCore 2 ↥N with hO'def
  have hU'n : U'.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hU'def, mem_subgroupOf] at ha ⊢
    simpa using (mem_normalizer_iff.mp (hnorm g.2) a).mp ha
  let π : ↥N →* alternatingGroup (Fin r) := θN.toMonoidHom.comp (QuotientGroup.mk' O')
  have hπ : Function.Surjective π :=
    θN.surjective.comp (QuotientGroup.mk'_surjective O')
  have hker : π.ker = O' := by
    ext x
    rw [MonoidHom.mem_ker]
    change θN (x : ↥N ⧸ O') = 1 ↔ x ∈ O'
    rw [← map_one θN, θN.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hVn : (U'.map π).Normal := hU'n.map π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U'.map π) with h | h
  · left
    intro u hu
    have h2 : π ⟨u, hUN hu⟩ = 1 := by
      have h3 : π ⟨u, hUN hu⟩ ∈ U'.map π := ⟨_, hu, rfl⟩
      rw [h, mem_bot] at h3
      exact h3
    have h4 : (⟨u, hUN hu⟩ : ↥N) ∈ O' := hker ▸ h2
    exact ⟨_, h4, rfl⟩
  · right
    refine eq_of_sup_core_of_perfect hUN hnorm hperf ?_
    have h1 : U' ⊔ O' = ⊤ := by
      have h2 := Subgroup.comap_map_eq π U'
      rw [h, Subgroup.comap_top, hker] at h2
      exact h2.symm
    have h3 := congrArg (Subgroup.map N.subtype) h1
    rwa [Subgroup.map_sup, hU'def, map_subgroupOf_eq_of_le hUN, ← MonoidHom.range_eq_map,
      range_subtype] at h3

end CFSG.ComponentClassification.SolMax
