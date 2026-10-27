module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphE6

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm)

local instance f4PilotCTGraphFamilyNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def e6A5Nodes : Finset (Fin (Tag.rank .E6)) := {0, 2, 3, 4, 5}

@[expose] def e6D4Nodes : Finset (Fin (Tag.rank .E6)) := {1, 2, 3, 4}

@[expose] def e6A3Nodes : Finset (Fin (Tag.rank .E6)) := {2, 3, 4}

theorem subset_e6A5Nodes_of_one_not_mem {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J) : J ⊆ e6A5Nodes := by
  intro a ha
  have key : ∀ b : Fin (Tag.rank .E6), b ≠ 1 → b ∈ e6A5Nodes := by decide
  exact key a fun h => h1 (h ▸ ha)

theorem subset_e6D4Nodes_of_not_mem {J : Finset (Fin (Tag.rank .E6))}
    (h0 : (0 : Fin (Tag.rank .E6)) ∉ J) (h5 : (5 : Fin (Tag.rank .E6)) ∉ J) : J ⊆ e6D4Nodes := by
  intro a ha
  have key : ∀ b : Fin (Tag.rank .E6), b ≠ 0 → b ≠ 5 → b ∈ e6D4Nodes := by decide
  exact key a (fun h => h0 (h ▸ ha)) fun h => h5 (h ▸ ha)

theorem subset_e6A3Nodes_of_not_mem {J : Finset (Fin (Tag.rank .E6))}
    (h0 : (0 : Fin (Tag.rank .E6)) ∉ J) (h1 : (1 : Fin (Tag.rank .E6)) ∉ J)
    (h5 : (5 : Fin (Tag.rank .E6)) ∉ J) : J ⊆ e6A3Nodes := by
  intro a ha
  have key : ∀ b : Fin (Tag.rank .E6), b ≠ 0 → b ≠ 1 → b ≠ 5 → b ∈ e6A3Nodes := by decide
  exact key a (fun h => h0 (h ▸ ha)) (fun h => h1 (h ▸ ha)) fun h => h5 (h ▸ ha)

theorem e6A3Nodes_subset_e6A5Nodes : e6A3Nodes ⊆ e6A5Nodes := by decide

theorem e6A3Nodes_subset_e6D4Nodes : e6A3Nodes ⊆ e6D4Nodes := by decide

theorem one_subset_e6D4Nodes : ({1} : Finset (Fin (Tag.rank .E6))) ⊆ e6D4Nodes := by decide

theorem singleton_subset_e6A5Nodes_of {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5) :
    ({j} : Finset (Fin (Tag.rank .E6))) ⊆ e6A5Nodes := by
  rcases hj with rfl | rfl <;> decide

theorem one_ne_of_end {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5) :
    (1 : Fin (Tag.rank .E6)) ≠ j := by
  rcases hj with rfl | rfl <;> decide

theorem e6RhoPerm_one : rhoPerm (1 : Fin (Tag.rank .E6)) = 1 := by decide

theorem rhoPerm_ne_one {i : Fin (Tag.rank .E6)} (hi : i ≠ 1) : rhoPerm i ≠ 1 := by
  revert i
  decide

theorem rhoPerm_mem_e6D4Nodes {i : Fin (Tag.rank .E6)} (hi : i ∈ e6D4Nodes) :
    rhoPerm i ∈ e6D4Nodes := by
  revert i
  decide

theorem rhoPerm_mem_e6D4Nodes' : ∀ i ∈ e6D4Nodes, rhoPerm i ∈ e6D4Nodes :=
  fun _ hi => rhoPerm_mem_e6D4Nodes hi

theorem mem_e6A3Nodes_of_mem_e6D4Nodes {i : Fin (Tag.rank .E6)} (hi : i ∈ e6D4Nodes)
    (hi1 : i ≠ 1) : i ∈ e6A3Nodes := by
  revert i
  decide

theorem ne_one_of_mem_e6A5Nodes {i : Fin (Tag.rank .E6)} (hi : i ∈ e6A5Nodes) : i ≠ 1 := by
  revert i
  decide

theorem zero_not_mem_one : (0 : Fin (Tag.rank .E6)) ∉ ({1} : Finset (Fin (Tag.rank .E6))) := by
  decide

theorem five_not_mem_one : (5 : Fin (Tag.rank .E6)) ∉ ({1} : Finset (Fin (Tag.rank .E6))) := by
  decide

theorem zero_cases_end : (0 : Fin (Tag.rank .E6)) = 0 ∨ (0 : Fin (Tag.rank .E6)) = 5 := Or.inl rfl

theorem five_cases_end : (5 : Fin (Tag.rank .E6)) = 0 ∨ (5 : Fin (Tag.rank .E6)) = 5 := Or.inr rfl

theorem five_ne_zero_E6 : (5 : Fin (Tag.rank .E6)) ≠ 0 := by decide

theorem five_ne_one_E6' : (5 : Fin (Tag.rank .E6)) ≠ 1 := by decide

theorem e6_root_support_one_zero_five_check :
    ∀ γ ∈ rootFinset .E6, γ 2 = 0 → γ 3 = 0 → γ 4 = 0 →
      (γ 5 = 0 → γ 1 = 0 ∨ γ 0 = 0) ∧ (γ 0 = 0 → γ 1 = 0 ∨ γ 5 = 0) := by
  decide +kernel

section Pair

variable {K : Type} [Field K]

variable (K) in
noncomputable abbrev e6ScLevi (S : Finset (Fin (Tag.rank .E6))) :
    Subgroup (e6Data_valid.minGroup K) :=
  CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup S

theorem commute_scRootGroup_one_end {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5)
    {s t : Fin (Tag.rank .E6) → ℤ} (hs : s = Pi.single 1 1 ∨ s = -Pi.single 1 1)
    (ht : t = Pi.single j 1 ∨ t = -Pi.single j 1) {x y : e6Data_valid.minGroup K}
    (hx : x ∈ (e6Datum K).rootGroup s) (hy : y ∈ (e6Datum K).rootGroup t) : Commute x y := by
  have hroot : ∀ v, v ∈ (e6Datum K).roots ↔ IsRoot .E6 v := fun v =>
    e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 K
  refine commute_of_forall_not_mem_roots (e6Datum_steinbergExtras K) ?_ ?_ ?_ ?_ hx hy
  · rw [hroot]
    rcases hs with rfl | rfl
    exacts [isRoot_single _ 1, isRoot_neg_single _ 1]
  · rw [hroot]
    rcases ht with rfl | rfl
    exacts [isRoot_single _ j, isRoot_neg_single _ j]
  · intro a b hab
    have h1 := congrFun hab 1
    have hjj := congrFun hab j
    rcases hj with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp +decide at h1 hjj <;> exact ⟨h1, hjj⟩
  · intro a b ha hb hmem
    rw [hroot, ← mem_rootFinset] at hmem
    have h := e6_root_support_one_zero_five_check _ hmem
    rcases hj with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp +decide at h <;> omega

theorem commute_scLevi_one_end {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5) :
    ∀ x ∈ e6ScLevi K {1}, ∀ y ∈ e6ScLevi K {j}, Commute x y := by
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton,
    CFSG.LieType.CurtisTits.rankOne, CFSG.LieType.CurtisTits.rankOne]
  refine forall_commute_sup_left (forall_commute_sup_right ?_ ?_)
    (forall_commute_sup_right ?_ ?_)
  · exact fun x hx y hy => commute_scRootGroup_one_end hj (Or.inl rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one_end hj (Or.inl rfl) (Or.inr rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one_end hj (Or.inr rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one_end hj (Or.inr rfl) (Or.inr rfl) hx hy

theorem scLevi_one_inf_end_eq_bot {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5) :
    e6ScLevi K {1} ⊓ e6ScLevi K {j} = ⊥ := by
  have hc := commute_scLevi_one_end (K := K) hj
  dsimp only [e6ScLevi] at hc ⊢
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton] at hc ⊢
  exact rankOne_inf_rankOne_eq_bot (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K)
    (one_ne_of_end hj) hc

theorem scLevi_le_pair {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5) (h1 : (1 : Fin (Tag.rank .E6)) ∈ J)
    (hjJ : j ∈ J) :
    e6ScLevi K J ≤ e6ScLevi K {1} ⊔ e6ScLevi K {j} := by
  dsimp only [e6ScLevi]
  rw [E6Pilot.eq_pair_of_card_le_two hJ (one_ne_of_end hj) h1 hjJ, levi_pair]

end Pair

section Family

variable {K : Type} [Field K] {G : Type} [Group G]

@[expose] noncomputable def scLeviRestrict {S J : Finset (Fin (Tag.rank .E6))}
    (Φ : e6ScLevi K S →* G) (h : J ⊆ S) : e6ScLevi K J →* G :=
  Φ.comp (Subgroup.inclusion (CFSG.LieType.CurtisTits.levi_mono _ h))

theorem scLeviRestrict_apply {S J : Finset (Fin (Tag.rank .E6))} (Φ : e6ScLevi K S →* G)
    (h : J ⊆ S) (x : e6ScLevi K J) :
    scLeviRestrict Φ h x = Φ ⟨x, CFSG.LieType.CurtisTits.levi_mono _ h x.2⟩ :=
  rfl

theorem scLeviRestrict_eq_of_coe_eq {S I J : Finset (Fin (Tag.rank .E6))}
    (Φ : e6ScLevi K S →* G) (hI : I ⊆ S) (hJ : J ⊆ S) (x : e6ScLevi K I) (y : e6ScLevi K J)
    (hxy : (x : e6Data_valid.minGroup K) = y) : scLeviRestrict Φ hI x = scLeviRestrict Φ hJ y := by
  rw [scLeviRestrict_apply, scLeviRestrict_apply]
  congr 1
  exact Subtype.ext hxy

variable (ΦA : e6ScLevi K e6A5Nodes →* G) (ΦD : e6ScLevi K e6D4Nodes →* G)

@[expose] noncomputable def graphPairLift {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5)
    (hc : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b)) :
    ↥(e6ScLevi K {1} ⊔ e6ScLevi K {j}) →* G :=
  supLift (commute_scLevi_one_end hj) (scLevi_one_inf_end_eq_bot hj) _ _ hc

theorem graphPairLift_of_mem_left {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5)
    (hc : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b))
    (z : ↥(e6ScLevi K {1} ⊔ e6ScLevi K {j}))
    (hz : (z : e6Data_valid.minGroup K) ∈ e6ScLevi K {1}) :
    graphPairLift ΦA ΦD hj hc z = scLeviRestrict ΦD one_subset_e6D4Nodes ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_left (commute_scLevi_one_end hj) (scLevi_one_inf_end_eq_bot hj) hc ⟨z, hz⟩

theorem graphPairLift_of_mem_right {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5)
    (hc : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b))
    (z : ↥(e6ScLevi K {1} ⊔ e6ScLevi K {j}))
    (hz : (z : e6Data_valid.minGroup K) ∈ e6ScLevi K {j}) :
    graphPairLift ΦA ΦD hj hc z = scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_right (commute_scLevi_one_end hj) (scLevi_one_inf_end_eq_bot hj) hc ⟨z, hz⟩

theorem range_graphPairLift {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5)
    (hc : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b)) :
    (graphPairLift ΦA ΦD hj hc).range ≤ ΦA.range ⊔ ΦD.range := by
  rw [graphPairLift, range_supLift]
  refine sup_le (le_sup_of_le_right ?_) (le_sup_of_le_left ?_) <;>
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩

variable (hc0 : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of zero_cases_end) b))
  (hc5 : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of five_cases_end) b))

@[expose] noncomputable def graphFamilyE6
    (J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}) :
    (e6Datum K).leviAmalgam J →* G :=
  if h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1 then
    if h0 : (0 : Fin (Tag.rank .E6)) ∈ J.1 then
      (graphPairLift ΦA ΦD zero_cases_end hc0).comp
        (Subgroup.inclusion (scLevi_le_pair J.2 zero_cases_end h1 h0))
    else if h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1 then
      (graphPairLift ΦA ΦD five_cases_end hc5).comp
        (Subgroup.inclusion (scLevi_le_pair J.2 five_cases_end h1 h5))
    else scLeviRestrict ΦD (subset_e6D4Nodes_of_not_mem h0 h5)
  else scLeviRestrict ΦA (subset_e6A5Nodes_of_one_not_mem h1)

variable {ΦA ΦD hc0 hc5}

theorem graphFamilyE6_of_one_not_mem {J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J.1) (x : (e6Datum K).leviAmalgam J) :
    graphFamilyE6 ΦA ΦD hc0 hc5 J x =
      scLeviRestrict ΦA (subset_e6A5Nodes_of_one_not_mem h1) x := by
  rw [graphFamilyE6, dite_eq_right h1]

theorem graphFamilyE6_of_d4 {J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h0 : (0 : Fin (Tag.rank .E6)) ∉ J.1)
    (h5 : (5 : Fin (Tag.rank .E6)) ∉ J.1) (x : (e6Datum K).leviAmalgam J) :
    graphFamilyE6 ΦA ΦD hc0 hc5 J x =
      scLeviRestrict ΦD (subset_e6D4Nodes_of_not_mem h0 h5) x := by
  rw [graphFamilyE6, dite_eq_left h1, dite_eq_right h0, dite_eq_right h5]

theorem graphFamilyE6_of_zero {J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h0 : (0 : Fin (Tag.rank .E6)) ∈ J.1)
    (x : (e6Datum K).leviAmalgam J) :
    graphFamilyE6 ΦA ΦD hc0 hc5 J x =
      graphPairLift ΦA ΦD zero_cases_end hc0 ⟨x, scLevi_le_pair J.2 zero_cases_end h1 h0 x.2⟩ := by
  rw [graphFamilyE6, dite_eq_left h1, dite_eq_left h0]
  rfl

theorem graphFamilyE6_of_five {J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h0 : (0 : Fin (Tag.rank .E6)) ∉ J.1)
    (h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1) (x : (e6Datum K).leviAmalgam J) :
    graphFamilyE6 ΦA ΦD hc0 hc5 J x =
      graphPairLift ΦA ΦD five_cases_end hc5 ⟨x, scLevi_le_pair J.2 five_cases_end h1 h5 x.2⟩ := by
  rw [graphFamilyE6, dite_eq_left h1, dite_eq_right h0, dite_eq_left h5]
  rfl

theorem isCompatible_graphFamilyE6
    (hagree : ∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
      scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes x) :
    IsCompatible (e6Datum K).leviAmalgam (graphFamilyE6 ΦA ΦD hc0 hc5) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ j.1 := hij
  have hmono : ∀ {I : Finset (Fin (Tag.rank .E6))}, (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ I →
      (y : e6Data_valid.minGroup K) ∈ e6ScLevi K I :=
    fun h => hxy ▸ CFSG.LieType.CurtisTits.levi_mono _ h x.2
  by_cases h1j : (1 : Fin (Tag.rank .E6)) ∈ j.1
  · by_cases h0j : (0 : Fin (Tag.rank .E6)) ∈ j.1
    ·
      have hj : (j.1 : Finset (Fin (Tag.rank .E6))) = {1, 0} :=
        E6Pilot.eq_pair_of_card_le_two j.2 (one_ne_of_end zero_cases_end) h1j h0j
      have hij' : ∀ a ∈ i.1, a = 1 ∨ a = 0 := fun a ha => by
        have := hsub ha
        rw [hj, Finset.mem_insert, Finset.mem_singleton] at this
        exact this
      rw [graphFamilyE6_of_zero h1j h0j]
      by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
      · by_cases h0i : (0 : Fin (Tag.rank .E6)) ∈ i.1
        · rw [graphFamilyE6_of_zero h1i h0i]
          exact congrArg _ (Subtype.ext hxy)
        · have h5i : (5 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => by
            rcases hij' 5 h with h' | h'
            exacts [five_ne_one_E6' h', five_ne_zero_E6 h']
          have hi1 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {1} := fun a ha => by
            rcases hij' a ha with rfl | rfl
            · exact Finset.mem_singleton_self _
            · exact absurd ha h0i
          rw [graphFamilyE6_of_d4 h1i h0i h5i, graphPairLift_of_mem_left _ _ _ hc0 _ (hmono hi1)]
          exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
      · have hi0 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {0} := fun a ha => by
          rcases hij' a ha with rfl | rfl
          · exact absurd ha h1i
          · exact Finset.mem_singleton_self _
        rw [graphFamilyE6_of_one_not_mem h1i, graphPairLift_of_mem_right _ _ _ hc0 _ (hmono hi0)]
        exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
    · have h0i : (0 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h0j (hsub h)
      by_cases h5j : (5 : Fin (Tag.rank .E6)) ∈ j.1
      ·
        have hj : (j.1 : Finset (Fin (Tag.rank .E6))) = {1, 5} :=
          E6Pilot.eq_pair_of_card_le_two j.2 (one_ne_of_end five_cases_end) h1j h5j
        have hij' : ∀ a ∈ i.1, a = 1 ∨ a = 5 := fun a ha => by
          have := hsub ha
          rw [hj, Finset.mem_insert, Finset.mem_singleton] at this
          exact this
        rw [graphFamilyE6_of_five h1j h0j h5j]
        by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
        · by_cases h5i : (5 : Fin (Tag.rank .E6)) ∈ i.1
          · rw [graphFamilyE6_of_five h1i h0i h5i]
            exact congrArg _ (Subtype.ext hxy)
          · have hi1 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {1} := fun a ha => by
              rcases hij' a ha with rfl | rfl
              · exact Finset.mem_singleton_self _
              · exact absurd ha h5i
            rw [graphFamilyE6_of_d4 h1i h0i h5i,
              graphPairLift_of_mem_left _ _ _ hc5 _ (hmono hi1)]
            exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
        · have hi5 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {5} := fun a ha => by
            rcases hij' a ha with rfl | rfl
            · exact absurd ha h1i
            · exact Finset.mem_singleton_self _
          rw [graphFamilyE6_of_one_not_mem h1i,
            graphPairLift_of_mem_right _ _ _ hc5 _ (hmono hi5)]
          exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
      ·
        have h5i : (5 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h5j (hsub h)
        rw [graphFamilyE6_of_d4 h1j h0j h5j]
        by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
        · rw [graphFamilyE6_of_d4 h1i h0i h5i]
          exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
        · rw [graphFamilyE6_of_one_not_mem h1i]
          have hxA : (x : e6Data_valid.minGroup K) ∈ e6ScLevi K e6A3Nodes :=
            CFSG.LieType.CurtisTits.levi_mono _ (subset_e6A3Nodes_of_not_mem h0i h1i h5i) x.2
          rw [scLeviRestrict_eq_of_coe_eq ΦA _ e6A3Nodes_subset_e6A5Nodes x ⟨x, hxA⟩ rfl,
            hagree, scLeviRestrict_eq_of_coe_eq ΦD e6A3Nodes_subset_e6D4Nodes _ ⟨x, hxA⟩ y hxy]
  · have h1i : (1 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h1j (hsub h)
    rw [graphFamilyE6_of_one_not_mem h1i, graphFamilyE6_of_one_not_mem h1j]
    exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy

theorem range_le_of_forall_scLevi_singleton {S : Finset (Fin (Tag.rank .E6))}
    (Φ : e6ScLevi K S →* G) {H : Subgroup G}
    (h : ∀ i (hi : i ∈ S) (x : e6ScLevi K {i}),
      scLeviRestrict Φ (Finset.singleton_subset_iff.2 hi) x ∈ H) : Φ.range ≤ H := by
  rintro _ ⟨x, rfl⟩
  have hle : e6ScLevi K S ≤ (H.comap Φ).map (e6ScLevi K S).subtype := by
    show (⨆ j ∈ S, CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup j) ≤ _
    refine iSup₂_le fun i hi y hy => ?_
    have hy' : y ∈ e6ScLevi K {i} := by
      rw [e6ScLevi, CFSG.LieType.CurtisTits.levi_singleton]
      exact hy
    exact ⟨⟨y, CFSG.LieType.CurtisTits.levi_mono _ (Finset.singleton_subset_iff.2 hi) hy'⟩,
      h i hi ⟨y, hy'⟩, rfl⟩
  obtain ⟨x', hx', hxx'⟩ := hle x.2
  have hx : x' = x := Subtype.ext hxx'
  rw [← hx]
  exact hx'

theorem iSup_range_graphFamilyE6
    (hagree : ∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
      scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes x) :
    ⨆ J, (graphFamilyE6 ΦA ΦD hc0 hc5 J).range = ΦA.range ⊔ ΦD.range := by
  have hmem : ∀ (J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2})
      (x : (e6Datum K).leviAmalgam J),
      graphFamilyE6 ΦA ΦD hc0 hc5 J x ∈ ⨆ J, (graphFamilyE6 ΦA ΦD hc0 hc5 J).range :=
    fun J x => le_iSup (fun J => (graphFamilyE6 ΦA ΦD hc0 hc5 J).range) J ⟨x, rfl⟩
  apply le_antisymm
  · refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1
    · by_cases h0 : (0 : Fin (Tag.rank .E6)) ∈ J.1
      · rw [graphFamilyE6_of_zero h1 h0]
        exact range_graphPairLift _ _ _ _ ⟨_, rfl⟩
      · by_cases h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1
        · rw [graphFamilyE6_of_five h1 h0 h5]
          exact range_graphPairLift _ _ _ _ ⟨_, rfl⟩
        · rw [graphFamilyE6_of_d4 h1 h0 h5]
          exact mem_sup_right ⟨_, rfl⟩
    · rw [graphFamilyE6_of_one_not_mem h1]
      exact mem_sup_left ⟨_, rfl⟩
  · refine sup_le ?_ ?_
    · refine range_le_of_forall_scLevi_singleton ΦA fun i hi x => ?_
      have hi1 : (1 : Fin (Tag.rank .E6)) ∉ ({i} : Finset (Fin (Tag.rank .E6))) := by
        rw [Finset.mem_singleton]
        exact fun h => ne_one_of_mem_e6A5Nodes hi h.symm
      rw [scLeviRestrict_eq_of_coe_eq ΦA _ (subset_e6A5Nodes_of_one_not_mem hi1) x x rfl,
        ← graphFamilyE6_of_one_not_mem (J := ⟨{i}, card_singleton_le_two_E6 i⟩) hi1 x]
      exact hmem ⟨{i}, card_singleton_le_two_E6 i⟩ x
    · refine range_le_of_forall_scLevi_singleton ΦD fun i hi x => ?_
      by_cases hi1 : i = 1
      · subst hi1
        rw [scLeviRestrict_eq_of_coe_eq ΦD _
          (subset_e6D4Nodes_of_not_mem zero_not_mem_one five_not_mem_one) x x rfl,
          ← graphFamilyE6_of_d4 (J := ⟨{1}, card_singleton_le_two_E6 1⟩)
            (Finset.mem_singleton_self _) zero_not_mem_one five_not_mem_one x]
        exact hmem ⟨{1}, card_singleton_le_two_E6 1⟩ x
      · have hiA : ({i} : Finset (Fin (Tag.rank .E6))) ⊆ e6A3Nodes :=
          Finset.singleton_subset_iff.2 (mem_e6A3Nodes_of_mem_e6D4Nodes hi hi1)
        have hi1' : (1 : Fin (Tag.rank .E6)) ∉ ({i} : Finset (Fin (Tag.rank .E6))) := by
          rw [Finset.mem_singleton]
          exact fun h => hi1 h.symm
        have hxA : (x : e6Data_valid.minGroup K) ∈ e6ScLevi K e6A3Nodes :=
          CFSG.LieType.CurtisTits.levi_mono _ hiA x.2
        rw [scLeviRestrict_eq_of_coe_eq ΦD _ e6A3Nodes_subset_e6D4Nodes x ⟨x, hxA⟩ rfl,
          ← hagree, scLeviRestrict_eq_of_coe_eq ΦA e6A3Nodes_subset_e6A5Nodes
            (subset_e6A5Nodes_of_one_not_mem hi1') ⟨x, hxA⟩ x rfl,
          ← graphFamilyE6_of_one_not_mem (J := ⟨{i}, card_singleton_le_two_E6 i⟩) hi1' x]
        exact hmem ⟨{i}, card_singleton_le_two_E6 i⟩ x

end Family

section Main

variable {K : Type} [Field K] {G : Type} [Group G]
  {ΦA : e6ScLevi K e6A5Nodes →* G} {ΦD : e6ScLevi K e6D4Nodes →* G}
  {hc0 : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of zero_cases_end) b)}
  {hc5 : ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of five_cases_end) b)}

theorem conj_graphFamilyE6 {t : G}
    (hconjA : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hconjD : ∀ x y : e6ScLevi K e6D4Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦD x * t⁻¹ = ΦD y)
    (i : Fin (Tag.rank .E6)) (x : e6ScLevi K {i}) (y : e6ScLevi K {rhoPerm i})
    (hxy : (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x) :
    t * graphFamilyE6 ΦA ΦD hc0 hc5 ⟨{i}, card_singleton_le_two_E6 i⟩ x * t⁻¹ =
      graphFamilyE6 ΦA ΦD hc0 hc5 ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩ y := by
  by_cases hi : i = 1
  · subst hi
    have h1 : (1 : Fin (Tag.rank .E6)) ∈ ({rhoPerm 1} : Finset (Fin (Tag.rank .E6))) := by
      rw [e6RhoPerm_one]
      exact Finset.mem_singleton_self _
    have h0 : (0 : Fin (Tag.rank .E6)) ∉ ({rhoPerm 1} : Finset (Fin (Tag.rank .E6))) := by
      rw [e6RhoPerm_one]
      exact zero_not_mem_one
    have h5 : (5 : Fin (Tag.rank .E6)) ∉ ({rhoPerm 1} : Finset (Fin (Tag.rank .E6))) := by
      rw [e6RhoPerm_one]
      exact five_not_mem_one
    rw [graphFamilyE6_of_d4 (J := ⟨{1}, card_singleton_le_two_E6 1⟩)
      (Finset.mem_singleton_self _) zero_not_mem_one five_not_mem_one x,
      graphFamilyE6_of_d4 (J := ⟨{rhoPerm 1}, card_singleton_le_two_E6 (rhoPerm 1)⟩) h1 h0 h5 y,
      scLeviRestrict_apply, scLeviRestrict_apply]
    exact hconjD _ _ hxy
  · have h1 : (1 : Fin (Tag.rank .E6)) ∉ ({i} : Finset (Fin (Tag.rank .E6))) := by
      rw [Finset.mem_singleton]
      exact fun h => hi h.symm
    have h1' : (1 : Fin (Tag.rank .E6)) ∉ ({rhoPerm i} : Finset (Fin (Tag.rank .E6))) := by
      rw [Finset.mem_singleton]
      exact fun h => rhoPerm_ne_one hi h.symm
    rw [graphFamilyE6_of_one_not_mem (J := ⟨{i}, card_singleton_le_two_E6 i⟩) h1 x,
      graphFamilyE6_of_one_not_mem (J := ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩) h1' y,
      scLeviRestrict_apply, scLeviRestrict_apply]
    exact hconjA _ _ hxy

theorem isE6GraphRowFamily_graphFamilyE6 {L : Subgroup G} {F : Type} [Field F]
    {e : L ≃* adjointGroup .F4 F} {t : G}
    (hagree : ∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
      scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes x)
    (hconjA : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hconjD : ∀ x y : e6ScLevi K e6D4Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦD x * t⁻¹ = ΦD y)
    (hrange : ΦA.range ⊔ ΦD.range = pieceSpan e) :
    IsE6GraphRowFamily e t K (graphFamilyE6 ΦA ΦD hc0 hc5) where
  compatible := isCompatible_graphFamilyE6 hagree
  iSup_range := (iSup_range_graphFamilyE6 hagree).trans hrange
  conj := conj_graphFamilyE6 hconjA hconjD

end Main

section Twist

variable {K : Type} [Field K] {G : Type} [Group G]

theorem sigma_mem_e6ScLevi {S : Finset (Fin (Tag.rank .E6))} (hS : ∀ i ∈ S, rhoPerm i ∈ S)
    {x : e6Data_valid.minGroup K} (hx : x ∈ e6ScLevi K S) :
    sigma K (RingHom.id K) x ∈ e6ScLevi K S := by
  have hle : e6ScLevi K S ≤ (e6ScLevi K S).comap (sigma K (RingHom.id K)) := by
    show (⨆ j ∈ S, CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup j) ≤ _
    refine iSup₂_le fun i hi y hy => ?_
    rw [Subgroup.mem_comap]
    exact CFSG.LieType.CurtisTits.rankOne_le_levi _ (hS i hi)
      (CFSG.LieType.Steinberg.TwistedE6.sigma_mem_rankOne (RingHom.id K) hy)
  exact hle hx

@[expose] noncomputable def sigmaScLevi {S : Finset (Fin (Tag.rank .E6))}
    (hS : ∀ i ∈ S, rhoPerm i ∈ S) : e6ScLevi K S →* e6ScLevi K S :=
  ((sigma K (RingHom.id K)).comp (e6ScLevi K S).subtype).codRestrict (e6ScLevi K S)
    fun x => sigma_mem_e6ScLevi hS x.2

theorem coe_sigmaScLevi {S : Finset (Fin (Tag.rank .E6))} (hS : ∀ i ∈ S, rhoPerm i ∈ S)
    (x : e6ScLevi K S) :
    ((sigmaScLevi hS x : e6ScLevi K S) : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x :=
  rfl

theorem sigmaScLevi_sigmaScLevi {S : Finset (Fin (Tag.rank .E6))} (hS : ∀ i ∈ S, rhoPerm i ∈ S)
    (x : e6ScLevi K S) : sigmaScLevi hS (sigmaScLevi hS x) = x :=
  Subtype.ext (CFSG.LieType.Steinberg.TwistedE6.sigma_sigma (RingHom.id K) (fun _ => rfl) x)

theorem exists_agree_of_agree_or_twist {ΦA : e6ScLevi K e6A5Nodes →* G}
    {ΦD : e6ScLevi K e6D4Nodes →* G} {t : G}
    (htw : (∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
        scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes x) ∨
      (∀ x y : e6ScLevi K e6A3Nodes, (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
        scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
          scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes y))
    (hconjD : ∀ x y : e6ScLevi K e6D4Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦD x * t⁻¹ = ΦD y)
    (hc : ∀ j, (hj : j = 0 ∨ j = 5) → ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b)) :
    ∃ ΦD' : e6ScLevi K e6D4Nodes →* G,
      (∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
        scLeviRestrict ΦD' e6A3Nodes_subset_e6D4Nodes x) ∧
      (∀ x y : e6ScLevi K e6D4Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦD' x * t⁻¹ = ΦD' y) ∧
      ΦD'.range = ΦD.range ∧
      (∀ j, (hj : j = 0 ∨ j = 5) → ∀ a b, Commute (scLeviRestrict ΦD' one_subset_e6D4Nodes a)
        (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b)) := by
  rcases htw with h | h
  · exact ⟨ΦD, h, hconjD, rfl, hc⟩
  set τ := sigmaScLevi (K := K) rhoPerm_mem_e6D4Nodes' with hτ
  have hτ1 : ∀ a : e6ScLevi K {1}, ((τ ⟨a, CFSG.LieType.CurtisTits.levi_mono _
      one_subset_e6D4Nodes a.2⟩ : e6ScLevi K e6D4Nodes) : e6Data_valid.minGroup K) ∈
      e6ScLevi K {1} := fun a => by
    rw [coe_sigmaScLevi]
    have := sigma_mem_e6ScLevi (K := K) (S := {1}) (fun i hi => by
      rw [Finset.mem_singleton] at hi ⊢
      rw [hi, e6RhoPerm_one]) a.2
    exact this
  refine ⟨ΦD.comp τ, fun x => ?_, fun x y hxy => ?_, ?_, fun j hj a b => ?_⟩
  · rw [scLeviRestrict_apply, scLeviRestrict_apply, MonoidHom.comp_apply]
    have hσx : sigma K (RingHom.id K) (x : e6Data_valid.minGroup K) ∈ e6ScLevi K e6A3Nodes :=
      sigma_mem_e6ScLevi (fun i hi => by revert i; decide) x.2
    have := h x ⟨_, hσx⟩ rfl
    rw [scLeviRestrict_apply, scLeviRestrict_apply] at this
    rw [this]
    congr 1
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    refine hconjD _ _ ?_
    rw [coe_sigmaScLevi, coe_sigmaScLevi, hxy]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 fun x => ⟨τ x, sigmaScLevi_sigmaScLevi _ x⟩,
      ← MonoidHom.range_eq_map]
  · rw [scLeviRestrict_apply, MonoidHom.comp_apply]
    have := hc j hj ⟨_, hτ1 a⟩ b
    rw [scLeviRestrict_apply] at this
    exact this

end Twist

section Param

variable {G : Type} [Group G] {L : Subgroup G} {F : Type} [Field F] {K : Type} [Field K]

structure IsE6GraphRowParam (e : L ≃* adjointGroup .F4 F) (t : G)
    (ΦA : e6ScLevi K e6A5Nodes →* G) (ΦD : e6ScLevi K e6D4Nodes →* G) : Prop where
  agree_or_twist : (∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
      scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes x) ∨
    (∀ x y : e6ScLevi K e6A3Nodes, (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
      scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
        scLeviRestrict ΦD e6A3Nodes_subset_e6D4Nodes y)
  conjA : ∀ x y : e6ScLevi K e6A5Nodes,
    (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y
  conjD : ∀ x y : e6ScLevi K e6D4Nodes,
    (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦD x * t⁻¹ = ΦD y
  comm : ∀ j, (hj : j = 0 ∨ j = 5) → ∀ a b, Commute (scLeviRestrict ΦD one_subset_e6D4Nodes a)
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b)
  range_sup : ΦA.range ⊔ ΦD.range = pieceSpan e

theorem IsE6GraphRowParam.exists_isE6GraphRowFamily {e : L ≃* adjointGroup .F4 F} {t : G}
    {ΦA : e6ScLevi K e6A5Nodes →* G} {ΦD : e6ScLevi K e6D4Nodes →* G}
    (h : IsE6GraphRowParam e t ΦA ΦD) :
    ∃ φ : ∀ J, (e6Datum K).leviAmalgam J →* G, IsE6GraphRowFamily e t K φ := by
  obtain ⟨ΦD', hagree, hconjD', hrange', hc'⟩ :=
    exists_agree_of_agree_or_twist h.agree_or_twist h.conjD h.comm
  exact ⟨graphFamilyE6 ΦA ΦD' (hc' 0 zero_cases_end) (hc' 5 five_cases_end),
    isE6GraphRowFamily_graphFamilyE6 hagree h.conjA hconjD' (by rw [hrange']; exact h.range_sup)⟩

@[expose] def E6GraphRowParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∃ (ΦA : e6ScLevi K e6A5Nodes →* G) (ΦD : e6ScLevi K e6D4Nodes →* G),
      IsE6GraphRowParam e t ΦA ΦD

theorem e6GraphRowFamilyInput_of_paramInput (h : E6GraphRowParamInput) :
    E6GraphRowFamilyInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk
  obtain ⟨ΦA, ΦD, hp⟩ := h G L K e t f hw hf hk
  exact hp.exists_isE6GraphRowFamily

end Param

section Reduction

theorem e6RowCTQuotInput_of_paramInput (h : E6GraphRowParamInput) : E6RowCTQuotInput :=
  e6RowCTQuotInput_of_familyInput (e6GraphRowFamilyInput_of_paramInput h)

end Reduction

end CFSG.SeitzReduction.F4Pilot
