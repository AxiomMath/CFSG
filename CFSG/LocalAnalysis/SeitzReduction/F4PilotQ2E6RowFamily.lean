module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowCT
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphFamily

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm)

local instance f4PilotQ2E6RowFamilyNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def e6TwoA2Nodes : Finset (Fin (Tag.rank .E6)) := {1, 3}

theorem orth_cases_E6 {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3) :
    j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5 := by
  revert j
  decide

theorem singleton_subset_e6A5Nodes_of_orth {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3) :
    ({j} : Finset (Fin (Tag.rank .E6))) ⊆ e6A5Nodes := by
  rcases orth_cases_E6 hj with rfl | rfl | rfl | rfl <;> decide

theorem one_subset_e6TwoA2Nodes : ({1} : Finset (Fin (Tag.rank .E6))) ⊆ e6TwoA2Nodes := by
  decide

theorem three_subset_e6TwoA2Nodes : ({3} : Finset (Fin (Tag.rank .E6))) ⊆ e6TwoA2Nodes := by
  decide

theorem three_subset_e6A5Nodes : ({3} : Finset (Fin (Tag.rank .E6))) ⊆ e6A5Nodes := by
  decide

theorem subset_e6TwoA2Nodes_of_not_exists {J : Finset (Fin (Tag.rank .E6))}
    (h : ¬ ∃ j ∈ J, j ≠ 1 ∧ j ≠ 3) : J ⊆ e6TwoA2Nodes := by
  intro a ha
  have key : ∀ b : Fin (Tag.rank .E6), ¬ (b ≠ 1 ∧ b ≠ 3) → b ∈ e6TwoA2Nodes := by decide
  exact key a fun hb => h ⟨a, ha, hb⟩

theorem subset_three_of_subset_e6TwoA2Nodes {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ e6TwoA2Nodes) (h1 : (1 : Fin (Tag.rank .E6)) ∉ J) :
    J ⊆ {3} := by
  intro a ha
  have key : ∀ b : Fin (Tag.rank .E6), b ∈ e6TwoA2Nodes → b ≠ 1 → b ∈ ({3} : Finset _) := by
    decide
  exact key a (hJ ha) fun h => h1 (h ▸ ha)

theorem eq_three_of_mem_e6TwoA2Nodes {i : Fin (Tag.rank .E6)} (hi : i ∈ e6TwoA2Nodes)
    (hi1 : i ≠ 1) : i = 3 := by
  revert i
  decide

@[expose] noncomputable def orthNodeE6 {J : Finset (Fin (Tag.rank .E6))}
    (h : ∃ j ∈ J, j ≠ 1 ∧ j ≠ 3) : Fin (Tag.rank .E6) :=
  Classical.choose h

theorem orthNodeE6_mem {J : Finset (Fin (Tag.rank .E6))} (h : ∃ j ∈ J, j ≠ 1 ∧ j ≠ 3) :
    orthNodeE6 h ∈ J :=
  (Classical.choose_spec h).1

theorem orthNodeE6_spec {J : Finset (Fin (Tag.rank .E6))} (h : ∃ j ∈ J, j ≠ 1 ∧ j ≠ 3) :
    orthNodeE6 h ≠ 1 ∧ orthNodeE6 h ≠ 3 :=
  (Classical.choose_spec h).2

theorem e6_root_support_one_zero_check :
    ∀ γ ∈ rootFinset .E6, γ 2 = 0 → γ 3 = 0 → γ 4 = 0 → γ 5 = 0 → γ 1 = 0 ∨ γ 0 = 0 := by
  decide +kernel

theorem e6_root_support_one_two_check :
    ∀ γ ∈ rootFinset .E6, γ 0 = 0 → γ 3 = 0 → γ 4 = 0 → γ 5 = 0 → γ 1 = 0 ∨ γ 2 = 0 := by
  decide +kernel

theorem e6_root_support_one_four_check :
    ∀ γ ∈ rootFinset .E6, γ 0 = 0 → γ 2 = 0 → γ 3 = 0 → γ 5 = 0 → γ 1 = 0 ∨ γ 4 = 0 := by
  decide +kernel

theorem e6_root_support_one_five_check :
    ∀ γ ∈ rootFinset .E6, γ 0 = 0 → γ 2 = 0 → γ 3 = 0 → γ 4 = 0 → γ 1 = 0 ∨ γ 5 = 0 := by
  decide +kernel

section Pair

variable {K : Type} [Field K]

theorem commute_scRootGroup_one_orth {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3)
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
    rcases orth_cases_E6 hj with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl <;>
      rcases ht with rfl | rfl <;> simp +decide at h1 hjj <;> exact ⟨h1, hjj⟩
  · intro a b ha hb hmem
    rw [hroot, ← mem_rootFinset] at hmem
    rcases orth_cases_E6 hj with rfl | rfl | rfl | rfl
    · have h := e6_root_support_one_zero_check _ hmem
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp +decide at h <;> omega
    · have h := e6_root_support_one_two_check _ hmem
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp +decide at h <;> omega
    · have h := e6_root_support_one_four_check _ hmem
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp +decide at h <;> omega
    · have h := e6_root_support_one_five_check _ hmem
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp +decide at h <;> omega

theorem commute_scLevi_one_orth {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3) :
    ∀ x ∈ e6ScLevi K {1}, ∀ y ∈ e6ScLevi K {j}, Commute x y := by
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton,
    CFSG.LieType.CurtisTits.rankOne, CFSG.LieType.CurtisTits.rankOne]
  refine forall_commute_sup_left (forall_commute_sup_right ?_ ?_)
    (forall_commute_sup_right ?_ ?_)
  · exact fun x hx y hy => commute_scRootGroup_one_orth hj (Or.inl rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one_orth hj (Or.inl rfl) (Or.inr rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one_orth hj (Or.inr rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one_orth hj (Or.inr rfl) (Or.inr rfl) hx hy

theorem scLevi_one_inf_orth_eq_bot {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3) :
    e6ScLevi K {1} ⊓ e6ScLevi K {j} = ⊥ := by
  have hc := commute_scLevi_one_orth (K := K) hj
  dsimp only [e6ScLevi] at hc ⊢
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton] at hc ⊢
  exact rankOne_inf_rankOne_eq_bot (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K)
    (fun h => hj.1 h.symm) hc

theorem scLevi_le_pair_orth {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3) (h1 : (1 : Fin (Tag.rank .E6)) ∈ J)
    (hjJ : j ∈ J) :
    e6ScLevi K J ≤ e6ScLevi K {1} ⊔ e6ScLevi K {j} := by
  dsimp only [e6ScLevi]
  rw [E6Pilot.eq_pair_of_card_le_two hJ (fun h => hj.1 h.symm) h1 hjJ, levi_pair]

end Pair

section Family

variable {K : Type} [Field K] {G : Type} [Group G]

variable (ΦA : e6ScLevi K e6A5Nodes →* G) (ΦB : e6ScLevi K e6TwoA2Nodes →* G)

@[expose] noncomputable def twoPairLiftE6 {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3)
    (hc : ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b)) :
    ↥(e6ScLevi K {1} ⊔ e6ScLevi K {j}) →* G :=
  supLift (commute_scLevi_one_orth hj) (scLevi_one_inf_orth_eq_bot hj) _ _ hc

theorem twoPairLiftE6_of_mem_left {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3)
    (hc : ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b))
    (z : ↥(e6ScLevi K {1} ⊔ e6ScLevi K {j}))
    (hz : (z : e6Data_valid.minGroup K) ∈ e6ScLevi K {1}) :
    twoPairLiftE6 ΦA ΦB hj hc z = scLeviRestrict ΦB one_subset_e6TwoA2Nodes ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_left (commute_scLevi_one_orth hj) (scLevi_one_inf_orth_eq_bot hj) hc
    ⟨z, hz⟩

theorem twoPairLiftE6_of_mem_right {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3)
    (hc : ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b))
    (z : ↥(e6ScLevi K {1} ⊔ e6ScLevi K {j}))
    (hz : (z : e6Data_valid.minGroup K) ∈ e6ScLevi K {j}) :
    twoPairLiftE6 ΦA ΦB hj hc z =
      scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_right (commute_scLevi_one_orth hj) (scLevi_one_inf_orth_eq_bot hj) hc
    ⟨z, hz⟩

theorem range_twoPairLiftE6 {j : Fin (Tag.rank .E6)} (hj : j ≠ 1 ∧ j ≠ 3)
    (hc : ∀ a b, Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b)) :
    (twoPairLiftE6 ΦA ΦB hj hc).range ≤ ΦA.range ⊔ ΦB.range := by
  rw [twoPairLiftE6, range_supLift]
  refine sup_le (le_sup_of_le_right ?_) (le_sup_of_le_left ?_) <;>
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩

variable (hc : ∀ (j : Fin (Tag.rank .E6)) (hj : j ≠ 1 ∧ j ≠ 3) (a b),
    Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b))

@[expose] noncomputable def twoGraphFamilyE6
    (J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}) :
    (e6Datum K).leviAmalgam J →* G :=
  if h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1 then
    if hj : ∃ j ∈ J.1, j ≠ 1 ∧ j ≠ 3 then
      (twoPairLiftE6 ΦA ΦB (orthNodeE6_spec hj) (hc _ (orthNodeE6_spec hj))).comp
        (Subgroup.inclusion (scLevi_le_pair_orth J.2 (orthNodeE6_spec hj) h1 (orthNodeE6_mem hj)))
    else scLeviRestrict ΦB (subset_e6TwoA2Nodes_of_not_exists hj)
  else scLeviRestrict ΦA (subset_e6A5Nodes_of_one_not_mem h1)

variable {ΦA ΦB hc}

theorem twoGraphFamilyE6_of_one_not_mem {J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J.1) (x : (e6Datum K).leviAmalgam J) :
    twoGraphFamilyE6 ΦA ΦB hc J x =
      scLeviRestrict ΦA (subset_e6A5Nodes_of_one_not_mem h1) x := by
  rw [twoGraphFamilyE6, dite_eq_right h1]

theorem twoGraphFamilyE6_of_a2 {J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (hj : ¬ ∃ j ∈ J.1, j ≠ 1 ∧ j ≠ 3)
    (x : (e6Datum K).leviAmalgam J) :
    twoGraphFamilyE6 ΦA ΦB hc J x =
      scLeviRestrict ΦB (subset_e6TwoA2Nodes_of_not_exists hj) x := by
  rw [twoGraphFamilyE6, dite_eq_left h1, dite_eq_right hj]

theorem twoGraphFamilyE6_of_pair {J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (hj : ∃ j ∈ J.1, j ≠ 1 ∧ j ≠ 3)
    (x : (e6Datum K).leviAmalgam J) :
    twoGraphFamilyE6 ΦA ΦB hc J x =
      twoPairLiftE6 ΦA ΦB (orthNodeE6_spec hj) (hc _ (orthNodeE6_spec hj))
        ⟨x, scLevi_le_pair_orth J.2 (orthNodeE6_spec hj) h1 (orthNodeE6_mem hj) x.2⟩ := by
  rw [twoGraphFamilyE6, dite_eq_left h1, dite_eq_left hj]
  rfl

theorem isCompatible_twoGraphFamilyE6
    (hagree : ∀ x : e6ScLevi K {3}, scLeviRestrict ΦA three_subset_e6A5Nodes x =
      scLeviRestrict ΦB three_subset_e6TwoA2Nodes x) :
    IsCompatible (e6Datum K).leviAmalgam (twoGraphFamilyE6 ΦA ΦB hc) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ j.1 := hij
  have hmono : ∀ {I : Finset (Fin (Tag.rank .E6))}, (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ I →
      (y : e6Data_valid.minGroup K) ∈ e6ScLevi K I :=
    fun h => hxy ▸ CFSG.LieType.CurtisTits.levi_mono _ h x.2
  by_cases h1j : (1 : Fin (Tag.rank .E6)) ∈ j.1
  · by_cases hpj : ∃ k ∈ j.1, k ≠ 1 ∧ k ≠ 3
    ·
      have hkspec := orthNodeE6_spec hpj
      have hjeq : (j.1 : Finset (Fin (Tag.rank .E6))) = {1, orthNodeE6 hpj} :=
        E6Pilot.eq_pair_of_card_le_two j.2 (fun h => hkspec.1 h.symm) h1j (orthNodeE6_mem hpj)
      have hij' : ∀ a ∈ i.1, a = 1 ∨ a = orthNodeE6 hpj := fun a ha => by
        have := hsub ha
        rw [hjeq, Finset.mem_insert, Finset.mem_singleton] at this
        exact this
      rw [twoGraphFamilyE6_of_pair h1j hpj]
      by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
      · by_cases hpi : ∃ k ∈ i.1, k ≠ 1 ∧ k ≠ 3
        ·
          have hki : orthNodeE6 hpj ∈ i.1 := by
            obtain ⟨k', hk'i, hk'⟩ := hpi
            rcases hij' k' hk'i with h | h
            · exact absurd h hk'.1
            · exact h ▸ hk'i
          have hieq : i = j := Subtype.ext (by
            rw [hjeq]
            exact E6Pilot.eq_pair_of_card_le_two i.2 (fun h => hkspec.1 h.symm) h1i hki)
          subst hieq
          rw [twoGraphFamilyE6_of_pair h1i hpi]
          exact congrArg _ (Subtype.ext hxy)
        ·
          have hi1 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {1} := fun a ha => by
            rcases hij' a ha with h | h
            · exact h ▸ Finset.mem_singleton_self _
            · exact absurd ⟨a, ha, h ▸ hkspec⟩ hpi
          rw [twoGraphFamilyE6_of_a2 h1i hpi, twoPairLiftE6_of_mem_left ΦA ΦB (orthNodeE6_spec hpj)
            (hc _ (orthNodeE6_spec hpj)) _ (hmono hi1)]
          exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
      ·
        have hik : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {orthNodeE6 hpj} := fun a ha => by
          rcases hij' a ha with h | h
          · exact absurd (h ▸ ha) h1i
          · exact h ▸ Finset.mem_singleton_self _
        rw [twoGraphFamilyE6_of_one_not_mem h1i, twoPairLiftE6_of_mem_right ΦA ΦB
          (orthNodeE6_spec hpj) (hc _ (orthNodeE6_spec hpj)) _ (hmono hik)]
        exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
    ·
      have hpi : ¬ ∃ k ∈ i.1, k ≠ 1 ∧ k ≠ 3 := fun ⟨k, hk, hk'⟩ => hpj ⟨k, hsub hk, hk'⟩
      rw [twoGraphFamilyE6_of_a2 h1j hpj]
      by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
      · rw [twoGraphFamilyE6_of_a2 h1i hpi]
        exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
      · rw [twoGraphFamilyE6_of_one_not_mem h1i]
        have hi3 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {3} :=
          subset_three_of_subset_e6TwoA2Nodes (subset_e6TwoA2Nodes_of_not_exists hpi) h1i
        have hx3 : (x : e6Data_valid.minGroup K) ∈ e6ScLevi K {3} :=
          CFSG.LieType.CurtisTits.levi_mono _ hi3 x.2
        rw [scLeviRestrict_eq_of_coe_eq ΦA _ three_subset_e6A5Nodes x ⟨x, hx3⟩ rfl,
          hagree, scLeviRestrict_eq_of_coe_eq ΦB three_subset_e6TwoA2Nodes _ ⟨x, hx3⟩ y hxy]
  · have h1i : (1 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h1j (hsub h)
    rw [twoGraphFamilyE6_of_one_not_mem h1i, twoGraphFamilyE6_of_one_not_mem h1j]
    exact scLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy

theorem iSup_range_twoGraphFamilyE6
    (hagree : ∀ x : e6ScLevi K {3}, scLeviRestrict ΦA three_subset_e6A5Nodes x =
      scLeviRestrict ΦB three_subset_e6TwoA2Nodes x) :
    ⨆ J, (twoGraphFamilyE6 ΦA ΦB hc J).range = ΦA.range ⊔ ΦB.range := by
  have hmem : ∀ (J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2})
      (x : (e6Datum K).leviAmalgam J),
      twoGraphFamilyE6 ΦA ΦB hc J x ∈ ⨆ J, (twoGraphFamilyE6 ΦA ΦB hc J).range :=
    fun J x => le_iSup (fun J => (twoGraphFamilyE6 ΦA ΦB hc J).range) J ⟨x, rfl⟩
  apply le_antisymm
  · refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1
    · by_cases hp : ∃ k ∈ J.1, k ≠ 1 ∧ k ≠ 3
      · rw [twoGraphFamilyE6_of_pair h1 hp]
        exact range_twoPairLiftE6 ΦA ΦB (orthNodeE6_spec hp) (hc _ (orthNodeE6_spec hp))
          ⟨_, rfl⟩
      · rw [twoGraphFamilyE6_of_a2 h1 hp]
        exact mem_sup_right ⟨_, rfl⟩
    · rw [twoGraphFamilyE6_of_one_not_mem h1]
      exact mem_sup_left ⟨_, rfl⟩
  · refine sup_le ?_ ?_
    · refine range_le_of_forall_scLevi_singleton ΦA fun i hi x => ?_
      have hi1 : (1 : Fin (Tag.rank .E6)) ∉ ({i} : Finset (Fin (Tag.rank .E6))) := by
        rw [Finset.mem_singleton]
        exact fun h => ne_one_of_mem_e6A5Nodes hi h.symm
      rw [scLeviRestrict_eq_of_coe_eq ΦA _ (subset_e6A5Nodes_of_one_not_mem hi1) x x rfl,
        ← twoGraphFamilyE6_of_one_not_mem (J := ⟨{i}, card_singleton_le_two_E6 i⟩) hi1 x]
      exact hmem ⟨{i}, card_singleton_le_two_E6 i⟩ x
    · refine range_le_of_forall_scLevi_singleton ΦB fun i hi x => ?_
      by_cases hi1 : i = 1
      · subst hi1
        have hp : ¬ ∃ k ∈ ({1} : Finset (Fin (Tag.rank .E6))), k ≠ 1 ∧ k ≠ 3 := by decide
        rw [scLeviRestrict_eq_of_coe_eq ΦB _ (subset_e6TwoA2Nodes_of_not_exists hp) x x rfl,
          ← twoGraphFamilyE6_of_a2 (J := ⟨{1}, card_singleton_le_two_E6 1⟩)
            (Finset.mem_singleton_self _) hp x]
        exact hmem ⟨{1}, card_singleton_le_two_E6 1⟩ x
      · have hi3 := eq_three_of_mem_e6TwoA2Nodes hi hi1
        subst hi3
        have h1 : (1 : Fin (Tag.rank .E6)) ∉ ({3} : Finset (Fin (Tag.rank .E6))) := by decide
        rw [scLeviRestrict_eq_of_coe_eq ΦB _ three_subset_e6TwoA2Nodes x x rfl, ← hagree,
          scLeviRestrict_eq_of_coe_eq ΦA three_subset_e6A5Nodes
            (subset_e6A5Nodes_of_one_not_mem h1) x x rfl,
          ← twoGraphFamilyE6_of_one_not_mem (J := ⟨{3}, card_singleton_le_two_E6 3⟩) h1 x]
        exact hmem ⟨{3}, card_singleton_le_two_E6 3⟩ x

end Family

section Main

variable {K : Type} [Field K] {G : Type} [Group G]
  {ΦA : e6ScLevi K e6A5Nodes →* G} {ΦB : e6ScLevi K e6TwoA2Nodes →* G}
  {hc : ∀ (j : Fin (Tag.rank .E6)) (hj : j ≠ 1 ∧ j ≠ 3) (a b),
    Commute (scLeviRestrict ΦB one_subset_e6TwoA2Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth hj) b)}

theorem conj_twoGraphFamilyE6 {t : G}
    (hconjA : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hconjB : ∀ x y : e6ScLevi K e6TwoA2Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦB x * t⁻¹ = ΦB y)
    (i : Fin (Tag.rank .E6)) (x : e6ScLevi K {i}) (y : e6ScLevi K {rhoPerm i})
    (hxy : (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x) :
    t * twoGraphFamilyE6 ΦA ΦB hc ⟨{i}, card_singleton_le_two_E6 i⟩ x * t⁻¹ =
      twoGraphFamilyE6 ΦA ΦB hc ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩ y := by
  by_cases hi : i = 1
  · subst hi
    have h1 : (1 : Fin (Tag.rank .E6)) ∈ ({rhoPerm 1} : Finset (Fin (Tag.rank .E6))) := by
      rw [e6RhoPerm_one]
      exact Finset.mem_singleton_self _
    have hp : ¬ ∃ k ∈ ({1} : Finset (Fin (Tag.rank .E6))), k ≠ 1 ∧ k ≠ 3 := by decide
    have hp' : ¬ ∃ k ∈ ({rhoPerm 1} : Finset (Fin (Tag.rank .E6))), k ≠ 1 ∧ k ≠ 3 := by
      rw [e6RhoPerm_one]
      exact hp
    rw [twoGraphFamilyE6_of_a2 (J := ⟨{1}, card_singleton_le_two_E6 1⟩)
      (Finset.mem_singleton_self _) hp x,
      twoGraphFamilyE6_of_a2 (J := ⟨{rhoPerm 1}, card_singleton_le_two_E6 (rhoPerm 1)⟩) h1 hp' y,
      scLeviRestrict_apply, scLeviRestrict_apply]
    exact hconjB _ _ hxy
  · have h1 : (1 : Fin (Tag.rank .E6)) ∉ ({i} : Finset (Fin (Tag.rank .E6))) := by
      rw [Finset.mem_singleton]
      exact fun h => hi h.symm
    have h1' : (1 : Fin (Tag.rank .E6)) ∉ ({rhoPerm i} : Finset (Fin (Tag.rank .E6))) := by
      rw [Finset.mem_singleton]
      exact fun h => rhoPerm_ne_one hi h.symm
    rw [twoGraphFamilyE6_of_one_not_mem (J := ⟨{i}, card_singleton_le_two_E6 i⟩) h1 x,
      twoGraphFamilyE6_of_one_not_mem (J := ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩)
        h1' y, scLeviRestrict_apply, scLeviRestrict_apply]
    exact hconjA _ _ hxy

theorem isTwoE6GraphFamily_twoGraphFamilyE6 {t : G} {G₀ : Subgroup G}
    (hagree : ∀ x : e6ScLevi K {3}, scLeviRestrict ΦA three_subset_e6A5Nodes x =
      scLeviRestrict ΦB three_subset_e6TwoA2Nodes x)
    (hconjA : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hconjB : ∀ x y : e6ScLevi K e6TwoA2Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦB x * t⁻¹ = ΦB y)
    (hrange : ΦA.range ⊔ ΦB.range = G₀) :
    IsTwoE6GraphFamily G₀ t K (twoGraphFamilyE6 ΦA ΦB hc) where
  compatible := isCompatible_twoGraphFamilyE6 hagree
  iSup_range := (iSup_range_twoGraphFamilyE6 hagree).trans hrange
  conj := conj_twoGraphFamilyE6 hconjA hconjB

end Main

end CFSG.SeitzReduction.F4Pilot
