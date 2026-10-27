module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldTwist
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)

local instance e6PilotCTFieldFamilyNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem e6_root_support_one_four_five_check :
    ∀ γ ∈ rootFinset .E6, γ 0 = 0 → γ 2 = 0 → γ 3 = 0 →
      (γ 5 = 0 → γ 1 = 0 ∨ γ 4 = 0) ∧ (γ 4 = 0 → γ 1 = 0 ∨ γ 5 = 0) := by
  decide +kernel

theorem toWeight_pair_check :
    MinData.toWeight (τ := .E6) (Pi.single 1 1) 1 = 2 ∧ MinData.toWeight (τ := .E6) (Pi.single 1 1) 4 = 0 ∧
      MinData.toWeight (τ := .E6) (Pi.single 1 1) 5 = 0 ∧ MinData.toWeight (τ := .E6) (Pi.single 4 1) 4 = 2 ∧
      MinData.toWeight (τ := .E6) (Pi.single 4 1) 1 = 0 ∧ MinData.toWeight (τ := .E6) (Pi.single 5 1) 5 = 2 ∧
      MinData.toWeight (τ := .E6) (Pi.single 5 1) 1 = 0 := by
  decide +kernel

section Pair

variable {K : Type} [Field K]

theorem commute_scRootGroup_one {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    {s t : Fin (Tag.rank .E6) → ℤ} (hs : s = Pi.single 1 1 ∨ s = -Pi.single 1 1)
    (ht : t = Pi.single j 1 ∨ t = -Pi.single j 1) {x y : e6Data_valid.minGroup K}
    (hx : x ∈ (e6Datum K).rootGroup s) (hy : y ∈ (e6Datum K).rootGroup t) : Commute x y := by
  have hroot : ∀ v, v ∈ (e6Datum K).roots ↔ IsRoot .E6 v := fun v =>
    e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 K
  refine F4Pilot.commute_of_forall_not_mem_roots (e6Datum_steinbergExtras K) ?_ ?_ ?_ ?_ hx hy
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
      simp at h1 hjj <;> exact ⟨h1, hjj⟩
  · intro a b ha hb hmem
    rw [hroot, ← mem_rootFinset] at hmem
    have h := e6_root_support_one_four_five_check _ hmem
    rcases hj with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp +decide at h <;> omega

theorem commute_scLevi_one {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) :
    ∀ x ∈ CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup {1},
      ∀ y ∈ CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup {j}, Commute x y := by
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton,
    CFSG.LieType.CurtisTits.rankOne, CFSG.LieType.CurtisTits.rankOne]
  refine F4Pilot.forall_commute_sup_left (F4Pilot.forall_commute_sup_right ?_ ?_)
    (F4Pilot.forall_commute_sup_right ?_ ?_)
  · exact fun x hx y hy => commute_scRootGroup_one hj (Or.inl rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one hj (Or.inl rfl) (Or.inr rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one hj (Or.inr rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_scRootGroup_one hj (Or.inr rfl) (Or.inr rfl) hx hy

end Pair

section AdPair

variable {K : Type} [Field K] [Finite K]

theorem commute_adLevi_one {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) :
    ∀ x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1},
      ∀ y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}, Commute x y := by
  intro x hx y hy
  rw [← map_e6Isogeny_levi] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact (commute_scLevi_one hj a ha b hb).map _

theorem adLevi_one_inf_eq_bot [CharP K 2] {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊓
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hz1, hzj⟩ := mem_inf.1 hz
  rw [← map_e6Isogeny_levi] at hz1 hzj
  obtain ⟨a, ha, rfl⟩ := hz1
  obtain ⟨b, hb, hab⟩ := hzj
  have hc : b⁻¹ * a ∈ center (e6Data_valid.minGroup K) := by
    rw [← ker_e6Isogeny_eq_center, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hcomm := commute_scLevi_one (K := K) hj
  have hcx : ∀ x, Commute (b⁻¹ * a) x := fun x => (mem_center_iff.1 hc x).symm
  have hax : ∀ x ∈ CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup {1}, Commute a x := by
    intro x hx
    have h1 : a = b * (b⁻¹ * a) := by group
    rw [h1]
    exact ((hcomm x hx b hb).symm).mul_left (hcx x)
  have ha1 : a ∈ CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup 1 := by
    rw [← CFSG.LieType.CurtisTits.levi_singleton]
    exact ha
  have hH := F4Pilot.mem_torus_of_mem_rankOne_of_commute (e6Datum_isCTGroupDatum K)
    (e6Datum_steinbergExtras K) ha1 fun x hx => hax x (by
      rw [CFSG.LieType.CurtisTits.levi_singleton]
      exact hx)
  obtain ⟨s, rfl⟩ := (e6Data_valid.mem_torus K).1 hH
  have hx1 : e6Data_valid.xm K (Pi.single 1 1) 1 ∈
      CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup {1} := by
    rw [CFSG.LieType.CurtisTits.levi_singleton]
    exact mem_sup_left (e6Data_valid.xm_mem_rootGroup K _ 1)
  have hconj := e6Data_valid.hm_conj_xm K (isRoot_single .E6 1) 1 s 1
  rw [toWeight_pair_check.1, (hax _ hx1).eq, mul_inv_cancel_right] at hconj
  have hs := e6Data_valid.xm_injective K (isRoot_single .E6 1) hconj
  have hs2 : (s : K) * (s : K) = 1 := by
    rw [mul_one, zpow_ofNat, Units.val_pow_eq_pow_val] at hs
    rw [← sq]
    exact hs.symm
  have hs1 : s = 1 := Units.ext (charTwo_eq_one_of_mul_self_eq_one hs2)
  rw [hs1, e6Data_valid.hm_one, map_one, mem_bot]

end AdPair

theorem exists_mul_eq_of_mem_sup_of_commute_E6 {M : Type*} [Group M] {A B : Subgroup M}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : M} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← F4Pilot.range_noncommCoprod_subtype hcomm] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem subset_nodes_high_of_one_not_mem {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J) : J ⊆ E6Neighbour.high.nodes :=
  fun _ hj => mem_nodes_high_of_ne fun h => h1 (h ▸ hj)

theorem subset_nodes_six_of_not_mem {J : Finset (Fin (Tag.rank .E6))}
    (h4 : (4 : Fin (Tag.rank .E6)) ∉ J) (h5 : (5 : Fin (Tag.rank .E6)) ∉ J) :
    J ⊆ E6Neighbour.six.nodes :=
  fun _ hj => mem_nodes_six_of_ne (fun h => h4 (h ▸ hj)) fun h => h5 (h ▸ hj)

theorem subset_a3Nodes_of_not_mem {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J) (h4 : (4 : Fin (Tag.rank .E6)) ∉ J)
    (h5 : (5 : Fin (Tag.rank .E6)) ∉ J) : J ⊆ {0, 2, 3} := by
  intro a ha
  have key : ∀ b : Fin (Tag.rank .E6), b ≠ 1 → b ≠ 4 → b ≠ 5 →
      b ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6))) := by decide
  exact key a (fun h => h1 (h ▸ ha)) (fun h => h4 (h ▸ ha)) fun h => h5 (h ▸ ha)

theorem one_subset_six : ({1} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.six.nodes := by
  decide

theorem one_subset_three : ({1} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.three.nodes := by
  decide

theorem singleton_subset_high_of {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) :
    ({j} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.high.nodes := by
  rcases hj with rfl | rfl <;> decide

theorem singleton_subset_three_of {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) :
    ({j} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.three.nodes := by
  rcases hj with rfl | rfl <;> decide

theorem one_ne_of {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) : (1 : Fin (Tag.rank .E6)) ≠ j := by
  rcases hj with rfl | rfl <;> decide

theorem four_cases : (4 : Fin (Tag.rank .E6)) = 4 ∨ (4 : Fin (Tag.rank .E6)) = 5 := Or.inl rfl

theorem five_ne_one_E6 : (5 : Fin (Tag.rank .E6)) ≠ 1 := by decide

theorem five_ne_four_E6 : (5 : Fin (Tag.rank .E6)) ≠ 4 := by decide

theorem five_cases : (5 : Fin (Tag.rank .E6)) = 4 ∨ (5 : Fin (Tag.rank .E6)) = 5 := Or.inr rfl

section Family

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

omit
  [Finite K] [CharP K 2] in
theorem adLevi_le_pair {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5) (h1 : (1 : Fin (Tag.rank .E6)) ∈ J)
    (hjJ : j ∈ J) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} := by
  rw [eq_pair_of_card_le_two hJ (one_ne_of hj) h1 hjJ, F4Pilot.levi_pair]

variable (hX : FieldNeighbourIso σ e .high) (hY : FieldNeighbourIso σ e .six)

@[expose] noncomputable def fieldPairLiftE6 {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    (hc : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
      (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) b)) :
    ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}) →* G :=
  F4Pilot.supLift (commute_adLevi_one hj) (adLevi_one_inf_eq_bot hj) _ _ hc

theorem fieldPairLiftE6_of_mem_left {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    (hc : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
      (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) b))
    (z : ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}))
    (hz : (z : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1}) :
    fieldPairLiftE6 hX hY hj hc z =
      hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact F4Pilot.supLift_apply_left (commute_adLevi_one hj) (adLevi_one_inf_eq_bot hj) hc ⟨z, hz⟩

theorem fieldPairLiftE6_of_mem_right {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    (hc : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
      (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) b))
    (z : ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}))
    (hz : (z : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}) :
    fieldPairLiftE6 hX hY hj hc z =
      hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact F4Pilot.supLift_apply_right (commute_adLevi_one hj) (adLevi_one_inf_eq_bot hj) hc ⟨z, hz⟩

variable (hc4 : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
    (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of four_cases)) b))
  (hc5 : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
    (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of five_cases)) b))

@[expose] noncomputable def fieldFamilyE6
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    (adjDatumE6 K).leviAmalgam J →* G :=
  if h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1 then
    if h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1 then
      (fieldPairLiftE6 hX hY four_cases hc4).comp
        (Subgroup.inclusion (adLevi_le_pair J.2 four_cases h1 h4))
    else if h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1 then
      (fieldPairLiftE6 hX hY five_cases hc5).comp
        (Subgroup.inclusion (adLevi_le_pair J.2 five_cases h1 h5))
    else hY.restrictTo (levi_le_neighbourLevi (K := K) (subset_nodes_six_of_not_mem h4 h5))
  else hX.restrictTo (levi_le_neighbourLevi (K := K) (subset_nodes_high_of_one_not_mem h1))

variable {hX hY hc4 hc5}

theorem fieldFamilyE6_of_one_not_mem {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J.1) (x : (adjDatumE6 K).leviAmalgam J) :
    fieldFamilyE6 hX hY hc4 hc5 J x =
      hX.restrictTo (levi_le_neighbourLevi (K := K) (subset_nodes_high_of_one_not_mem h1)) x := by
  rw [fieldFamilyE6, dite_eq_right h1]

theorem fieldFamilyE6_of_six {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h4 : (4 : Fin (Tag.rank .E6)) ∉ J.1)
    (h5 : (5 : Fin (Tag.rank .E6)) ∉ J.1) (x : (adjDatumE6 K).leviAmalgam J) :
    fieldFamilyE6 hX hY hc4 hc5 J x =
      hY.restrictTo (levi_le_neighbourLevi (K := K) (subset_nodes_six_of_not_mem h4 h5)) x := by
  rw [fieldFamilyE6, dite_eq_left h1, dite_eq_right h4, dite_eq_right h5]

theorem fieldFamilyE6_of_four {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1)
    (x : (adjDatumE6 K).leviAmalgam J) :
    fieldFamilyE6 hX hY hc4 hc5 J x =
      fieldPairLiftE6 hX hY four_cases hc4 ⟨x, adLevi_le_pair J.2 four_cases h1 h4 x.2⟩ := by
  rw [fieldFamilyE6, dite_eq_left h1, dite_eq_left h4]
  rfl

theorem fieldFamilyE6_of_five {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (h4 : (4 : Fin (Tag.rank .E6)) ∉ J.1)
    (h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1) (x : (adjDatumE6 K).leviAmalgam J) :
    fieldFamilyE6 hX hY hc4 hc5 J x =
      fieldPairLiftE6 hX hY five_cases hc5 ⟨x, adLevi_le_pair J.2 five_cases h1 h5 x.2⟩ := by
  rw [fieldFamilyE6, dite_eq_left h1, dite_eq_right h4, dite_eq_left h5]
  rfl

theorem isCompatible_fieldFamilyE6
    (hagree : ∀ x, hX.restrictTo (a3Levi_le_levi_high (K := K)) x =
      hY.restrictTo (a3Levi_le_levi_six (K := K)) x) :
    IsCompatible (adjDatumE6 K).leviAmalgam (fieldFamilyE6 hX hY hc4 hc5) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ j.1 := hij
  have hmono : ∀ {I : Finset (Fin (Tag.rank .E6))}, (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ I →
      (y : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I :=
    fun h => hxy ▸ CFSG.LieType.CurtisTits.levi_mono _ h x.2
  by_cases h1j : (1 : Fin (Tag.rank .E6)) ∈ j.1
  · by_cases h4j : (4 : Fin (Tag.rank .E6)) ∈ j.1
    ·
      have hj : (j.1 : Finset (Fin (Tag.rank .E6))) = {1, 4} :=
        eq_pair_of_card_le_two j.2 (one_ne_of four_cases) h1j h4j
      have hij' : ∀ a ∈ i.1, a = 1 ∨ a = 4 := fun a ha => by
        have := hsub ha
        rw [hj, Finset.mem_insert, Finset.mem_singleton] at this
        exact this
      rw [fieldFamilyE6_of_four h1j h4j]
      by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
      · by_cases h4i : (4 : Fin (Tag.rank .E6)) ∈ i.1
        · rw [fieldFamilyE6_of_four h1i h4i]
          exact congrArg _ (Subtype.ext hxy)
        · have h5i : (5 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => by
            rcases hij' 5 h with h' | h'
            exacts [five_ne_one_E6 h', five_ne_four_E6 h']
          have hi1 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {1} := fun a ha => by
            rcases hij' a ha with rfl | rfl
            · exact Finset.mem_singleton_self _
            · exact absurd ha h4i
          rw [fieldFamilyE6_of_six h1i h4i h5i, fieldPairLiftE6_of_mem_left hX hY _ hc4 _ (hmono hi1)]
          exact hY.restrictTo_eq_of_coe_eq _ _ _ _ hxy
      · have hi4 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {4} := fun a ha => by
          rcases hij' a ha with rfl | rfl
          · exact absurd ha h1i
          · exact Finset.mem_singleton_self _
        rw [fieldFamilyE6_of_one_not_mem h1i, fieldPairLiftE6_of_mem_right hX hY _ hc4 _ (hmono hi4)]
        exact hX.restrictTo_eq_of_coe_eq _ _ _ _ hxy
    · have h4i : (4 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h4j (hsub h)
      by_cases h5j : (5 : Fin (Tag.rank .E6)) ∈ j.1
      ·
        have hj : (j.1 : Finset (Fin (Tag.rank .E6))) = {1, 5} :=
          eq_pair_of_card_le_two j.2 (one_ne_of five_cases) h1j h5j
        have hij' : ∀ a ∈ i.1, a = 1 ∨ a = 5 := fun a ha => by
          have := hsub ha
          rw [hj, Finset.mem_insert, Finset.mem_singleton] at this
          exact this
        rw [fieldFamilyE6_of_five h1j h4j h5j]
        by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
        · by_cases h5i : (5 : Fin (Tag.rank .E6)) ∈ i.1
          · rw [fieldFamilyE6_of_five h1i h4i h5i]
            exact congrArg _ (Subtype.ext hxy)
          · have hi1 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {1} := fun a ha => by
              rcases hij' a ha with rfl | rfl
              · exact Finset.mem_singleton_self _
              · exact absurd ha h5i
            rw [fieldFamilyE6_of_six h1i h4i h5i,
              fieldPairLiftE6_of_mem_left hX hY _ hc5 _ (hmono hi1)]
            exact hY.restrictTo_eq_of_coe_eq _ _ _ _ hxy
        · have hi5 : (i.1 : Finset (Fin (Tag.rank .E6))) ⊆ {5} := fun a ha => by
            rcases hij' a ha with rfl | rfl
            · exact absurd ha h1i
            · exact Finset.mem_singleton_self _
          rw [fieldFamilyE6_of_one_not_mem h1i,
            fieldPairLiftE6_of_mem_right hX hY _ hc5 _ (hmono hi5)]
          exact hX.restrictTo_eq_of_coe_eq _ _ _ _ hxy
      ·
        have h5i : (5 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h5j (hsub h)
        rw [fieldFamilyE6_of_six h1j h4j h5j]
        by_cases h1i : (1 : Fin (Tag.rank .E6)) ∈ i.1
        · rw [fieldFamilyE6_of_six h1i h4i h5i]
          exact hY.restrictTo_eq_of_coe_eq _ _ _ _ hxy
        · rw [fieldFamilyE6_of_one_not_mem h1i]
          have hxA : (x : adjointGroup .E6 K) ∈ a3Levi K :=
            CFSG.LieType.CurtisTits.levi_mono _ (subset_a3Nodes_of_not_mem h1i h4i h5i) x.2
          rw [hX.restrictTo_eq_of_coe_eq _ a3Levi_le_levi_high x ⟨x, hxA⟩ rfl, hagree,
            hY.restrictTo_eq_of_coe_eq a3Levi_le_levi_six _ ⟨x, hxA⟩ y hxy]
  · have h1i : (1 : Fin (Tag.rank .E6)) ∉ i.1 := fun h => h1j (hsub h)
    rw [fieldFamilyE6_of_one_not_mem h1i, fieldFamilyE6_of_one_not_mem h1j]
    exact hX.restrictTo_eq_of_coe_eq _ _ _ _ hxy

theorem range_fieldPairLiftE6 [Finite G] (hZ : FieldNeighbourIso σ e .three)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
    (hc : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
      (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) b)) :
    (fieldPairLiftE6 hX hY hj hc).range = pieceCore e {1, j} := by
  have hJ3 : ({1, j} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.three.nodes :=
    Finset.insert_subset_iff.2 ⟨one_subset_three (Finset.mem_singleton_self _),
      singleton_subset_three_of hj⟩
  rw [fieldPairLiftE6, F4Pilot.range_supLift, hY.range_restrictTo_levi hq one_subset_six (by simp),
    hX.range_restrictTo_levi hq (singleton_subset_high_of hj) (by simp),
    ← hZ.range_restrictTo_levi hq one_subset_three (by simp),
    ← hZ.range_restrictTo_levi hq (singleton_subset_three_of hj) (by simp),
    ← hZ.range_restrictTo_levi hq hJ3 (Finset.card_le_two),
    hZ.range_restrictTo, hZ.range_restrictTo, hZ.range_restrictTo, ← Subgroup.map_sup]
  congr 1
  rw [F4Pilot.levi_pair, Subgroup.subgroupOf_sup (levi_le_neighbourLevi one_subset_three)
    (levi_le_neighbourLevi (singleton_subset_three_of hj))]

theorem range_fieldFamilyE6 [Finite G] (hZ : FieldNeighbourIso σ e .three)
    (hq : 4 ≤ Nat.card (fixSubfield σ))
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    (fieldFamilyE6 hX hY hc4 hc5 J).range = pieceCore e J.1 := by
  have hpair : ∀ {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
      (hc : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
        (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) b))
      (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (hjJ : j ∈ J.1),
      (fieldFamilyE6 hX hY hc4 hc5 J).range = (fieldPairLiftE6 hX hY hj hc).range →
      (fieldFamilyE6 hX hY hc4 hc5 J).range = pieceCore e J.1 := by
    intro j hj hc h1 hjJ hrange
    rw [hrange, range_fieldPairLiftE6 hZ hq hj hc,
      eq_pair_of_card_le_two J.2 (one_ne_of hj) h1 hjJ]
  by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1
  · by_cases h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1
    · refine hpair four_cases hc4 h1 h4 (le_antisymm ?_ ?_)
      · rintro _ ⟨x, rfl⟩
        rw [fieldFamilyE6_of_four h1 h4]
        exact ⟨_, rfl⟩
      · rintro _ ⟨z, rfl⟩
        have hz : (z : adjointGroup .E6 K) ∈
            CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1 := by
          rw [eq_pair_of_card_le_two J.2 (one_ne_of four_cases) h1 h4, F4Pilot.levi_pair]
          exact z.2
        exact ⟨⟨z, hz⟩, by rw [fieldFamilyE6_of_four h1 h4]⟩
    · by_cases h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1
      · refine hpair five_cases hc5 h1 h5 (le_antisymm ?_ ?_)
        · rintro _ ⟨x, rfl⟩
          rw [fieldFamilyE6_of_five h1 h4 h5]
          exact ⟨_, rfl⟩
        · rintro _ ⟨z, rfl⟩
          have hz : (z : adjointGroup .E6 K) ∈
              CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1 := by
            rw [eq_pair_of_card_le_two J.2 (one_ne_of five_cases) h1 h5, F4Pilot.levi_pair]
            exact z.2
          exact ⟨⟨z, hz⟩, by rw [fieldFamilyE6_of_five h1 h4 h5]⟩
      · have hφ : fieldFamilyE6 hX hY hc4 hc5 J = hY.restrictTo
            (levi_le_neighbourLevi (K := K) (subset_nodes_six_of_not_mem h4 h5)) :=
          MonoidHom.ext fun x => fieldFamilyE6_of_six h1 h4 h5 x
        rw [hφ, hY.range_restrictTo_levi hq (subset_nodes_six_of_not_mem h4 h5) J.2]
  · have hφ : fieldFamilyE6 hX hY hc4 hc5 J = hX.restrictTo
        (levi_le_neighbourLevi (K := K) (subset_nodes_high_of_one_not_mem h1)) :=
      MonoidHom.ext fun x => fieldFamilyE6_of_one_not_mem h1 x
    rw [hφ, hX.range_restrictTo_levi hq (subset_nodes_high_of_one_not_mem h1) J.2]

theorem fix_fieldFamilyE6 (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2})
    (x : adjointGroup .E6 (fixSubfield σ))
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1)
    (y : (adjDatumE6 K).leviAmalgam J)
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    fieldFamilyE6 hX hY hc4 hc5 J y = ((e.symm x : L) : G) := by
  have hpair : ∀ {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5)
      (hc : ∀ a b, Commute (hY.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
        (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) b))
      (h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1) (hjJ : j ∈ J.1)
      (hy : (y : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}),
      fieldPairLiftE6 hX hY hj hc ⟨y, hy⟩ = ((e.symm x : L) : G) := by
    intro j hj hc h1 hjJ hy
    have hJ : (J.1 : Finset (Fin (Tag.rank .E6))) = {1, j} :=
      eq_pair_of_card_le_two J.2 (one_ne_of hj) h1 hjJ
    have hx' : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup {j} := by
      rw [← F4Pilot.levi_pair, ← hJ]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_eq_of_mem_sup_of_commute_E6 (commute_adLevi_one (K := fixSubfield σ) hj) hx'
    obtain ⟨a', ha'⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype ha
    obtain ⟨b', hb'⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype hb
    have hyab : (⟨y, hy⟩ : ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j})) =
        ⟨a', mem_sup_left a'.2⟩ * ⟨b', mem_sup_right b'.2⟩ := by
      refine Subtype.ext (Subtype.ext ?_)
      change ((y : adjointGroup .E6 K) : ModGL .E6 K) =
        ((a' : adjointGroup .E6 K) : ModGL .E6 K) * ((b' : adjointGroup .E6 K) : ModGL .E6 K)
      rw [hxy, ha', hb', ← map_mul]
      rfl
    rw [hyab, map_mul, fieldPairLiftE6_of_mem_left hX hY hj hc _ a'.2,
      fieldPairLiftE6_of_mem_right hX hY hj hc _ b'.2,
      hY.restrictTo_fix _ (levi_le_neighbourLevi (K := fixSubfield σ) one_subset_six ha) _ ha',
      hX.restrictTo_fix _
        (levi_le_neighbourLevi (K := fixSubfield σ) (singleton_subset_high_of hj) hb) _ hb',
      map_mul, L.coe_mul]
  by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J.1
  · by_cases h4 : (4 : Fin (Tag.rank .E6)) ∈ J.1
    · rw [fieldFamilyE6_of_four h1 h4]
      exact hpair four_cases hc4 h1 h4 _
    · by_cases h5 : (5 : Fin (Tag.rank .E6)) ∈ J.1
      · rw [fieldFamilyE6_of_five h1 h4 h5]
        exact hpair five_cases hc5 h1 h5 _
      · rw [fieldFamilyE6_of_six h1 h4 h5]
        exact hY.restrictTo_fix _ (levi_le_neighbourLevi (K := fixSubfield σ)
          (subset_nodes_six_of_not_mem h4 h5) hx) y hxy
  · rw [fieldFamilyE6_of_one_not_mem h1]
    exact hX.restrictTo_fix _ (levi_le_neighbourLevi (K := fixSubfield σ)
      (subset_nodes_high_of_one_not_mem h1) hx) y hxy

end Family

section Exists

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem exists_isFieldRowFamily (hX : FieldNeighbourIso σ e .high)
    (hY : FieldNeighbourIso σ e .six) (hZ : FieldNeighbourIso σ e .three)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G, IsFieldRowFamily e φ ∧
      ∀ (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2})
        (h1 : (1 : Fin (Tag.rank .E6)) ∉ J.1) (x : (adjDatumE6 K).leviAmalgam J),
        φ J x = hX.restrictTo
          (levi_le_neighbourLevi (K := K) (subset_nodes_high_of_one_not_mem h1)) x := by
  obtain ⟨ρ, hρ, hagree⟩ := exists_twist_eq_on_a3 hX hY hq
  set hY' := hY.twist ρ hρ with hY'def
  have hc : ∀ {j : Fin (Tag.rank .E6)} (hj : j = 4 ∨ j = 5), ∀ a b,
      Commute (hY'.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a)
        (hX.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj)) b) := by
    intro j hj a b
    have hM1 : (hY'.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six)).range =
        (hZ.restrictTo (levi_le_neighbourLevi (K := K) one_subset_three)).range := by
      rw [hY'.range_restrictTo_levi hq one_subset_six (by simp),
        hZ.range_restrictTo_levi hq one_subset_three (by simp)]
    have hMj : (hX.restrictTo
        (levi_le_neighbourLevi (K := K) (singleton_subset_high_of hj))).range =
        (hZ.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_three_of hj))).range := by
      rw [hX.range_restrictTo_levi hq (singleton_subset_high_of hj) (by simp),
        hZ.range_restrictTo_levi hq (singleton_subset_three_of hj) (by simp)]
    obtain ⟨a', ha'⟩ : hY'.restrictTo (levi_le_neighbourLevi (K := K) one_subset_six) a ∈
        (hZ.restrictTo (levi_le_neighbourLevi (K := K) one_subset_three)).range :=
      hM1 ▸ ⟨a, rfl⟩
    obtain ⟨b', hb'⟩ : hX.restrictTo (levi_le_neighbourLevi (K := K)
        (singleton_subset_high_of hj)) b ∈
        (hZ.restrictTo (levi_le_neighbourLevi (K := K) (singleton_subset_three_of hj))).range :=
      hMj ▸ ⟨b, rfl⟩
    rw [← ha', ← hb']
    exact hZ.commute_restrictTo _ _ a' b' (commute_adLevi_one hj _ a'.2 _ b'.2)
  exact ⟨fieldFamilyE6 hX hY' (hc four_cases) (hc five_cases),
    ⟨isCompatible_fieldFamilyE6 hagree, range_fieldFamilyE6 hZ hq, fix_fieldFamilyE6⟩,
    fun J h1 x => fieldFamilyE6_of_one_not_mem h1 x⟩

end Exists

end CFSG.SeitzReduction.E6Pilot
