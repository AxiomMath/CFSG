module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedDatum twistedRootGroup)

local instance f4PilotCTGraphTwistedFamilyNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem zero_not_mem_singleton_of_ne_F4 {i : Fin (Tag.rank .F4)} (hi : i ≠ 0) :
    (0 : Fin (Tag.rank .F4)) ∉ ({i} : Finset (Fin (Tag.rank .F4))) := by
  rw [Finset.mem_singleton]
  exact fun h => hi h.symm

theorem three_not_mem_zero_F4 :
    (3 : Fin (Tag.rank .F4)) ∉ ({0} : Finset (Fin (Tag.rank .F4))) := by
  decide

theorem ne_zero_of_mem_nodes_X {i : Fin (Tag.rank .F4)} (hi : i ∈ AmalgamNeighbour.X.nodes) :
    i ≠ 0 := by
  revert i
  decide

theorem mem_one_two_of_mem_nodes_Y {i : Fin (Tag.rank .F4)} (hi : i ∈ AmalgamNeighbour.Y.nodes)
    (hi0 : i ≠ 0) : i ∈ ({1, 2} : Finset (Fin (Tag.rank .F4))) := by
  revert i
  decide

section Pair


variable {k : Type} [Field k] {θ : k →+* k}

variable (k θ) in
noncomputable abbrev twLevi (S : Finset (Fin (Tag.rank .F4))) : Subgroup (fixedGroup k θ) :=
  CFSG.LieType.CurtisTits.levi (twistedRootGroup k θ) S

theorem commute_twistedRootGroup_zero_three (hθ : ∀ c, θ (θ c) = c)
    {s t : Fin (Tag.rank .F4) → ℤ}
    (hs : s = Pi.single 0 1 ∨ s = -Pi.single 0 1) (ht : t = Pi.single 3 1 ∨ t = -Pi.single 3 1)
    {x y : fixedGroup k θ} (hx : x ∈ twistedRootGroup k θ s)
    (hy : y ∈ twistedRootGroup k θ t) : Commute x y := by
  have hroot : ∀ v, v ∈ (twistedDatum k θ).roots ↔ IsRoot .F4 v := fun v => by
    rw [CFSG.LieType.Steinberg.TwistedE6.twistedDatum_roots]
    rfl
  have h10 : (1 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h20 : (2 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h30 : (3 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h13 : (1 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  have h23 : (2 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  have h03 : (0 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  refine commute_of_forall_not_mem_roots
    (CFSG.LieType.Steinberg.TwistedE6.twistedDatum_steinbergExtras θ hθ) ?_ ?_ ?_ ?_ hx hy
  · refine (hroot _).2 ?_
    rcases hs with rfl | rfl
    exacts [isRoot_single _ 0, isRoot_neg_single _ 0]
  · refine (hroot _).2 ?_
    rcases ht with rfl | rfl
    exacts [isRoot_single _ 3, isRoot_neg_single _ 3]
  · intro a b hab
    have hab' : (a • s + b • t : Fin (Tag.rank .F4) → ℤ) = 0 := hab
    have h0 := congrFun hab' 0
    have h3 := congrFun hab' 3
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h30, h03] at h0 h3 <;> exact ⟨h0, h3⟩
  · intro a b ha hb hmem
    have hmem' : a • s + b • t ∈ rootFinset .F4 := mem_rootFinset.2 ((hroot _).1 hmem)
    have h := f4_root_support_zero_three_check _ hmem'
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h10, h20, h30, h13, h23, h03] at h <;> omega

theorem commute_twLevi_zero_three (hθ : ∀ c, θ (θ c) = c) :
    ∀ x ∈ twLevi k θ {0}, ∀ y ∈ twLevi k θ {3}, Commute x y := by
  dsimp only [twLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton,
    CFSG.LieType.CurtisTits.rankOne, CFSG.LieType.CurtisTits.rankOne]
  refine forall_commute_sup_left (forall_commute_sup_right ?_ ?_)
    (forall_commute_sup_right ?_ ?_)
  · exact fun x hx y hy => commute_twistedRootGroup_zero_three hθ (Or.inl rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_twistedRootGroup_zero_three hθ (Or.inl rfl) (Or.inr rfl) hx hy
  · exact fun x hx y hy => commute_twistedRootGroup_zero_three hθ (Or.inr rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_twistedRootGroup_zero_three hθ (Or.inr rfl) (Or.inr rfl) hx hy

theorem twLevi_zero_inf_three_eq_bot (hθ : ∀ c, θ (θ c) = c) :
    twLevi k θ {0} ⊓ twLevi k θ {3} = ⊥ := by
  have hc := commute_twLevi_zero_three (k := k) hθ
  dsimp only [twLevi] at hc ⊢
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton] at hc ⊢
  exact rankOne_inf_rankOne_eq_bot
    (CFSG.LieType.Steinberg.TwistedE6.twistedDatum_isCTGroupDatum θ hθ
      (CFSG.LieType.Steinberg.TwistedE6.iSup_twistedDatum_rootGroup θ hθ))
    (CFSG.LieType.Steinberg.TwistedE6.twistedDatum_steinbergExtras θ hθ)
    (by decide : (0 : Fin (Tag.rank .F4)) ≠ 3) hc

theorem twLevi_le_sup_of_mem_of_mem {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J) :
    twLevi k θ J ≤ twLevi k θ {0} ⊔ twLevi k θ {3} := by
  dsimp only [twLevi]
  rw [eq_pair_zero_three hJ h0 h3, levi_pair]

end Pair

section Family


variable {k : Type} [Field k] {θ : k →+* k} {G : Type} [Group G]

@[expose] noncomputable def twLeviRestrict {S J : Finset (Fin (Tag.rank .F4))}
    (Φ : twLevi k θ S →* G) (h : J ⊆ S) : twLevi k θ J →* G :=
  Φ.comp (Subgroup.inclusion (CFSG.LieType.CurtisTits.levi_mono _ h))

theorem twLeviRestrict_apply {S J : Finset (Fin (Tag.rank .F4))} (Φ : twLevi k θ S →* G)
    (h : J ⊆ S) (x : twLevi k θ J) :
    twLeviRestrict Φ h x = Φ ⟨x, CFSG.LieType.CurtisTits.levi_mono _ h x.2⟩ :=
  rfl

theorem twLeviRestrict_eq_of_coe_eq {S I J : Finset (Fin (Tag.rank .F4))}
    (Φ : twLevi k θ S →* G) (hI : I ⊆ S) (hJ : J ⊆ S) (x : twLevi k θ I) (y : twLevi k θ J)
    (hxy : (x : fixedGroup k θ) = y) : twLeviRestrict Φ hI x = twLeviRestrict Φ hJ y := by
  rw [twLeviRestrict_apply, twLeviRestrict_apply]
  congr 1
  exact Subtype.ext hxy

variable (hθ : ∀ c, θ (θ c) = c) (ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G)
  (ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G)
  (hc : ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a) (twLeviRestrict ΦX three_subset_X b))

@[expose] noncomputable def twGraphPairLift : ↥(twLevi k θ {0} ⊔ twLevi k θ {3}) →* G :=
  supLift (commute_twLevi_zero_three hθ) (twLevi_zero_inf_three_eq_bot hθ) _ _ hc

theorem twGraphPairLift_of_mem_left (z : ↥(twLevi k θ {0} ⊔ twLevi k θ {3}))
    (hz : (z : fixedGroup k θ) ∈ twLevi k θ {0}) :
    twGraphPairLift hθ ΦX ΦY hc z = twLeviRestrict ΦY zero_subset_Y ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_left (commute_twLevi_zero_three hθ) (twLevi_zero_inf_three_eq_bot hθ) hc
    ⟨z, hz⟩

theorem twGraphPairLift_of_mem_right (z : ↥(twLevi k θ {0} ⊔ twLevi k θ {3}))
    (hz : (z : fixedGroup k θ) ∈ twLevi k θ {3}) :
    twGraphPairLift hθ ΦX ΦY hc z = twLeviRestrict ΦX three_subset_X ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_right (commute_twLevi_zero_three hθ) (twLevi_zero_inf_three_eq_bot hθ) hc
    ⟨z, hz⟩

theorem range_twGraphPairLift : (twGraphPairLift hθ ΦX ΦY hc).range ≤ ΦX.range ⊔ ΦY.range := by
  rw [twGraphPairLift, range_supLift]
  refine sup_le (le_sup_of_le_right ?_) (le_sup_of_le_left ?_) <;>
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩

@[expose] noncomputable def twGraphFamily
    (J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}) : twLevi k θ J.1 →* G :=
  if h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1 then
    if h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1 then
      (twGraphPairLift hθ ΦX ΦY hc).comp
        (Subgroup.inclusion (twLevi_le_sup_of_mem_of_mem J.2 h0 h3))
    else twLeviRestrict ΦY (subset_nodes_Y_of_three_not_mem h3)
  else twLeviRestrict ΦX (subset_nodes_X_of_zero_not_mem h0)

variable {hθ ΦX ΦY hc}

theorem twGraphFamily_of_zero_not_mem
    {J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J.1) (x : twLevi k θ J.1) :
    twGraphFamily hθ ΦX ΦY hc J x = twLeviRestrict ΦX (subset_nodes_X_of_zero_not_mem h0) x := by
  rw [twGraphFamily, dite_eq_right h0]

theorem twGraphFamily_of_three_not_mem
    {J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∉ J.1)
    (x : twLevi k θ J.1) :
    twGraphFamily hθ ΦX ΦY hc J x = twLeviRestrict ΦY (subset_nodes_Y_of_three_not_mem h3) x := by
  rw [twGraphFamily, dite_eq_left h0, dite_eq_right h3]

theorem twGraphFamily_of_mem_of_mem
    {J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1)
    (x : twLevi k θ J.1) :
    twGraphFamily hθ ΦX ΦY hc J x =
      twGraphPairLift hθ ΦX ΦY hc ⟨x, twLevi_le_sup_of_mem_of_mem J.2 h0 h3 x.2⟩ := by
  rw [twGraphFamily, dite_eq_left h0, dite_eq_left h3]
  rfl

theorem isCompatible_twGraphFamily
    (hagree : ∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
      twLeviRestrict ΦY one_two_subset_Y x) :
    ∀ i j : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, i.1 ⊆ j.1 →
      ∀ (x : twLevi k θ i.1) (y : twLevi k θ j.1), (x : fixedGroup k θ) = y →
        twGraphFamily hθ ΦX ΦY hc i x = twGraphFamily hθ ΦX ΦY hc j y := by
  intro i j hsub x y hxy
  by_cases h0j : (0 : Fin (Tag.rank .F4)) ∈ j.1
  · by_cases h3j : (3 : Fin (Tag.rank .F4)) ∈ j.1
    · have hj : (j.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three j.2 h0j h3j
      rw [twGraphFamily_of_mem_of_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · by_cases h3i : (3 : Fin (Tag.rank .F4)) ∈ i.1
        · rw [twGraphFamily_of_mem_of_mem h0i h3i]
          exact congrArg (twGraphPairLift hθ ΦX ΦY hc) (Subtype.ext hxy)
        · have hi0 : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ {0} := by
            intro a ha
            have ha' := hsub ha
            rw [hj, Finset.mem_insert, Finset.mem_singleton] at ha'
            rcases ha' with rfl | rfl
            · exact Finset.mem_singleton_self _
            · exact absurd ha h3i
          have hy0 : (y : fixedGroup k θ) ∈ twLevi k θ {0} := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hi0 x.2
          rw [twGraphFamily_of_three_not_mem h0i h3i, twGraphPairLift_of_mem_left hθ ΦX ΦY hc _ hy0]
          exact twLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
      · have hi3 : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ {3} := by
          intro a ha
          have ha' := hsub ha
          rw [hj, Finset.mem_insert, Finset.mem_singleton] at ha'
          rcases ha' with rfl | rfl
          · exact absurd ha h0i
          · exact Finset.mem_singleton_self _
        have hy3 : (y : fixedGroup k θ) ∈ twLevi k θ {3} := by
          rw [← hxy]
          exact CFSG.LieType.CurtisTits.levi_mono _ hi3 x.2
        rw [twGraphFamily_of_zero_not_mem h0i, twGraphPairLift_of_mem_right hθ ΦX ΦY hc _ hy3]
        exact twLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
    · have h3i : (3 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h3j (hsub h)
      rw [twGraphFamily_of_three_not_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · rw [twGraphFamily_of_three_not_mem h0i h3i]
        exact twLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy
      · rw [twGraphFamily_of_zero_not_mem h0i]
        have hx12 : (x : fixedGroup k θ) ∈ twLevi k θ {1, 2} :=
          CFSG.LieType.CurtisTits.levi_mono _ (subset_one_two_of_not_mem h0i h3i) x.2
        rw [twLeviRestrict_eq_of_coe_eq ΦX _ one_two_subset_X x ⟨x, hx12⟩ rfl, hagree,
          twLeviRestrict_eq_of_coe_eq ΦY one_two_subset_Y _ ⟨x, hx12⟩ y hxy]
  · have h0i : (0 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h0j (hsub h)
    rw [twGraphFamily_of_zero_not_mem h0i, twGraphFamily_of_zero_not_mem h0j]
    exact twLeviRestrict_eq_of_coe_eq _ _ _ _ _ hxy

theorem range_le_of_forall_twLevi_singleton {S : Finset (Fin (Tag.rank .F4))}
    (Φ : twLevi k θ S →* G) {H : Subgroup G}
    (h : ∀ i (hi : i ∈ S) (x : twLevi k θ {i}),
      twLeviRestrict Φ (Finset.singleton_subset_iff.2 hi) x ∈ H) : Φ.range ≤ H := by
  rintro _ ⟨x, rfl⟩
  have hle : twLevi k θ S ≤ (H.comap Φ).map (twLevi k θ S).subtype := by
    show (⨆ j ∈ S, CFSG.LieType.CurtisTits.rankOne (twistedRootGroup k θ) j) ≤ _
    refine iSup₂_le fun i hi y hy => ?_
    have hy' : y ∈ twLevi k θ {i} := by
      rw [twLevi, CFSG.LieType.CurtisTits.levi_singleton]
      exact hy
    exact ⟨⟨y, CFSG.LieType.CurtisTits.levi_mono _ (Finset.singleton_subset_iff.2 hi) hy'⟩,
      h i hi ⟨y, hy'⟩, rfl⟩
  obtain ⟨x', hx', hxx'⟩ := hle x.2
  have hx : x' = x := Subtype.ext hxx'
  rw [← hx]
  exact hx'

theorem iSup_range_twGraphFamily
    (hagree : ∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
      twLeviRestrict ΦY one_two_subset_Y x) :
    ⨆ J, (twGraphFamily hθ ΦX ΦY hc J).range = ΦX.range ⊔ ΦY.range := by
  have hmem : ∀ (J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}) (x : twLevi k θ J.1),
      twGraphFamily hθ ΦX ΦY hc J x ∈ ⨆ J, (twGraphFamily hθ ΦX ΦY hc J).range :=
    fun J x => le_iSup (fun J => (twGraphFamily hθ ΦX ΦY hc J).range) J ⟨x, rfl⟩
  apply le_antisymm
  · refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
    · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
      · rw [twGraphFamily_of_mem_of_mem h0 h3]
        exact range_twGraphPairLift hθ ΦX ΦY hc ⟨_, rfl⟩
      · rw [twGraphFamily_of_three_not_mem h0 h3]
        exact mem_sup_right ⟨_, rfl⟩
    · rw [twGraphFamily_of_zero_not_mem h0]
      exact mem_sup_left ⟨_, rfl⟩
  · refine sup_le ?_ ?_
    · refine range_le_of_forall_twLevi_singleton ΦX fun i hi x => ?_
      have hi0 := zero_not_mem_singleton_of_ne_F4 (ne_zero_of_mem_nodes_X hi)
      rw [twLeviRestrict_eq_of_coe_eq ΦX _ (subset_nodes_X_of_zero_not_mem hi0) x x rfl,
        ← twGraphFamily_of_zero_not_mem (J := ⟨{i}, card_singleton_le_two_F4 i⟩) hi0 x]
      exact hmem ⟨{i}, card_singleton_le_two_F4 i⟩ x
    · refine range_le_of_forall_twLevi_singleton ΦY fun i hi x => ?_
      by_cases hi0 : i = 0
      · subst hi0
        rw [twLeviRestrict_eq_of_coe_eq ΦY _
          (subset_nodes_Y_of_three_not_mem three_not_mem_zero_F4) x x rfl,
          ← twGraphFamily_of_three_not_mem (J := ⟨{0}, card_singleton_le_two_F4 0⟩)
            (Finset.mem_singleton_self _) three_not_mem_zero_F4 x]
        exact hmem ⟨{0}, card_singleton_le_two_F4 0⟩ x
      · have hi12 : ({i} : Finset (Fin (Tag.rank .F4))) ⊆ {1, 2} :=
          Finset.singleton_subset_iff.2 (mem_one_two_of_mem_nodes_Y hi hi0)
        have hi0' := zero_not_mem_singleton_of_ne_F4 hi0
        have hx12 : (x : fixedGroup k θ) ∈ twLevi k θ {1, 2} :=
          CFSG.LieType.CurtisTits.levi_mono _ hi12 x.2
        rw [twLeviRestrict_eq_of_coe_eq ΦY _ one_two_subset_Y x ⟨x, hx12⟩ rfl, ← hagree,
          twLeviRestrict_eq_of_coe_eq ΦX one_two_subset_X
            (subset_nodes_X_of_zero_not_mem hi0') ⟨x, hx12⟩ x rfl,
          ← twGraphFamily_of_zero_not_mem (J := ⟨{i}, card_singleton_le_two_F4 i⟩) hi0' x]
        exact hmem ⟨{i}, card_singleton_le_two_F4 i⟩ x

end Family

section Main


variable {k : Type} [Field k] {θ : k →+* k} {G : Type} [Group G]

theorem sigmaHat_mem_twLevi {S : Finset (Fin (Tag.rank .F4))} {x : fixedGroup k θ}
    (hx : x ∈ twLevi k θ S) : sigmaHat θ x ∈ twLevi k θ S := by
  have hle : twLevi k θ S ≤ (twLevi k θ S).comap (sigmaHat θ) := by
    show (⨆ j ∈ S, CFSG.LieType.CurtisTits.rankOne (twistedRootGroup k θ) j) ≤ _
    refine iSup₂_le fun i hi y hy => ?_
    rw [Subgroup.mem_comap]
    exact CFSG.LieType.CurtisTits.rankOne_le_levi _ hi (sigmaHat_mem_rankOne θ hy)
  exact hle hx

@[expose] noncomputable def sigmaTwLevi (S : Finset (Fin (Tag.rank .F4))) :
    twLevi k θ S →* twLevi k θ S :=
  ((sigmaHat θ).comp (twLevi k θ S).subtype).codRestrict (twLevi k θ S)
    fun x => sigmaHat_mem_twLevi x.2

theorem coe_sigmaTwLevi (S : Finset (Fin (Tag.rank .F4))) (x : twLevi k θ S) :
    ((sigmaTwLevi S x : twLevi k θ S) : fixedGroup k θ) = sigmaHat θ x :=
  rfl

theorem sigmaTwLevi_sigmaTwLevi (S : Finset (Fin (Tag.rank .F4))) (x : twLevi k θ S) :
    sigmaTwLevi S (sigmaTwLevi S x) = x :=
  Subtype.ext (Subtype.ext
    (CFSG.LieType.Steinberg.TwistedE6.sigma_sigma (RingHom.id k) (fun _ => rfl) _))

variable {hθ : ∀ c, θ (θ c) = c} {ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G}
  {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G}
  {hc : ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a) (twLeviRestrict ΦX three_subset_X b)}

theorem conj_twGraphFamily {t : G}
    (hconjX : ∀ x y : twLevi k θ AmalgamNeighbour.X.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦX x * t⁻¹ = ΦX y)
    (hconjY : ∀ x y : twLevi k θ AmalgamNeighbour.Y.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦY x * t⁻¹ = ΦY y)
    (i : Fin (Tag.rank .F4)) (x y : twLevi k θ {i})
    (hxy : (y : fixedGroup k θ) = sigmaHat θ x) :
    t * twGraphFamily hθ ΦX ΦY hc ⟨{i}, card_singleton_le_two_F4 i⟩ x * t⁻¹ =
      twGraphFamily hθ ΦX ΦY hc ⟨{i}, card_singleton_le_two_F4 i⟩ y := by
  by_cases hi : i = 0
  · subst hi
    rw [twGraphFamily_of_three_not_mem (J := ⟨{0}, card_singleton_le_two_F4 0⟩)
      (Finset.mem_singleton_self _) three_not_mem_zero_F4 x,
      twGraphFamily_of_three_not_mem (J := ⟨{0}, card_singleton_le_two_F4 0⟩)
      (Finset.mem_singleton_self _) three_not_mem_zero_F4 y,
      twLeviRestrict_apply, twLeviRestrict_apply]
    exact hconjY _ _ hxy
  · have hi0 := zero_not_mem_singleton_of_ne_F4 hi
    rw [twGraphFamily_of_zero_not_mem (J := ⟨{i}, card_singleton_le_two_F4 i⟩) hi0 x,
      twGraphFamily_of_zero_not_mem (J := ⟨{i}, card_singleton_le_two_F4 i⟩) hi0 y,
      twLeviRestrict_apply, twLeviRestrict_apply]
    exact hconjX _ _ hxy

theorem isTwistedE6GraphRowFamily_twGraphFamily {L : Subgroup G} {F : Type} [Field F]
    {e : L ≃* adjointGroup .F4 F} {t : G}
    (hagree : ∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
      twLeviRestrict ΦY one_two_subset_Y x)
    (hconjX : ∀ x y : twLevi k θ AmalgamNeighbour.X.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦX x * t⁻¹ = ΦX y)
    (hconjY : ∀ x y : twLevi k θ AmalgamNeighbour.Y.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦY x * t⁻¹ = ΦY y)
    (hrange : ΦX.range ⊔ ΦY.range = pieceSpan e) :
    IsTwistedE6GraphRowFamily e t k θ (twGraphFamily hθ ΦX ΦY hc) where
  compatible := fun i j hij x y hxy =>
    isCompatible_twGraphFamily hagree ⟨i.1, i.2⟩ ⟨j.1, j.2⟩ hij x y hxy
  iSup_range := (iSup_range_twGraphFamily hagree).trans hrange
  conj := conj_twGraphFamily hconjX hconjY

end Main

section Param


variable {k : Type} [Field k] {θ : k →+* k} {G : Type} [Group G]

theorem exists_twAgree_of_agree_or_twist {ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G}
    {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G} {t : G}
    (htw : (∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
        twLeviRestrict ΦY one_two_subset_Y x) ∨
      (∀ x y : twLevi k θ {1, 2}, (y : fixedGroup k θ) = sigmaHat θ x →
        twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y))
    (hconjY : ∀ x y : twLevi k θ AmalgamNeighbour.Y.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦY x * t⁻¹ = ΦY y)
    (hc : ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a) (twLeviRestrict ΦX three_subset_X b)) :
    ∃ ΦY' : twLevi k θ AmalgamNeighbour.Y.nodes →* G,
      (∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
        twLeviRestrict ΦY' one_two_subset_Y x) ∧
      (∀ x y : twLevi k θ AmalgamNeighbour.Y.nodes,
        (y : fixedGroup k θ) = sigmaHat θ x → t * ΦY' x * t⁻¹ = ΦY' y) ∧
      ΦY'.range = ΦY.range ∧
      (∀ a b, Commute (twLeviRestrict ΦY' zero_subset_Y a)
        (twLeviRestrict ΦX three_subset_X b)) := by
  rcases htw with h | h
  · exact ⟨ΦY, h, hconjY, rfl, hc⟩
  set τ := sigmaTwLevi (k := k) (θ := θ) AmalgamNeighbour.Y.nodes with hτ
  refine ⟨ΦY.comp τ, fun x => ?_, fun x y hxy => ?_, ?_, fun a b => ?_⟩
  · rw [twLeviRestrict_apply, twLeviRestrict_apply, MonoidHom.comp_apply]
    have hσx : sigmaHat θ (x : fixedGroup k θ) ∈ twLevi k θ {1, 2} := sigmaHat_mem_twLevi x.2
    have := h x ⟨_, hσx⟩ rfl
    rw [twLeviRestrict_apply, twLeviRestrict_apply] at this
    rw [this]
    congr 1
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    refine hconjY _ _ ?_
    rw [coe_sigmaTwLevi, coe_sigmaTwLevi, hxy]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 fun x => ⟨τ x, sigmaTwLevi_sigmaTwLevi _ x⟩,
      ← MonoidHom.range_eq_map]
  · rw [twLeviRestrict_apply, MonoidHom.comp_apply]
    have hσa : sigmaHat θ (a : fixedGroup k θ) ∈ twLevi k θ {0} := sigmaHat_mem_twLevi a.2
    have := hc ⟨_, hσa⟩ b
    rw [twLeviRestrict_apply] at this
    exact this

variable {L : Subgroup G} {F : Type} [Field F]

structure IsTwistedE6GraphRowParam (e : L ≃* adjointGroup .F4 F) (t : G)
    (ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G)
    (ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G) : Prop where
  agree_or_twist : (∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
      twLeviRestrict ΦY one_two_subset_Y x) ∨
    (∀ x y : twLevi k θ {1, 2}, (y : fixedGroup k θ) = sigmaHat θ x →
      twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y)
  conjX : ∀ x y : twLevi k θ AmalgamNeighbour.X.nodes,
    (y : fixedGroup k θ) = sigmaHat θ x → t * ΦX x * t⁻¹ = ΦX y
  conjY : ∀ x y : twLevi k θ AmalgamNeighbour.Y.nodes,
    (y : fixedGroup k θ) = sigmaHat θ x → t * ΦY x * t⁻¹ = ΦY y
  comm : ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a) (twLeviRestrict ΦX three_subset_X b)
  range_sup : ΦX.range ⊔ ΦY.range = pieceSpan e

theorem IsTwistedE6GraphRowParam.exists_isTwistedE6GraphRowFamily (hθ : ∀ c, θ (θ c) = c)
    {e : L ≃* adjointGroup .F4 F} {t : G} {ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G}
    {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G} (h : IsTwistedE6GraphRowParam e t ΦX ΦY) :
    ∃ φ : ∀ J, (twistedDatum k θ).leviAmalgam J →* G, IsTwistedE6GraphRowFamily e t k θ φ := by
  obtain ⟨ΦY', hagree, hconjY', hrange', hc'⟩ :=
    exists_twAgree_of_agree_or_twist h.agree_or_twist h.conjY h.comm
  exact ⟨twGraphFamily hθ ΦX ΦY' hc',
    isTwistedE6GraphRowFamily_twGraphFamily hagree h.conjX hconjY'
      (by rw [hrange']; exact h.range_sup)⟩

@[expose] def TwistedE6GraphRowParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    TwistedE6RowKinds e t f →
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (σ' : K' ≃+* K'), Nat.card K' = (2 ^ f) ^ 2 ∧
      (∀ c, σ' c = c ^ (2 ^ f)) ∧
      ∃ (ΦX : twLevi K' σ'.toRingHom AmalgamNeighbour.X.nodes →* G)
        (ΦY : twLevi K' σ'.toRingHom AmalgamNeighbour.Y.nodes →* G),
        IsTwistedE6GraphRowParam e t ΦX ΦY

theorem twistedE6GraphRowFamilyInput_of_paramInput (h : TwistedE6GraphRowParamInput) :
    TwistedE6GraphRowFamilyInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk
  obtain ⟨K', i1, i2, σ', hK', hσ', ΦX, ΦY, hp⟩ := h G L K e t f hw hf hk
  exact ⟨K', i1, i2, σ', hK', hσ', hp.exists_isTwistedE6GraphRowFamily
    (involutive_of_natCard_eq hK' hσ')⟩

end Param

section Reduction


theorem twistedE6RowCTQuotInput_of_paramInput (h : TwistedE6GraphRowParamInput) :
    TwistedE6RowCTQuotInput :=
  twistedE6RowCTQuotInput_of_familyInput (twistedE6GraphRowFamilyInput_of_paramInput h)

end Reduction

end CFSG.SeitzReduction.F4Pilot
