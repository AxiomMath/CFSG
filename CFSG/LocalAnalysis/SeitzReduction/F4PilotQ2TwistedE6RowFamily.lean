module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6RowCT
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwistedFamily

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg
open CFSG.LieType.CurtisTits (IsCompatible rankOne levi)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedDatum twistedRootGroup)

set_option linter.unusedSectionVars false

local instance f4PilotQ2TwistedE6RowFamilyNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Ext

variable {k : Type} [Field k] {θ : k →+* k} {G : Type} [Group G]

theorem twLevi_singleton_le {S : Finset (Fin (Tag.rank .F4))} {i : Fin (Tag.rank .F4)}
    (hi : i ∈ S) : twLevi k θ {i} ≤ twLevi k θ S :=
  CFSG.LieType.CurtisTits.levi_mono _ (Finset.singleton_subset_iff.2 hi)

theorem eq_top_of_forall_rankOne {S : Finset (Fin (Tag.rank .F4))} (H' : Subgroup (twLevi k θ S))
    (h : ∀ i (hi : i ∈ S) (x : fixedGroup k θ) (hx : x ∈ twLevi k θ {i}),
      (⟨x, twLevi_singleton_le hi hx⟩ : twLevi k θ S) ∈ H') : H' = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hle : twLevi k θ S ≤ H'.map (twLevi k θ S).subtype := by
    change (⨆ j ∈ S, rankOne (twistedRootGroup k θ) j) ≤ _
    refine iSup₂_le fun i hi => ?_
    intro y hy
    have hy' : y ∈ twLevi k θ {i} := by
      rw [twLevi, CFSG.LieType.CurtisTits.levi_singleton]
      exact hy
    exact ⟨_, h i hi y hy', rfl⟩
  obtain ⟨⟨y, hy⟩, hyH, hyx⟩ := hle hx
  have hyx' : y = x := hyx
  subst hyx'
  exact hyH

theorem hom_ext_twLevi {S : Finset (Fin (Tag.rank .F4))} {f₁ f₂ : twLevi k θ S →* G}
    (h : ∀ i (hi : i ∈ S) (x : fixedGroup k θ) (hx : x ∈ twLevi k θ {i}),
      f₁ ⟨x, twLevi_singleton_le hi hx⟩ = f₂ ⟨x, twLevi_singleton_le hi hx⟩) : f₁ = f₂ := by
  have htop := eq_top_of_forall_rankOne (f₁.eqLocus f₂) h
  ext x
  have hx : x ∈ f₁.eqLocus f₂ := htop ▸ mem_top x
  exact hx

theorem isCompatible_of_rankOne
    (φ : ∀ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, twLevi k θ J.1 →* G)
    (ψ : ∀ i : Fin (Tag.rank .F4), twLevi k θ {i} →* G)
    (hψ : ∀ (J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}) (i : Fin (Tag.rank .F4))
      (hi : i ∈ J.1) (x : fixedGroup k θ) (hx : x ∈ twLevi k θ {i}),
      φ J ⟨x, twLevi_singleton_le hi hx⟩ = ψ i ⟨x, hx⟩) :
    ∀ I J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, I.1 ⊆ J.1 →
      ∀ (x : twLevi k θ I.1) (y : twLevi k θ J.1), (x : fixedGroup k θ) = y → φ I x = φ J y := by
  intro I J hIJ x y hxy
  have hle : twLevi k θ I.1 ≤ twLevi k θ J.1 := CFSG.LieType.CurtisTits.levi_mono _ hIJ
  have hext : φ I = (φ J).comp (Subgroup.inclusion hle) := by
    refine hom_ext_twLevi fun i hi z hz => ?_
    have h1 := hψ I i hi z hz
    have h2 := hψ J i (hIJ hi) z hz
    have h3 : Subgroup.inclusion hle ⟨z, twLevi_singleton_le hi hz⟩ =
        ⟨z, twLevi_singleton_le (hIJ hi) hz⟩ := Subtype.ext (Subgroup.coe_inclusion hle _)
    rw [MonoidHom.comp_apply, h3, h1, h2]
  have h4 : Subgroup.inclusion hle x = y := Subtype.ext ((Subgroup.coe_inclusion hle x).trans hxy)
  rw [hext, MonoidHom.comp_apply, h4]

end Ext

theorem f4_root_support_zero_two_check :
    ∀ γ ∈ rootFinset .F4, γ 1 = 0 → γ 3 = 0 → γ 0 = 0 ∨ γ 2 = 0 := by
  decide +kernel

section Pair

variable {k : Type} [Field k] {θ : k →+* k}

theorem commute_twistedRootGroup_zero_two (hθ : ∀ c, θ (θ c) = c)
    {s t : Fin (Tag.rank .F4) → ℤ}
    (hs : s = Pi.single 0 1 ∨ s = -Pi.single 0 1) (ht : t = Pi.single 2 1 ∨ t = -Pi.single 2 1)
    {x y : fixedGroup k θ} (hx : x ∈ twistedRootGroup k θ s)
    (hy : y ∈ twistedRootGroup k θ t) : Commute x y := by
  have hroot : ∀ v, v ∈ (twistedDatum k θ).roots ↔ IsRoot .F4 v := fun v => by
    rw [CFSG.LieType.Steinberg.TwistedE6.twistedDatum_roots]
    rfl
  have h10 : (1 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h20 : (2 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h30 : (3 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h12 : (1 : Fin (Tag.rank .F4)) ≠ 2 := by decide
  have h32 : (3 : Fin (Tag.rank .F4)) ≠ 2 := by decide
  have h02 : (0 : Fin (Tag.rank .F4)) ≠ 2 := by decide
  refine commute_of_forall_not_mem_roots
    (CFSG.LieType.Steinberg.TwistedE6.twistedDatum_steinbergExtras θ hθ) ?_ ?_ ?_ ?_ hx hy
  · refine (hroot _).2 ?_
    rcases hs with rfl | rfl
    exacts [isRoot_single _ 0, isRoot_neg_single _ 0]
  · refine (hroot _).2 ?_
    rcases ht with rfl | rfl
    exacts [isRoot_single _ 2, isRoot_neg_single _ 2]
  · intro a b hab
    have hab' : (a • s + b • t : Fin (Tag.rank .F4) → ℤ) = 0 := hab
    have h0 := congrFun hab' 0
    have h2 := congrFun hab' 2
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h20, h02] at h0 h2 <;> exact ⟨h0, h2⟩
  · intro a b ha hb hmem
    have hmem' : a • s + b • t ∈ rootFinset .F4 := mem_rootFinset.2 ((hroot _).1 hmem)
    have h := f4_root_support_zero_two_check _ hmem'
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h10, h20, h30, h12, h32, h02] at h <;> omega

theorem commute_twLevi_zero_two (hθ : ∀ c, θ (θ c) = c) :
    ∀ x ∈ twLevi k θ {0}, ∀ y ∈ twLevi k θ {2}, Commute x y := by
  dsimp only [twLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton,
    CFSG.LieType.CurtisTits.rankOne, CFSG.LieType.CurtisTits.rankOne]
  refine forall_commute_sup_left (forall_commute_sup_right ?_ ?_)
    (forall_commute_sup_right ?_ ?_)
  · exact fun x hx y hy => commute_twistedRootGroup_zero_two hθ (Or.inl rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_twistedRootGroup_zero_two hθ (Or.inl rfl) (Or.inr rfl) hx hy
  · exact fun x hx y hy => commute_twistedRootGroup_zero_two hθ (Or.inr rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_twistedRootGroup_zero_two hθ (Or.inr rfl) (Or.inr rfl) hx hy

theorem twLevi_zero_inf_two_eq_bot (hθ : ∀ c, θ (θ c) = c) :
    twLevi k θ {0} ⊓ twLevi k θ {2} = ⊥ := by
  have hc := commute_twLevi_zero_two (k := k) hθ
  dsimp only [twLevi] at hc ⊢
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton] at hc ⊢
  exact rankOne_inf_rankOne_eq_bot
    (CFSG.LieType.Steinberg.TwistedE6.twistedDatum_isCTGroupDatum θ hθ
      (CFSG.LieType.Steinberg.TwistedE6.iSup_twistedDatum_rootGroup θ hθ))
    (CFSG.LieType.Steinberg.TwistedE6.twistedDatum_steinbergExtras θ hθ)
    (by decide : (0 : Fin (Tag.rank .F4)) ≠ 2) hc

theorem eq_pair_zero_two {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h2 : (2 : Fin (Tag.rank .F4)) ∈ J) : J = {0, 2} := by
  have hsub : ({0, 2} : Finset (Fin (Tag.rank .F4))) ⊆ J := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    exacts [h0, h2]
  have hc : ({0, 2} : Finset (Fin (Tag.rank .F4))).card = 2 := by decide
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc]; exact hJ)).symm

theorem twLevi_le_sup_zero_two {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h2 : (2 : Fin (Tag.rank .F4)) ∈ J) :
    twLevi k θ J ≤ twLevi k θ {0} ⊔ twLevi k θ {2} := by
  dsimp only [twLevi]
  rw [eq_pair_zero_two hJ h0 h2, levi_pair]

end Pair

theorem zero_subset_zero_one : ({0} : Finset (Fin (Tag.rank .F4))) ⊆ {0, 1} := by
  decide

theorem one_subset_zero_one : ({1} : Finset (Fin (Tag.rank .F4))) ⊆ {0, 1} := by
  decide

theorem two_subset_X : ({2} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X.nodes := by
  decide

theorem subset_zero_one_of_not_mem {J : Finset (Fin (Tag.rank .F4))}
    (h2 : (2 : Fin (Tag.rank .F4)) ∉ J) (h3 : (3 : Fin (Tag.rank .F4)) ∉ J) : J ⊆ {0, 1} := by
  intro j hj
  have key : ∀ j : Fin (Tag.rank .F4), j ≠ 2 → j ≠ 3 → j ∈ ({0, 1} : Finset _) := by decide
  exact key j (fun h => h2 (h ▸ hj)) (fun h => h3 (h ▸ hj))

theorem one_subset_nodes_X : ({1} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X.nodes := by
  decide

section Family

variable {k : Type} [Field k] {θ : k →+* k} {G : Type} [Group G]

variable (hθ : ∀ c, θ (θ c) = c) (ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G)
  (ΦL : twLevi k θ {0, 1} →* G)
  (hc2 : ∀ a b, Commute (twLeviRestrict ΦL zero_subset_zero_one a)
    (twLeviRestrict ΦX two_subset_X b))
  (hc3 : ∀ a b, Commute (twLeviRestrict ΦL zero_subset_zero_one a)
    (twLeviRestrict ΦX three_subset_X b))

@[expose] noncomputable def twTwoPairLift2 : ↥(twLevi k θ {0} ⊔ twLevi k θ {2}) →* G :=
  supLift (commute_twLevi_zero_two hθ) (twLevi_zero_inf_two_eq_bot hθ) _ _ hc2

@[expose] noncomputable def twTwoPairLift3 : ↥(twLevi k θ {0} ⊔ twLevi k θ {3}) →* G :=
  supLift (commute_twLevi_zero_three hθ) (twLevi_zero_inf_three_eq_bot hθ) _ _ hc3

@[expose] noncomputable def twTwoFamily (J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}) :
    twLevi k θ J.1 →* G :=
  if h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1 then
    if h2 : (2 : Fin (Tag.rank .F4)) ∈ J.1 then
      (twTwoPairLift2 hθ ΦX ΦL hc2).comp (Subgroup.inclusion (twLevi_le_sup_zero_two J.2 h0 h2))
    else if h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1 then
      (twTwoPairLift3 hθ ΦX ΦL hc3).comp
        (Subgroup.inclusion (twLevi_le_sup_of_mem_of_mem J.2 h0 h3))
    else twLeviRestrict ΦL (subset_zero_one_of_not_mem h2 h3)
  else twLeviRestrict ΦX (subset_nodes_X_of_zero_not_mem h0)

variable {hθ ΦX ΦL hc2 hc3}

theorem twTwoFamily_of_zero_not_mem {J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J.1) (x : twLevi k θ J.1) :
    twTwoFamily hθ ΦX ΦL hc2 hc3 J x = twLeviRestrict ΦX (subset_nodes_X_of_zero_not_mem h0) x := by
  rw [twTwoFamily, dite_eq_right h0]

theorem twTwoFamily_of_zero_two {J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h2 : (2 : Fin (Tag.rank .F4)) ∈ J.1)
    (x : twLevi k θ J.1) :
    twTwoFamily hθ ΦX ΦL hc2 hc3 J x =
      twTwoPairLift2 hθ ΦX ΦL hc2 ⟨x, twLevi_le_sup_zero_two J.2 h0 h2 x.2⟩ := by
  rw [twTwoFamily, dite_eq_left h0, dite_eq_left h2, MonoidHom.comp_apply]
  exact congrArg _ (Subtype.ext (Subgroup.coe_inclusion _ _))

theorem twTwoFamily_of_zero_three {J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h2 : (2 : Fin (Tag.rank .F4)) ∉ J.1)
    (h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1) (x : twLevi k θ J.1) :
    twTwoFamily hθ ΦX ΦL hc2 hc3 J x =
      twTwoPairLift3 hθ ΦX ΦL hc3 ⟨x, twLevi_le_sup_of_mem_of_mem J.2 h0 h3 x.2⟩ := by
  rw [twTwoFamily, dite_eq_left h0, dite_eq_right h2, dite_eq_left h3, MonoidHom.comp_apply]
  exact congrArg _ (Subtype.ext (Subgroup.coe_inclusion _ _))

theorem twTwoFamily_of_zero_one {J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h2 : (2 : Fin (Tag.rank .F4)) ∉ J.1)
    (h3 : (3 : Fin (Tag.rank .F4)) ∉ J.1) (x : twLevi k θ J.1) :
    twTwoFamily hθ ΦX ΦL hc2 hc3 J x = twLeviRestrict ΦL (subset_zero_one_of_not_mem h2 h3) x := by
  rw [twTwoFamily, dite_eq_left h0, dite_eq_right h2, dite_eq_right h3]

theorem twTwoFamily_rankOne_zero (J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2})
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (x : fixedGroup k θ) (hx : x ∈ twLevi k θ {0}) :
    twTwoFamily hθ ΦX ΦL hc2 hc3 J ⟨x, twLevi_singleton_le h0 hx⟩ =
      twLeviRestrict ΦL zero_subset_zero_one ⟨x, hx⟩ := by
  by_cases h2 : (2 : Fin (Tag.rank .F4)) ∈ J.1
  · rw [twTwoFamily_of_zero_two h0 h2]
    exact supLift_apply_left (commute_twLevi_zero_two hθ) (twLevi_zero_inf_two_eq_bot hθ) hc2
      ⟨x, hx⟩
  · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
    · rw [twTwoFamily_of_zero_three h0 h2 h3]
      exact supLift_apply_left (commute_twLevi_zero_three hθ) (twLevi_zero_inf_three_eq_bot hθ)
        hc3 ⟨x, hx⟩
    · rw [twTwoFamily_of_zero_one h0 h2 h3, twLeviRestrict_apply, twLeviRestrict_apply]

theorem twTwoFamily_rankOne_ne
    (hagree : ∀ x : twLevi k θ {1}, twLeviRestrict ΦL one_subset_zero_one x =
      twLeviRestrict ΦX one_subset_nodes_X x)
    (J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}) {i : Fin (Tag.rank .F4)} (hi : i ∈ J.1)
    (hi0 : i ≠ 0) (x : fixedGroup k θ) (hx : x ∈ twLevi k θ {i}) :
    twTwoFamily hθ ΦX ΦL hc2 hc3 J ⟨x, twLevi_singleton_le hi hx⟩ =
      ΦX ⟨x, twLevi_singleton_le (mem_nodes_X_of_ne hi0) hx⟩ := by
  by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
  · by_cases h2 : (2 : Fin (Tag.rank .F4)) ∈ J.1
    · have hJ := eq_pair_zero_two J.2 h0 h2
      have hi2 : i = 2 := by
        rw [hJ, Finset.mem_insert, Finset.mem_singleton] at hi
        exact hi.resolve_left hi0
      subst hi2
      rw [twTwoFamily_of_zero_two h0 h2]
      exact (supLift_apply_right (commute_twLevi_zero_two hθ) (twLevi_zero_inf_two_eq_bot hθ) hc2
        ⟨x, hx⟩).trans (twLeviRestrict_apply _ _ _)
    · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
      · have hJ := eq_pair_zero_three J.2 h0 h3
        have hi3 : i = 3 := by
          rw [hJ, Finset.mem_insert, Finset.mem_singleton] at hi
          exact hi.resolve_left hi0
        subst hi3
        rw [twTwoFamily_of_zero_three h0 h2 h3]
        exact (supLift_apply_right (commute_twLevi_zero_three hθ)
          (twLevi_zero_inf_three_eq_bot hθ) hc3 ⟨x, hx⟩).trans (twLeviRestrict_apply _ _ _)
      · have hi1 : i = 1 := by
          have h := subset_zero_one_of_not_mem h2 h3 hi
          rw [Finset.mem_insert, Finset.mem_singleton] at h
          exact h.resolve_left hi0
        subst hi1
        rw [twTwoFamily_of_zero_one h0 h2 h3, twLeviRestrict_apply]
        have h := hagree ⟨x, hx⟩
        rw [twLeviRestrict_apply, twLeviRestrict_apply] at h
        exact h
  · rw [twTwoFamily_of_zero_not_mem h0, twLeviRestrict_apply]

end Family

section Main

variable {k : Type} [Field k] {θ : k →+* k} {G : Type} [Group G]
  {hθ : ∀ c, θ (θ c) = c} {ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G}
  {ΦL : twLevi k θ {0, 1} →* G}
  {hc2 : ∀ a b, Commute (twLeviRestrict ΦL zero_subset_zero_one a)
    (twLeviRestrict ΦX two_subset_X b)}
  {hc3 : ∀ a b, Commute (twLeviRestrict ΦL zero_subset_zero_one a)
    (twLeviRestrict ΦX three_subset_X b)}

theorem isCompatible_twTwoFamily
    (hagree : ∀ x : twLevi k θ {1}, twLeviRestrict ΦL one_subset_zero_one x =
      twLeviRestrict ΦX one_subset_nodes_X x) :
    ∀ I J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, I.1 ⊆ J.1 →
      ∀ (x : twLevi k θ I.1) (y : twLevi k θ J.1), (x : fixedGroup k θ) = y →
        twTwoFamily hθ ΦX ΦL hc2 hc3 I x = twTwoFamily hθ ΦX ΦL hc2 hc3 J y := by
  refine isCompatible_of_rankOne _
    (fun i => twTwoFamily hθ ΦX ΦL hc2 hc3 ⟨{i}, card_singleton_le_two_F4 i⟩) ?_
  intro J i hi x hx
  by_cases hi0 : i = 0
  · subst hi0
    rw [twTwoFamily_rankOne_zero J hi x hx]
    exact (twTwoFamily_rankOne_zero ⟨{0}, card_singleton_le_two_F4 0⟩
      (Finset.mem_singleton_self 0) x hx).symm
  · rw [twTwoFamily_rankOne_ne hagree J hi hi0 x hx]
    exact (twTwoFamily_rankOne_ne hagree ⟨{i}, card_singleton_le_two_F4 i⟩
      (Finset.mem_singleton_self i) hi0 x hx).symm

theorem conj_twTwoFamily {t : G}
    (hagree : ∀ x : twLevi k θ {1}, twLeviRestrict ΦL one_subset_zero_one x =
      twLeviRestrict ΦX one_subset_nodes_X x)
    (hconjX : ∀ x y : twLevi k θ AmalgamNeighbour.X.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦX x * t⁻¹ = ΦX y)
    (hconjL : ∀ x y : twLevi k θ {0, 1},
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦL x * t⁻¹ = ΦL y)
    (i : Fin (Tag.rank .F4))
    (x y : CFSG.LieType.CurtisTits.levi (twistedDatum k θ).rootGroup {i})
    (hxy : (y : fixedGroup k θ) = sigmaHat θ x) :
    t * twTwoFamily hθ ΦX ΦL hc2 hc3 ⟨{i}, card_singleton_le_two_F4 i⟩ x * t⁻¹ =
      twTwoFamily hθ ΦX ΦL hc2 hc3 ⟨{i}, card_singleton_le_two_F4 i⟩ y := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  by_cases hi0 : i = 0
  · subst hi0
    have h1 := twTwoFamily_rankOne_zero (hθ := hθ) (ΦX := ΦX) (ΦL := ΦL) (hc2 := hc2) (hc3 := hc3)
      ⟨{0}, card_singleton_le_two_F4 0⟩ (Finset.mem_singleton_self 0) x hx
    have h2 := twTwoFamily_rankOne_zero (hθ := hθ) (ΦX := ΦX) (ΦL := ΦL) (hc2 := hc2) (hc3 := hc3)
      ⟨{0}, card_singleton_le_two_F4 0⟩ (Finset.mem_singleton_self 0) y hy
    rw [twLeviRestrict_apply] at h1 h2
    exact (congrArg (fun z => t * z * t⁻¹) h1).trans ((hconjL _ _ hxy).trans h2.symm)
  · have h1 := twTwoFamily_rankOne_ne (hθ := hθ) (hc2 := hc2) (hc3 := hc3) hagree
      ⟨{i}, card_singleton_le_two_F4 i⟩ (Finset.mem_singleton_self i) hi0 x hx
    have h2 := twTwoFamily_rankOne_ne (hθ := hθ) (hc2 := hc2) (hc3 := hc3) hagree
      ⟨{i}, card_singleton_le_two_F4 i⟩ (Finset.mem_singleton_self i) hi0 y hy
    exact (congrArg (fun z => t * z * t⁻¹) h1).trans ((hconjX _ _ hxy).trans h2.symm)

theorem range_twLeviRestrict_le_range {S J : Finset (Fin (Tag.rank .F4))}
    (Φ : twLevi k θ S →* G) (h : J ⊆ S) : (twLeviRestrict Φ h).range ≤ Φ.range := by
  rintro _ ⟨z, rfl⟩
  exact ⟨_, rfl⟩

theorem twTwoFamily_mem_sup (J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2})
    (x : twLevi k θ J.1) : twTwoFamily hθ ΦX ΦL hc2 hc3 J x ∈ ΦX.range ⊔ ΦL.range := by
  by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
  · by_cases h2 : (2 : Fin (Tag.rank .F4)) ∈ J.1
    · rw [twTwoFamily_of_zero_two h0 h2]
      have hr : (twTwoPairLift2 hθ ΦX ΦL hc2).range ≤ ΦX.range ⊔ ΦL.range := by
        rw [twTwoPairLift2, range_supLift]
        exact sup_le (le_sup_of_le_right (range_twLeviRestrict_le_range _ _))
          (le_sup_of_le_left (range_twLeviRestrict_le_range _ _))
      exact hr ⟨_, rfl⟩
    · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
      · rw [twTwoFamily_of_zero_three h0 h2 h3]
        have hr : (twTwoPairLift3 hθ ΦX ΦL hc3).range ≤ ΦX.range ⊔ ΦL.range := by
          rw [twTwoPairLift3, range_supLift]
          exact sup_le (le_sup_of_le_right (range_twLeviRestrict_le_range _ _))
            (le_sup_of_le_left (range_twLeviRestrict_le_range _ _))
        exact hr ⟨_, rfl⟩
      · rw [twTwoFamily_of_zero_one h0 h2 h3]
        exact mem_sup_right (range_twLeviRestrict_le_range _ _ ⟨x, rfl⟩)
  · rw [twTwoFamily_of_zero_not_mem h0]
    exact mem_sup_left (range_twLeviRestrict_le_range _ _ ⟨x, rfl⟩)

theorem twoFamilySpan_twTwoFamily
    (hagree : ∀ x : twLevi k θ {1}, twLeviRestrict ΦL one_subset_zero_one x =
      twLeviRestrict ΦX one_subset_nodes_X x) :
    twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3) = ΦX.range ⊔ ΦL.range := by
  apply le_antisymm
  · refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    exact twTwoFamily_mem_sup J x
  · refine sup_le ?_ ?_
    · have htop : (twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)).comap ΦX = ⊤ :=
        eq_top_of_forall_rankOne _ fun i hi z hz => by
          have hi0 : i ≠ 0 := ne_zero_of_mem_nodes_X hi
          have hmem := mem_twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)
            ⟨{i}, card_singleton_le_two_F4 i⟩ ⟨z, hz⟩
          have h := twTwoFamily_rankOne_ne (hθ := hθ) (hc2 := hc2) (hc3 := hc3) hagree
            ⟨{i}, card_singleton_le_two_F4 i⟩ (Finset.mem_singleton_self i) hi0 z hz
          exact (congrArg (· ∈ twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)) h).mp hmem
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ (twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)).comap ΦX := htop ▸ mem_top x
      exact hx
    · have htop : (twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)).comap ΦL = ⊤ :=
        eq_top_of_forall_rankOne _ fun i hi z hz => by
          rw [Subgroup.mem_comap]
          have hi' : i = 0 ∨ i = 1 := by
            rw [Finset.mem_insert, Finset.mem_singleton] at hi
            exact hi
          rcases hi' with rfl | rfl
          · have hmem := mem_twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)
              ⟨{(0 : Fin (Tag.rank .F4))}, card_singleton_le_two_F4 0⟩ ⟨z, hz⟩
            have h := twTwoFamily_rankOne_zero (hθ := hθ) (ΦX := ΦX) (ΦL := ΦL) (hc2 := hc2)
              (hc3 := hc3) ⟨{0}, card_singleton_le_two_F4 0⟩ (Finset.mem_singleton_self 0) z hz
            exact (congrArg (· ∈ twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3))
              (h.trans (twLeviRestrict_apply _ _ _))).mp hmem
          · have hmem := mem_twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)
              ⟨{(1 : Fin (Tag.rank .F4))}, card_singleton_le_two_F4 1⟩ ⟨z, hz⟩
            have h := twTwoFamily_rankOne_ne (hθ := hθ) (hc2 := hc2) (hc3 := hc3) hagree
              ⟨{1}, card_singleton_le_two_F4 1⟩ (Finset.mem_singleton_self 1) (by decide) z hz
            have ha := hagree ⟨z, hz⟩
            rw [twLeviRestrict_apply, twLeviRestrict_apply] at ha
            exact (congrArg (· ∈ twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3))
              (h.trans ha.symm)).mp hmem
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ (twoFamilySpan (twTwoFamily hθ ΦX ΦL hc2 hc3)).comap ΦL := htop ▸ mem_top x
      exact hx

theorem isTwistedE6TwoFamily_twTwoFamily {t : G}
    (hagree : ∀ x : twLevi k θ {1}, twLeviRestrict ΦL one_subset_zero_one x =
      twLeviRestrict ΦX one_subset_nodes_X x)
    (hconjX : ∀ x y : twLevi k θ AmalgamNeighbour.X.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦX x * t⁻¹ = ΦX y)
    (hconjL : ∀ x y : twLevi k θ {0, 1},
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦL x * t⁻¹ = ΦL y) :
    IsTwistedE6TwoFamily t k θ (twTwoFamily hθ ΦX ΦL hc2 hc3) where
  compatible := fun I J hIJ x y hxy => isCompatible_twTwoFamily hagree I J hIJ x y hxy
  conj := conj_twTwoFamily hagree hconjX hconjL

end Main

end CFSG.SeitzReduction.F4Pilot
