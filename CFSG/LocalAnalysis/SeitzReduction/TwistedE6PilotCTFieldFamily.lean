module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldImagesXCover
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldSL2
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldImagesX

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.LieType.Chevalley.E6GraphLevi (realize unitarySL unitaryTwist)
open CFSG.LieType.Steinberg.Adjoint (iform iform_smul_left iform_smul_right)
open CFSG.SeitzReduction.E6Pilot (adjDatumE6)

local instance twistedE6PilotCTFieldFamilyNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotCTFieldFamilyNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotCTFieldFamilyNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

abbrev e6Set (J : Finset (Fin Tag.E6.rank)) : Set (Fin TwistTag.E6.tag.rank) :=
  (J : Set (Fin Tag.E6.rank))

abbrev e6Node (i : Fin Tag.E6.rank) : Fin TwistTag.E6.tag.rank := i

section Members

variable
  {K : Type} [Field K]

theorem coe_mem_rootSpan_of_mem_levi {J : Finset (Fin (Tag.rank .E6))}
    {x : adjointGroup .E6 K} (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    ((x : ModGL .E6 K) : ModGL TwistTag.E6.tag K) ∈
      rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (e6Set J)) := by
  rw [E6Pilot.levi_adjDatumE6_eq, mem_subgroupOf] at hx
  exact hx

@[expose] noncomputable def leviToRootSpan (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →*
      rootSpan TwistTag.E6.tag K
        (F4Pilot.signedSimpleRoots (e6Set J)) where
  toFun x := ⟨(((x : adjointGroup .E6 K) : ModGL .E6 K) : ModGL TwistTag.E6.tag K),
    coe_mem_rootSpan_of_mem_levi x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_leviToRootSpan (J : Finset (Fin (Tag.rank .E6)))
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    ((leviToRootSpan J x : rootSpan TwistTag.E6.tag K _) : ModGL TwistTag.E6.tag K) =
      (((x : adjointGroup .E6 K) : ModGL .E6 K) : ModGL TwistTag.E6.tag K) :=
  rfl

theorem rootSpan_signedSimpleRoots_le_subsystemGroup {J : Finset (Fin TwistTag.E6.tag.rank)}
    {S : Set (Fin TwistTag.E6.tag.rank)} (hJS : ∀ j ∈ J, j ∈ S) :
    rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (J : Set (Fin TwistTag.E6.tag.rank))) ≤
      subsystemGroup TwistTag.E6.tag K S := by
  rw [← F4Pilot.closure_xUnit_yUnit_eq_rootSpan]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨j, hj, c, h⟩
  exact ⟨j, hJS j hj, c, h⟩

theorem eq_one_of_mem_levi_empty {x : adjointGroup .E6 K}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup ∅) : x = 1 := by
  have h : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup ∅ = ⊥ := by
    simp [CFSG.LieType.CurtisTits.levi]
  rw [h, mem_bot] at hx
  exact hx

end Members

theorem iform_one_check : ∀ m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank)),
    iform (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) (Pi.single m 1) = 0 := by
  decide

theorem mem_zero_two_four_five {m : Fin Tag.E6.rank} (h1 : m ≠ 1) (h3 : m ≠ 3) :
    m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank)) := by
  revert m
  decide

section Pair

variable
  {K : Type} [Field K]

theorem commute_levi_one {m : Fin Tag.E6.rank}
    (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) :
    ∀ a ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1},
      ∀ b ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {m}, Commute a b := by
  intro a ha b hb
  have h0 : iform (Pi.single (e6Node 1) 1 : Fin TwistTag.E6.tag.rank → ℤ)
      (Pi.single (e6Node m) 1) = 0 := iform_one_check m hm
  have hneg : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, -v = (-1 : ℤ) • v :=
    fun v => (neg_one_smul ℤ v).symm
  have hc := forall_commute_rootSpan_of_iform (K := K)
    (S₁ := F4Pilot.signedSimpleRoots (e6Set {1}))
    (S₂ := F4Pilot.signedSimpleRoots (e6Set {m}))
    (fun α hα β hβ => by
      obtain ⟨i, hi, hαi⟩ := hα
      obtain ⟨j, hj, hβj⟩ := hβ
      have hi' : i = e6Node 1 := Finset.mem_singleton.1 (Finset.mem_coe.1 hi)
      have hj' : j = e6Node m := Finset.mem_singleton.1 (Finset.mem_coe.1 hj)
      rw [hi'] at hαi
      rw [hj'] at hβj
      refine ⟨F4Pilot.isRoot_of_mem_signedSimpleRoots ⟨i, hi, hi' ▸ hαi⟩,
        F4Pilot.isRoot_of_mem_signedSimpleRoots ⟨j, hj, hj' ▸ hβj⟩, ?_⟩
      rcases hαi with rfl | rfl <;> rcases hβj with rfl | rfl
      · exact h0
      · rw [hneg, iform_smul_right, h0, mul_zero]
      · rw [hneg, iform_smul_left, h0, mul_zero]
      · rw [hneg, hneg, iform_smul_left, iform_smul_right, h0, mul_zero, mul_zero])
    _ (coe_mem_rootSpan_of_mem_levi ha) _ (coe_mem_rootSpan_of_mem_levi hb)
  exact Subtype.ext hc.eq

theorem rootSpan_singleton_eq_range (i : Fin Tag.E6.rank) :
    rootSpan TwistTag.E6.tag K (F4Pilot.signedSimpleRoots (e6Set {i})) =
      (rankOneHom TwistTag.E6 K (e6Node i)).range := by
  rw [rankOneHom_range, ← F4Pilot.closure_xUnit_yUnit_eq_rootSpan]
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, c, h | h⟩
    · have hji : j = e6Node i := Finset.mem_singleton.1 (Finset.mem_coe.1 hj)
      subst hji
      exact Or.inl ⟨c, h.symm⟩
    · have hji : j = e6Node i := Finset.mem_singleton.1 (Finset.mem_coe.1 hj)
      subst hji
      exact Or.inr ⟨c, h.symm⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨e6Node i, Finset.mem_coe.2 (Finset.mem_singleton_self _), c, Or.inl rfl⟩
    · exact ⟨e6Node i, Finset.mem_coe.2 (Finset.mem_singleton_self _), c, Or.inr rfl⟩

theorem levi_one_inf_eq_bot [CharP K 2] {m : Fin Tag.E6.rank}
    (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊓
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {m} = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hz1, hzm⟩ := mem_inf.1 hz
  have hzr := coe_mem_rootSpan_of_mem_levi hz1
  rw [rootSpan_singleton_eq_range] at hzr
  obtain ⟨g, hg⟩ := hzr
  have hinj := rankOneHom_injective_of_charTwo (K := K) TwistTag.E6 (e6Node 1)
  have hcomm : ∀ h, Commute g h := by
    intro h
    have hmem : rankOneHom TwistTag.E6 K (e6Node 1) h ∈ rootSpan TwistTag.E6.tag K
        (F4Pilot.signedSimpleRoots (e6Set {1})) := by
      rw [rootSpan_singleton_eq_range]
      exact ⟨h, rfl⟩
    have hadj : rankOneHom TwistTag.E6 K (e6Node 1) h ∈ adjointGroup .E6 K :=
      E6Pilot.rootSpan_le_adjointGroup_E6 _ hmem
    have hlevi : (⟨_, hadj⟩ : adjointGroup .E6 K) ∈
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} := by
      rw [E6Pilot.levi_adjDatumE6_eq, mem_subgroupOf]
      exact hmem
    have hc := (commute_levi_one hm _ hlevi z hzm).symm
    have hc' := congrArg Subtype.val hc.eq
    have hc'' : rankOneHom TwistTag.E6 K (e6Node 1) (g * h) =
        rankOneHom TwistTag.E6 K (e6Node 1) (h * g) := by
      rw [map_mul, map_mul, hg]
      exact hc'
    exact hinj hc''
  have hgc : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    mem_center_iff.2 fun h => (hcomm h).symm.eq
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hgc
  have hr1 : r = 1 := by
    rw [Fintype.card_fin, sq] at hr
    exact E8Pilot.eq_one_of_mul_self_eq_one_of_charTwo hr
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [← hrg, hr1, map_one]
    rfl
  rw [mem_bot]
  apply Subtype.ext
  change (z : ModGL .E6 K) = 1
  rw [← hg, hg1, map_one]
  rfl

end Pair

theorem eq_pair_of_one_mem {J : Finset (Fin Tag.E6.rank)} (hJ : J.card ≤ 2)
    {m : Fin Tag.E6.rank} (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) (h1 : 1 ∈ J)
    (hmJ : m ∈ J) : J = {1, m} := by
  have key : ∀ m : Fin Tag.E6.rank, m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank)) →
      (1 : Fin Tag.E6.rank) ≠ m := by decide
  exact E6Pilot.eq_pair_of_card_le_two hJ (key m hm) h1 hmJ

section Family

variable
  {K : Type} [Field K] [CharP K 2] {G : Type} [Group G]

variable (h2 : (2 : K) = 0) (Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G)
  (ΦY : subsystemGroup TwistTag.E6.tag K setD →* G)

@[expose] noncomputable def xFam (J : Finset (Fin Tag.E6.rank)) (h1 : (1 : Fin Tag.E6.rank) ∉ J)
    (hJ2 : J.card ≤ 2) : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* G :=
  Φ.comp ((xSection h2 J h1 hJ2).comp (leviToRootSpan J))

@[expose] noncomputable def yFam (J : Finset (Fin Tag.E6.rank)) (hJ : ∀ j ∈ J, e6Node j ∈ setD) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* G :=
  ΦY.comp ((Subgroup.inclusion (rootSpan_signedSimpleRoots_le_subsystemGroup hJ)).comp
    (leviToRootSpan J))

theorem one_mem_setD : ∀ j ∈ ({1} : Finset (Fin Tag.E6.rank)), e6Node j ∈ setD := by
  intro j hj
  rw [Finset.mem_singleton.1 hj]
  exact Or.inl rfl

theorem not_one_mem_singleton {m : Fin Tag.E6.rank}
    (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) :
    (1 : Fin Tag.E6.rank) ∉ ({m} : Finset (Fin Tag.E6.rank)) := by
  rw [Finset.mem_singleton]
  intro h
  rw [← h] at hm
  exact absurd hm (by decide)

@[expose] noncomputable def pairFam {m : Fin Tag.E6.rank}
    (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank)))
    (hc : ∀ a b, Commute (yFam ΦY {1} one_mem_setD a)
      (xFam h2 Φ {m} (not_one_mem_singleton hm) (by simp) b)) :
    ↥(CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {m}) →* G :=
  F4Pilot.supLift (commute_levi_one hm) (levi_one_inf_eq_bot hm) _ _ hc

end Family

theorem mem_setD_of_not_exists {J : Finset (Fin Tag.E6.rank)}
    (hm : ¬∃ m ∈ J, m ≠ 1 ∧ m ≠ 3) : ∀ j ∈ J, e6Node j ∈ setD := by
  intro j hj
  push Not at hm
  have key : ∀ j : Fin Tag.E6.rank, (j ≠ 1 → j = 3) → (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) := by
    decide
  exact key j (hm j hj)

theorem mem_of_exists_other {J : Finset (Fin Tag.E6.rank)} (hm : ∃ m ∈ J, m ≠ 1 ∧ m ≠ 3) :
    hm.choose ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank)) :=
  mem_zero_two_four_five hm.choose_spec.2.1 hm.choose_spec.2.2

section FamilyDef

variable
  {K : Type} [Field K] [CharP K 2] {G : Type} [Group G]

omit [CharP K 2] in
theorem levi_le_pair_of_exists {J : Finset (Fin Tag.E6.rank)} (hJ : J.card ≤ 2)
    (h1 : (1 : Fin Tag.E6.rank) ∈ J) (hm : ∃ m ∈ J, m ≠ 1 ∧ m ≠ 3) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} ⊔
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {hm.choose} := by
  have h := eq_pair_of_one_mem hJ (mem_of_exists_other hm) h1 hm.choose_spec.1
  calc CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J =
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1, hm.choose} := by
          exact congrArg _ h
    _ = _ := F4Pilot.levi_pair _ _ _
    _ ≤ _ := le_rfl

variable (h2 : (2 : K) = 0) (Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G)
  (ΦY : subsystemGroup TwistTag.E6.tag K setD →* G)
  (hc : ∀ (m : Fin Tag.E6.rank) (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) (a b),
    Commute (yFam ΦY {1} one_mem_setD a) (xFam h2 Φ {m} (not_one_mem_singleton hm) (by simp) b))

@[expose] noncomputable def fieldFamily2E6
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    (adjDatumE6 K).leviAmalgam J →* G :=
  if h1 : (1 : Fin Tag.E6.rank) ∈ J.1 then
    if hm : ∃ m ∈ J.1, m ≠ 1 ∧ m ≠ 3 then
      (pairFam h2 Φ ΦY (mem_of_exists_other hm) (hc _ (mem_of_exists_other hm))).comp
        (Subgroup.inclusion (levi_le_pair_of_exists J.2 h1 hm))
    else yFam ΦY J.1 (mem_setD_of_not_exists hm)
  else xFam h2 Φ J.1 h1 J.2

variable {h2 Φ ΦY hc}

theorem fieldFamily2E6_of_not_mem {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin Tag.E6.rank) ∉ J.1) (x : (adjDatumE6 K).leviAmalgam J) :
    fieldFamily2E6 h2 Φ ΦY hc J x = xFam h2 Φ J.1 h1 J.2 x := by
  rw [fieldFamily2E6, dite_eq_right h1]

theorem fieldFamily2E6_of_Y {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin Tag.E6.rank) ∈ J.1) (hm : ¬∃ m ∈ J.1, m ≠ 1 ∧ m ≠ 3)
    (x : (adjDatumE6 K).leviAmalgam J) :
    fieldFamily2E6 h2 Φ ΦY hc J x = yFam ΦY J.1 (mem_setD_of_not_exists hm) x := by
  rw [fieldFamily2E6, dite_eq_left h1, dite_eq_right hm]

theorem fieldFamily2E6_of_pair {J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}}
    (h1 : (1 : Fin Tag.E6.rank) ∈ J.1) (hm : ∃ m ∈ J.1, m ≠ 1 ∧ m ≠ 3)
    (x : (adjDatumE6 K).leviAmalgam J) :
    fieldFamily2E6 h2 Φ ΦY hc J x = pairFam h2 Φ ΦY (mem_of_exists_other hm)
      (hc _ (mem_of_exists_other hm)) ⟨x, levi_le_pair_of_exists J.2 h1 hm x.2⟩ := by
  rw [fieldFamily2E6, dite_eq_left h1, dite_eq_left hm]
  rfl

end FamilyDef

section Compat

variable
  {K : Type} [Field K] [CharP K 2] {G : Type} [Group G]

theorem xFam_compat (h2 : (2 : K) = 0) (Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G)
    {t₀ : Kˣ} (ht₀ : t₀ ^ 2 ≠ 1) {I J : Finset (Fin Tag.E6.rank)} (hIJ : I ⊆ J)
    (h1J : (1 : Fin Tag.E6.rank) ∉ J) (hJ2 : J.card ≤ 2)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    (hxy : (x : adjointGroup .E6 K) = y) :
    xFam h2 Φ I (fun h => h1J (hIJ h)) ((Finset.card_le_card hIJ).trans hJ2) x =
      xFam h2 Φ J h1J hJ2 y := by
  have hy : leviToRootSpan J y =
      Subgroup.inclusion (rootSpan_signedSimpleRoots_mono hIJ) (leviToRootSpan I x) :=
    Subtype.ext (congrArg (fun z : adjointGroup .E6 K => (z : ModGL .E6 K)) hxy.symm)
  change Φ (xSection h2 I (fun h => h1J (hIJ h)) ((Finset.card_le_card hIJ).trans hJ2)
      (leviToRootSpan I x)) = Φ (xSection h2 J h1J hJ2 (leviToRootSpan J y))
  rw [hy]
  exact congrArg Φ (xSection_compat h2 ht₀ (I := I) (J := J) hIJ h1J hJ2 (leviToRootSpan I x)).symm

theorem yFam_compat (ΦY : subsystemGroup TwistTag.E6.tag K setD →* G)
    {I J : Finset (Fin Tag.E6.rank)} (hI : ∀ j ∈ I, e6Node j ∈ setD)
    (hJ : ∀ j ∈ J, e6Node j ∈ setD)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    (hxy : (x : adjointGroup .E6 K) = y) : yFam ΦY I hI x = yFam ΦY J hJ y :=
  congrArg ΦY (Subtype.ext (congrArg (fun z : adjointGroup .E6 K => (z : ModGL .E6 K)) hxy))

theorem three_mem_setD : ∀ j ∈ ({3} : Finset (Fin Tag.E6.rank)), e6Node j ∈ setD := by
  intro j hj
  rw [Finset.mem_singleton.1 hj]
  exact Or.inr (Or.inr (Or.inl rfl))

theorem not_one_mem_three : (1 : Fin Tag.E6.rank) ∉ ({3} : Finset (Fin Tag.E6.rank)) := by
  decide

variable {h2 : (2 : K) = 0} {Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G}
  {ΦY : subsystemGroup TwistTag.E6.tag K setD →* G}
  {hc : ∀ (m : Fin Tag.E6.rank) (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) (a b),
    Commute (yFam ΦY {1} one_mem_setD a) (xFam h2 Φ {m} (not_one_mem_singleton hm) (by simp) b)}

theorem isCompatible_fieldFamily2E6 {t₀ : Kˣ} (ht₀ : t₀ ^ 2 ≠ 1)
    (htw : ∀ x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {3},
      yFam ΦY {3} three_mem_setD x = xFam h2 Φ {3} not_one_mem_three (by simp) x) :
    IsCompatible (adjDatumE6 K).leviAmalgam (fieldFamily2E6 h2 Φ ΦY hc) := by
  intro I J hIJ x y hxy
  by_cases hIJeq : I = J
  · subst hIJeq
    rw [show x = y from Subtype.ext hxy]
  have hsub : (I.1 : Finset (Fin Tag.E6.rank)) ⊆ J.1 := hIJ
  by_cases h1J : (1 : Fin Tag.E6.rank) ∈ J.1
  · by_cases hmJ : ∃ m ∈ J.1, m ≠ 1 ∧ m ≠ 3
    ·
      have hm := mem_of_exists_other hmJ
      have hJeq := eq_pair_of_one_mem J.2 hm h1J hmJ.choose_spec.1
      rw [fieldFamily2E6_of_pair h1J hmJ]
      by_cases h1I : (1 : Fin Tag.E6.rank) ∈ I.1
      · have hmI : hmJ.choose ∉ I.1 := fun h =>
          hIJeq (Subtype.ext ((eq_pair_of_one_mem I.2 hm h1I h).trans hJeq.symm))
        have hI1 : I.1 ⊆ {1} := fun a ha => by
          have h3 := hsub ha
          rw [hJeq, Finset.mem_insert, Finset.mem_singleton] at h3
          rcases h3 with h3 | h3
          · rw [h3]
            exact Finset.mem_singleton_self _
          · exact absurd (h3 ▸ ha) hmI
        have hnI : ¬∃ m' ∈ I.1, m' ≠ 1 ∧ m' ≠ 3 := fun ⟨m', hm', h1', _⟩ =>
          h1' (Finset.mem_singleton.1 (hI1 hm'))
        rw [fieldFamily2E6_of_Y h1I hnI]
        have hy1 : (y : adjointGroup .E6 K) ∈
            CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} :=
          hxy ▸ CFSG.LieType.CurtisTits.levi_mono _ hI1 x.2
        have e := F4Pilot.supLift_apply_left (commute_levi_one hm) (levi_one_inf_eq_bot hm)
          (hc _ hm) (⟨_, hy1⟩ : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1})
        exact (yFam_compat ΦY _ one_mem_setD x ⟨_, hy1⟩ hxy).trans e.symm
      · have hIm : I.1 ⊆ {hmJ.choose} := fun a ha => by
          have h3 := hsub ha
          rw [hJeq, Finset.mem_insert] at h3
          rcases h3 with h3 | h3
          · exact absurd (h3 ▸ ha) h1I
          · exact h3
        rw [fieldFamily2E6_of_not_mem h1I]
        have hym : (y : adjointGroup .E6 K) ∈
            CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {hmJ.choose} :=
          hxy ▸ CFSG.LieType.CurtisTits.levi_mono _ hIm x.2
        have e := F4Pilot.supLift_apply_right (commute_levi_one hm) (levi_one_inf_eq_bot hm)
          (hc _ hm) (⟨_, hym⟩ : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {hmJ.choose})
        exact (xFam_compat h2 Φ ht₀ hIm (not_one_mem_singleton hm) (by simp) x ⟨_, hym⟩ hxy).trans
          e.symm
    ·
      rw [fieldFamily2E6_of_Y h1J hmJ]
      by_cases h1I : (1 : Fin Tag.E6.rank) ∈ I.1
      · have hnI : ¬∃ m' ∈ I.1, m' ≠ 1 ∧ m' ≠ 3 := fun ⟨m', hm', h⟩ => hmJ ⟨m', hsub hm', h⟩
        rw [fieldFamily2E6_of_Y h1I hnI]
        exact yFam_compat ΦY _ _ x y hxy
      · rw [fieldFamily2E6_of_not_mem h1I]
        have hI3 : I.1 ⊆ {3} := fun a ha => by
          by_contra h3
          exact hmJ ⟨a, hsub ha, fun h => h1I (h ▸ ha),
            fun h => h3 (h ▸ Finset.mem_singleton_self _)⟩
        have hy3 : (y : adjointGroup .E6 K) ∈
            CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {3} :=
          hxy ▸ CFSG.LieType.CurtisTits.levi_mono _ hI3 x.2
        rw [xFam_compat h2 Φ ht₀ hI3 not_one_mem_three (by simp) x ⟨_, hy3⟩ hxy, ← htw ⟨_, hy3⟩]
        exact yFam_compat ΦY _ _ _ y rfl
  ·
    have h1I : (1 : Fin Tag.E6.rank) ∉ I.1 := fun h => h1J (hsub h)
    rw [fieldFamily2E6_of_not_mem h1J, fieldFamily2E6_of_not_mem h1I]
    exact xFam_compat h2 Φ ht₀ hsub h1J J.2 x y hxy

end Compat

end CFSG.SeitzReduction.TwistedE6Pilot
