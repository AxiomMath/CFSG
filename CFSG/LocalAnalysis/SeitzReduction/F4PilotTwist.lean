module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeExists

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotTwistNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Twist


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

variable (K) in
theorem finite_levi (N : AmalgamNeighbour) : Finite (N.levi K) :=
  have : Finite (ModGL .F4 K) := finite_modGL
  inferInstance


@[expose] noncomputable def leviEntrywiseEquiv (ρ : K ≃+* K) (N : AmalgamNeighbour) :
    N.levi K ≃* N.levi K :=
  have := finite_levi K N
  MulEquiv.ofBijective (leviBaseChange (ρ : K →+* K) N)
    ⟨leviBaseChange_injective _ N, Finite.surjective_of_injective (leviBaseChange_injective _ N)⟩

theorem coe_leviEntrywiseEquiv (ρ : K ≃+* K) (N : AmalgamNeighbour) (x : N.levi K) :
    (((leviEntrywiseEquiv ρ N x : N.levi K) : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (ρ : K →+* K) ((x : adjointGroup .F4 K) : ModGL .F4 K) :=
  rfl

@[expose] noncomputable def FieldNeighbourIso.twist {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    FieldNeighbourIso σ e N where
  Φ := (leviEntrywiseEquiv ρ N).trans h.Φ
  fix x := by
    have hx : leviEntrywiseEquiv ρ N (leviInclusion σ N x) = leviInclusion σ N x := by
      refine Subtype.ext (Subtype.ext ?_)
      have hcomp : (ρ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
        RingHom.ext fun c => hρ c
      rw [coe_leviEntrywiseEquiv, coe_leviInclusion, baseChangeGL_baseChangeGL, hcomp]
    rw [MulEquiv.trans_apply, hx]
    exact h.fix x

theorem FieldNeighbourIso.twist_apply {N : AmalgamNeighbour} (h : FieldNeighbourIso σ e N)
    (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) (x : N.levi K) :
    (h.twist ρ hρ).Φ x = h.Φ (leviEntrywiseEquiv ρ N x) :=
  rfl

end Twist

section Restrict


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

@[expose] noncomputable def FieldNeighbourIso.restrict {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J →* G :=
  (neighbourCore e N).subtype.comp
    (h.Φ.toMonoidHom.comp (Subgroup.inclusion (levi_le_neighbourLevi hJ)))

theorem FieldNeighbourIso.restrict_apply {N : AmalgamNeighbour} (h : FieldNeighbourIso σ e N)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    h.restrict hJ x = (h.Φ ⟨x, levi_le_neighbourLevi hJ x.2⟩ : G) :=
  rfl

theorem FieldNeighbourIso.restrict_injective {N : AmalgamNeighbour} (h : FieldNeighbourIso σ e N)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) : Function.Injective (h.restrict hJ) :=
  Subtype.val_injective.comp (h.Φ.injective.comp (Subgroup.inclusion_injective _))

theorem FieldNeighbourIso.restrict_eq_of_coe_eq {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) {I J : Finset (Fin (Tag.rank .F4))} (hI : I ⊆ N.nodes)
    (hJ : J ⊆ N.nodes) (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : (x : adjointGroup .F4 K) = y) : h.restrict hI x = h.restrict hJ y := by
  rw [h.restrict_apply, h.restrict_apply]
  exact congrArg (fun z => (h.Φ z : G)) (Subtype.ext hxy)

theorem FieldNeighbourIso.commute_restrict {N : AmalgamNeighbour} (h : FieldNeighbourIso σ e N)
    {I J : Finset (Fin (Tag.rank .F4))} (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : Commute (x : adjointGroup .F4 K) y) : Commute (h.restrict hI x) (h.restrict hJ y) := by
  rw [h.restrict_apply, h.restrict_apply]
  have hc : Commute (⟨x, levi_le_neighbourLevi hI x.2⟩ : N.levi K)
      ⟨y, levi_le_neighbourLevi hJ y.2⟩ := Subtype.ext hxy.eq
  exact (hc.map h.Φ).map (neighbourCore e N).subtype

theorem exists_levi_baseChangeGL {k : Type} [Field k] (ι : k →+* K)
    {J : Finset (Fin (Tag.rank .F4))} {x : adjointGroup .F4 k}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum k).rootGroup J) :
    ∃ y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J,
      ((y : adjointGroup .F4 K) : ModGL .F4 K) = baseChangeGL ι (x : ModGL .F4 k) := by
  rw [levi_f4Datum_eq, mem_subgroupOf] at hx
  have h := map_rootSpan_baseChangeGL_le ι (amalgamRoots J) ⟨_, hx, rfl⟩
  refine ⟨⟨⟨_, rootSpan_le_adjointGroup_F4 _ h⟩, ?_⟩, rfl⟩
  rw [levi_f4Datum_eq, mem_subgroupOf]
  exact h

theorem FieldNeighbourIso.restrict_fix {N : AmalgamNeighbour} (h : FieldNeighbourIso σ e N)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) {x : adjointGroup .F4 (fixSubfield σ)}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup J)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .F4 (fixSubfield σ))) :
    h.restrict hJ y = ((e.symm x : L) : G) := by
  have hxN : x ∈ N.levi (fixSubfield σ) := levi_le_neighbourLevi hJ hx
  have h1 : (⟨y, levi_le_neighbourLevi hJ y.2⟩ : N.levi K) = leviInclusion σ N ⟨x, hxN⟩ :=
    Subtype.ext (Subtype.ext (by rw [coe_leviInclusion]; exact hxy))
  rw [h.restrict_apply, h1]
  exact h.fix ⟨x, hxN⟩

end Restrict

section Range


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem FieldNeighbourIso.range_restrict {N : AmalgamNeighbour} (h : FieldNeighbourIso σ e N)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) : (h.restrict hJ).range = pieceCore e J := by
  rw [← h.map_leviPiece hq hJ hJ2]
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨h.Φ ⟨x, levi_le_neighbourLevi hJ x.2⟩,
      ⟨⟨x, levi_le_neighbourLevi hJ x.2⟩, ?_, rfl⟩, rfl⟩
    have hx : (x : adjointGroup .F4 K) ∈
        (rootSpan .F4 K (amalgamRoots J)).subgroupOf (adjointGroup .F4 K) := by
      rw [← levi_f4Datum_eq]
      exact x.2
    exact mem_leviPiece.2 hx
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hy' : (y : adjointGroup .F4 K) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J := by
      rw [levi_f4Datum_eq, mem_subgroupOf]
      exact mem_leviPiece.1 hy
    exact ⟨⟨y, hy'⟩, rfl⟩

end Range

theorem one_two_subset_X : ({1, 2} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X.nodes := by
  decide

theorem one_two_subset_Y : ({1, 2} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.Y.nodes := by
  decide

section Agree


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem exists_twist_restrict_eq (hX : FieldNeighbourIso σ e .X) (hY : FieldNeighbourIso σ e .Y)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, ∃ hρ : ∀ c : fixSubfield σ, ρ c = c,
      ∀ x, hX.restrict one_two_subset_X x = (hY.twist ρ hρ).restrict one_two_subset_Y x := by
  have hB : B2Levi K ≤ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} :=
    levi_one_two_eq_B2Levi.ge
  set f₁ := (hX.restrict one_two_subset_X).comp (Subgroup.inclusion hB) with hf₁
  set f₂ := (hY.restrict one_two_subset_Y).comp (Subgroup.inclusion hB) with hf₂
  have hinc : (Subgroup.inclusion hB).range = ⊤ :=
    MonoidHom.range_eq_top.2 fun z => ⟨⟨(z : adjointGroup .F4 K), levi_one_two_eq_B2Levi.le z.2⟩,
      rfl⟩
  have hr : f₁.range = f₂.range := by
    rw [hf₁, hf₂, MonoidHom.range_comp, MonoidHom.range_comp, hinc, ← MonoidHom.range_eq_map,
      ← MonoidHom.range_eq_map, hX.range_restrict hq one_two_subset_X (by decide),
      hY.range_restrict hq one_two_subset_Y (by decide)]
  have hfix : ∀ (x : B2Levi (fixSubfield σ)) (y : B2Levi K),
      ((y : adjointGroup .F4 K) : ModGL .F4 K) = baseChangeGL (fixSubfield σ).subtype
        ((x : adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) → f₁ y = f₂ y := by
    intro x y hxy
    have hx : (x : adjointGroup .F4 (fixSubfield σ)) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {1, 2} := by
      rw [levi_one_two_eq_B2Levi]
      exact x.2
    change hX.restrict one_two_subset_X (Subgroup.inclusion hB y) =
      hY.restrict one_two_subset_Y (Subgroup.inclusion hB y)
    rw [hX.restrict_fix one_two_subset_X hx _ hxy, hY.restrict_fix one_two_subset_Y hx _ hxy]
  obtain ⟨ρ, hρ, hρf⟩ := exists_ringEquiv_of_injective_of_range_eq (fixSubfield σ).subtype
    ((hX.restrict_injective one_two_subset_X).comp (Subgroup.inclusion_injective hB))
    ((hY.restrict_injective one_two_subset_Y).comp (Subgroup.inclusion_injective hB)) hr hfix
  have hρ' : ∀ c : fixSubfield σ, ρ c = c := hρ
  refine ⟨ρ, hρ', fun x => ?_⟩
  have hxB : (x : adjointGroup .F4 K) ∈ B2Levi K := (levi_one_two_eq_B2Levi (K := K)).le x.2
  have hxP : (x : adjointGroup .F4 K) ∈ AmalgamNeighbour.Y.levi K :=
    levi_le_neighbourLevi one_two_subset_Y x.2
  have hy'B : ((leviEntrywiseEquiv ρ .Y ⟨x, hxP⟩ : AmalgamNeighbour.Y.levi K) :
      adjointGroup .F4 K) ∈ B2Levi K := by
    rw [mem_B2Levi_iff, coe_leviEntrywiseEquiv]
    exact map_rootSpan_baseChangeGL_le (ρ : K →+* K) b2LeviRoots ⟨_, mem_B2Levi_iff.1 hxB, rfl⟩
  have h1 := hρf ⟨x, hxB⟩ ⟨_, hy'B⟩ (coe_leviEntrywiseEquiv ρ .Y ⟨x, hxP⟩)
  change hX.restrict one_two_subset_X (Subgroup.inclusion hB ⟨x, hxB⟩) =
    hY.restrict one_two_subset_Y (Subgroup.inclusion hB ⟨_, hy'B⟩) at h1
  rw [show Subgroup.inclusion hB ⟨x, hxB⟩ = x from rfl] at h1
  rw [h1, hY.restrict_apply, (hY.twist ρ hρ').restrict_apply, FieldNeighbourIso.twist_apply]
  rfl

end Agree

theorem zero_subset_Y : ({0} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.Y.nodes := by
  decide

theorem three_subset_X : ({3} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X.nodes := by
  decide

theorem zero_subset_X' : ({0} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X'.nodes := by
  decide

theorem three_subset_X' : ({3} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X'.nodes := by
  decide

theorem zero_three_subset_X' :
    ({0, 3} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X'.nodes := by
  decide

theorem subset_nodes_X_of_zero_not_mem {J : Finset (Fin (Tag.rank .F4))}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J) : J ⊆ AmalgamNeighbour.X.nodes :=
  fun _ hj => mem_nodes_X_of_ne fun h => h0 (h ▸ hj)

theorem subset_nodes_Y_of_three_not_mem {J : Finset (Fin (Tag.rank .F4))}
    (h3 : (3 : Fin (Tag.rank .F4)) ∉ J) : J ⊆ AmalgamNeighbour.Y.nodes :=
  fun _ hj => mem_nodes_Y_of_ne fun h => h3 (h ▸ hj)

theorem subset_one_two_of_not_mem {I : Finset (Fin (Tag.rank .F4))}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ I) (h3 : (3 : Fin (Tag.rank .F4)) ∉ I) : I ⊆ {1, 2} := by
  intro a ha
  rcases fin_F4_cases a with rfl | rfl | rfl | rfl
  · exact absurd ha h0
  · decide
  · decide
  · exact absurd ha h3

section Family


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem levi_le_sup_of_mem_of_mem {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J ≤
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} := by
  rw [eq_pair_zero_three hJ h0 h3, levi_pair]

variable (hX : FieldNeighbourIso σ e .X) (hY : FieldNeighbourIso σ e .Y)
  (hcomm : ∀ a b, Commute (hY.restrict zero_subset_Y a) (hX.restrict three_subset_X b))

@[expose] noncomputable def fieldPairLift :
    ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) →* G :=
  supLift commute_levi_zero_three levi_zero_inf_levi_three_eq_bot (hY.restrict zero_subset_Y)
    (hX.restrict three_subset_X) hcomm

theorem fieldPairLift_of_mem_left
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}) :
    fieldPairLift hX hY hcomm z = hY.restrict zero_subset_Y ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_left commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm ⟨z, hz⟩

theorem fieldPairLift_of_mem_right
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) :
    fieldPairLift hX hY hcomm z = hX.restrict three_subset_X ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_right commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm ⟨z, hz⟩

@[expose] noncomputable def fieldFamily
    (J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}) :
    (Adjoint.f4Datum K).leviAmalgam J →* G :=
  if h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1 then
    if h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1 then
      (fieldPairLift hX hY hcomm).comp (Subgroup.inclusion (levi_le_sup_of_mem_of_mem J.2 h0 h3))
    else hY.restrict (subset_nodes_Y_of_three_not_mem h3)
  else hX.restrict (subset_nodes_X_of_zero_not_mem h0)

variable {hX hY hcomm}

theorem fieldFamily_of_zero_not_mem {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J.1) (x : (Adjoint.f4Datum K).leviAmalgam J) :
    fieldFamily hX hY hcomm J x = hX.restrict (subset_nodes_X_of_zero_not_mem h0) x := by
  rw [fieldFamily, dite_eq_right h0]

theorem fieldFamily_of_three_not_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∉ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    fieldFamily hX hY hcomm J x = hY.restrict (subset_nodes_Y_of_three_not_mem h3) x := by
  rw [fieldFamily, dite_eq_left h0, dite_eq_right h3]

theorem fieldFamily_of_mem_of_mem {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    fieldFamily hX hY hcomm J x =
      fieldPairLift hX hY hcomm ⟨x, levi_le_sup_of_mem_of_mem J.2 h0 h3 x.2⟩ := by
  rw [fieldFamily, dite_eq_left h0, dite_eq_left h3]
  rfl

theorem isCompatible_fieldFamily
    (hagree : ∀ x, hX.restrict one_two_subset_X x = hY.restrict one_two_subset_Y x) :
    CFSG.LieType.CurtisTits.IsCompatible (Adjoint.f4Datum K).leviAmalgam
      (fieldFamily hX hY hcomm) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ j.1 := hij
  by_cases h0j : (0 : Fin (Tag.rank .F4)) ∈ j.1
  · by_cases h3j : (3 : Fin (Tag.rank .F4)) ∈ j.1
    · have hj : (j.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three j.2 h0j h3j
      rw [fieldFamily_of_mem_of_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · by_cases h3i : (3 : Fin (Tag.rank .F4)) ∈ i.1
        · rw [fieldFamily_of_mem_of_mem h0i h3i]
          exact congrArg (fieldPairLift hX hY hcomm) (Subtype.ext hxy)
        · have hi0 : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ {0} := by
            intro a ha
            have ha' := hsub ha
            rw [hj, Finset.mem_insert, Finset.mem_singleton] at ha'
            rcases ha' with rfl | rfl
            · exact Finset.mem_singleton_self _
            · exact absurd ha h3i
          have hy0 : (y : adjointGroup .F4 K) ∈
              CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hi0 x.2
          rw [fieldFamily_of_three_not_mem h0i h3i, fieldPairLift_of_mem_left hX hY hcomm _ hy0]
          exact hY.restrict_eq_of_coe_eq _ _ _ _ hxy
      · have hi3 : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ {3} := by
          intro a ha
          have ha' := hsub ha
          rw [hj, Finset.mem_insert, Finset.mem_singleton] at ha'
          rcases ha' with rfl | rfl
          · exact absurd ha h0i
          · exact Finset.mem_singleton_self _
        have hy3 : (y : adjointGroup .F4 K) ∈
            CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} := by
          rw [← hxy]
          exact CFSG.LieType.CurtisTits.levi_mono _ hi3 x.2
        rw [fieldFamily_of_zero_not_mem h0i, fieldPairLift_of_mem_right hX hY hcomm _ hy3]
        exact hX.restrict_eq_of_coe_eq _ _ _ _ hxy
    · have h3i : (3 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h3j (hsub h)
      rw [fieldFamily_of_three_not_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · rw [fieldFamily_of_three_not_mem h0i h3i]
        exact hY.restrict_eq_of_coe_eq _ _ _ _ hxy
      · rw [fieldFamily_of_zero_not_mem h0i]
        have hx12 : (x : adjointGroup .F4 K) ∈
            CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} :=
          CFSG.LieType.CurtisTits.levi_mono _ (subset_one_two_of_not_mem h0i h3i) x.2
        rw [hX.restrict_eq_of_coe_eq _ one_two_subset_X x ⟨x, hx12⟩ rfl, hagree,
          hY.restrict_eq_of_coe_eq one_two_subset_Y _ ⟨x, hx12⟩ y hxy]
  · have h0i : (0 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h0j (hsub h)
    rw [fieldFamily_of_zero_not_mem h0i, fieldFamily_of_zero_not_mem h0j]
    exact hX.restrict_eq_of_coe_eq _ _ _ _ hxy

end Family

theorem exists_mul_eq_of_mem_sup_of_commute {M : Type*} [Group M] {A B : Subgroup M}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : M} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← range_noncommCoprod_subtype hcomm] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

section Images


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem FieldNeighbourIso.range_restrict_eq_map {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    (h.restrict hJ).range =
      ((CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J).subgroupOf
        (N.levi K)).map ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, levi_le_neighbourLevi hJ x.2⟩, x.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem FieldNeighbourIso.range_restrict_zero_three (h : FieldNeighbourIso σ e .X') :
    (h.restrict zero_three_subset_X').range =
      (h.restrict zero_subset_X').range ⊔ (h.restrict three_subset_X').range := by
  rw [h.range_restrict_eq_map, h.range_restrict_eq_map, h.range_restrict_eq_map,
    ← Subgroup.map_sup, levi_pair, subgroupOf_sup (levi_le_neighbourLevi zero_subset_X')
      (levi_le_neighbourLevi three_subset_X')]

end Images

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem exists_isCompatible_field (hX : FieldNeighbourIso σ e .X) (hY : FieldNeighbourIso σ e .Y)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ φ : ∀ J, (Adjoint.f4Datum K).leviAmalgam J →* G,
      CFSG.LieType.CurtisTits.IsCompatible (Adjoint.f4Datum K).leviAmalgam φ ∧
      (∀ J, (φ J).range = pieceCore e J.1) ∧
      ∀ J (x : adjointGroup .F4 (fixSubfield σ)),
        x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup J.1 →
        ∀ y : (Adjoint.f4Datum K).leviAmalgam J,
          ((y : adjointGroup .F4 K) : ModGL .F4 K) =
            baseChangeGL (fixSubfield σ).subtype (x : ModGL .F4 (fixSubfield σ)) →
          φ J y = ((e.symm x : L) : G) := by
  obtain ⟨ρ, hρ, hagree⟩ := exists_twist_restrict_eq hX hY hq
  set hY' := hY.twist ρ hρ with hY'def
  set hX' := hX.toX' with hX'def
  have hM0 : (hY'.restrict zero_subset_Y).range = (hX'.restrict zero_subset_X').range := by
    rw [hY'.range_restrict hq zero_subset_Y (by decide),
      hX'.range_restrict hq zero_subset_X' (by decide)]
  have hM3 : (hX.restrict three_subset_X).range = (hX'.restrict three_subset_X').range := by
    rw [hX.range_restrict hq three_subset_X (by decide),
      hX'.range_restrict hq three_subset_X' (by decide)]
  have hcomm : ∀ a b, Commute (hY'.restrict zero_subset_Y a) (hX.restrict three_subset_X b) := by
    intro a b
    obtain ⟨a', ha'⟩ : hY'.restrict zero_subset_Y a ∈ (hX'.restrict zero_subset_X').range :=
      hM0 ▸ ⟨a, rfl⟩
    obtain ⟨b', hb'⟩ : hX.restrict three_subset_X b ∈ (hX'.restrict three_subset_X').range :=
      hM3 ▸ ⟨b, rfl⟩
    rw [← ha', ← hb']
    exact hX'.commute_restrict _ _ a' b' (commute_levi_zero_three _ a'.2 _ b'.2)
  refine ⟨fieldFamily hX hY' hcomm, isCompatible_fieldFamily hagree, fun J => ?_,
    fun J x hx y hxy => ?_⟩
  ·
    by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
    · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
      · have hJ : (J.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three J.2 h0 h3
        have hrange : (fieldFamily hX hY' hcomm J).range = (fieldPairLift hX hY' hcomm).range := by
          refine le_antisymm ?_ ?_
          · rintro _ ⟨x, rfl⟩
            rw [fieldFamily_of_mem_of_mem h0 h3]
            exact ⟨_, rfl⟩
          · rintro _ ⟨z, rfl⟩
            have hz : (z : adjointGroup .F4 K) ∈
                CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J.1 := by
              rw [hJ, levi_pair]
              exact z.2
            refine ⟨⟨z, hz⟩, ?_⟩
            rw [fieldFamily_of_mem_of_mem h0 h3]
        rw [hrange, fieldPairLift, range_supLift, hY'.range_restrict hq zero_subset_Y (by decide),
          hX.range_restrict hq three_subset_X (by decide), hJ,
          ← hX'.range_restrict hq zero_subset_X' (by decide),
          ← hX'.range_restrict hq three_subset_X' (by decide),
          ← hX'.range_restrict hq zero_three_subset_X' (by decide),
          hX'.range_restrict_zero_three]
      · have hφ : fieldFamily hX hY' hcomm J =
            hY'.restrict (subset_nodes_Y_of_three_not_mem h3) :=
          MonoidHom.ext fun x => fieldFamily_of_three_not_mem h0 h3 x
        rw [hφ, hY'.range_restrict hq _ J.2]
    · have hφ : fieldFamily hX hY' hcomm J = hX.restrict (subset_nodes_X_of_zero_not_mem h0) :=
        MonoidHom.ext fun x => fieldFamily_of_zero_not_mem h0 x
      rw [hφ, hX.range_restrict hq _ J.2]
  ·
    by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
    · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
      · have hJ : (J.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three J.2 h0 h3
        rw [fieldFamily_of_mem_of_mem h0 h3]
        have hx' : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {0} ⊔
            CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {3} := by
          rw [← levi_pair, ← hJ]
          exact hx
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute commute_levi_zero_three hx'
        obtain ⟨a', ha'⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype ha
        obtain ⟨b', hb'⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype hb
        have hyab : (⟨y, levi_le_sup_of_mem_of_mem J.2 h0 h3 y.2⟩ :
            ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
              CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3})) =
            ⟨a', mem_sup_left a'.2⟩ * ⟨b', mem_sup_right b'.2⟩ := by
          refine Subtype.ext (Subtype.ext ?_)
          change ((y : adjointGroup .F4 K) : ModGL .F4 K) =
            ((a' : adjointGroup .F4 K) : ModGL .F4 K) * ((b' : adjointGroup .F4 K) : ModGL .F4 K)
          rw [hxy, ha', hb', ← map_mul]
          rfl
        rw [hyab, map_mul, fieldPairLift_of_mem_left hX hY' hcomm _ a'.2,
          fieldPairLift_of_mem_right hX hY' hcomm _ b'.2,
          hY'.restrict_fix zero_subset_Y ha _ ha', hX.restrict_fix three_subset_X hb _ hb',
          map_mul, L.coe_mul]
      · rw [fieldFamily_of_three_not_mem h0 h3]
        exact hY'.restrict_fix _ hx y hxy
    · rw [fieldFamily_of_zero_not_mem h0]
      exact hX.restrict_fix _ hx y hxy

end Main

section Galois

theorem mem_zpowers_of_forall_fixSubfield {K : Type} [Field K] [Finite K] {σ ρ : K ≃+* K}
    (hρ : ∀ c : fixSubfield σ, ρ c = c) : ρ ∈ Subgroup.zpowers σ := by
  have : Finite (K ≃+* K) := Finite.of_injective (fun f : K ≃+* K => (f : K → K))
    DFunLike.coe_injective
  have hfix : ∀ x ∈ FixedPoints.subfield (Subgroup.zpowers σ) K, ρ x = x := fun x hx =>
    hρ ⟨x, hx ⟨σ, Subgroup.mem_zpowers σ⟩⟩
  obtain ⟨h, hh⟩ := FixedPoints.toAlgAut_surjective (Subgroup.zpowers σ) K
    (AlgEquiv.ofRingEquiv (f := ρ) fun x => hfix x x.2)
  have hρh : (h : K ≃+* K) = ρ := RingEquiv.ext fun x => AlgEquiv.ext_iff.1 hh x
  exact hρh ▸ h.2

theorem eq_one_or_eq_of_forall_fixSubfield {K : Type} [Field K] [Finite K] {σ ρ : K ≃+* K}
    (hσ : orderOf σ = 2) (hρ : ∀ c : fixSubfield σ, ρ c = c) : ρ = 1 ∨ ρ = σ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_forall_fixSubfield hρ)
  rw [← zpow_mod_orderOf, hσ]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]


theorem exists_eq_one_or_eq_of_forall_B2Levi {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} (hσ : orderOf σ = 2) (θ : MulAut (B2Levi K))
    (hθ : ∀ (x : B2Levi (fixSubfield σ)) (y : B2Levi K), ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype
        ((x : adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) → θ y = y) :
    ∃ ρ : K ≃+* K, (ρ = 1 ∨ ρ = σ) ∧ ∀ y : B2Levi K,
      (((θ y : B2Levi K) : adjointGroup .F4 K) : ModGL .F4 K) =
        baseChangeGL (ρ : K →+* K) ((y : adjointGroup .F4 K) : ModGL .F4 K) := by
  obtain ⟨ρ, hρ, hθρ⟩ := exists_ringEquiv_of_forall_B2Levi (fixSubfield σ).subtype θ hθ
  exact ⟨ρ, eq_one_or_eq_of_forall_fixSubfield hσ hρ, hθρ⟩

end Galois

end CFSG.SeitzReduction.F4Pilot
