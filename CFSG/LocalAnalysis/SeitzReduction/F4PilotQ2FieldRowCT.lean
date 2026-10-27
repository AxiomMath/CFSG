module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldRowParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)

local instance f4PilotQ2FieldRowCTNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem c3Node_mem_one_two_three (j : Fin 3) :
    c3Node j ∈ ({1, 2, 3} : Finset (Fin (Tag.rank .F4))) := by
  fin_cases j <;> decide

theorem single_mem_c3Roots_q2 (j : Fin 3) : (Pi.single j 1 : Fin 3 → ℤ) ∈ c3Roots := by
  fin_cases j <;> decide

theorem neg_single_mem_c3Roots_q2 (j : Fin 3) : (-Pi.single j 1 : Fin 3 → ℤ) ∈ c3Roots := by
  fin_cases j <;> decide

theorem zero_not_mem_one_two_three : (0 : Fin (Tag.rank .F4)) ∉ ({1, 2, 3} : Finset _) := by
  decide

theorem zero_subset_zero_three : ({0} : Finset (Fin (Tag.rank .F4))) ⊆ {0, 3} := by
  decide


section Generation

variable {K : Type} [Field K]

theorem C3Levi_le_levi_one_two_three [Finite K] [CharP K 2] :
    C3Levi K ≤ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2, 3} := by
  rw [← range_c3LeviHom, MonoidHom.range_eq_map, ← levi_univ_statedSp_eq_top 3,
    Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun j _ => sup_le ?_ ?_
  · rw [← Subgroup.map_le_iff_le_comap,
      map_c3LeviHom_rootGroup (mem_roots_of_mem_c3Roots (single_mem_c3Roots_q2 j)),
      c3ToF4_single]
    exact le_sup_left.trans
      (CFSG.LieType.CurtisTits.rankOne_le_levi _ (c3Node_mem_one_two_three j))
  · rw [← Subgroup.map_le_iff_le_comap,
      map_c3LeviHom_rootGroup (mem_roots_of_mem_c3Roots (neg_single_mem_c3Roots_q2 j)),
      map_neg, c3ToF4_single]
    exact le_sup_right.trans
      (CFSG.LieType.CurtisTits.rankOne_le_levi _ (c3Node_mem_one_two_three j))

theorem top_le_C3Levi_sup_range_fixedFieldInclusion (σ : K ≃+* K) :
    (⊤ : Subgroup (adjointGroup .F4 K)) ≤
      C3Levi K ⊔ (fixedFieldInclusion (τ := .F4) σ).range := by
  have hn : fixedFieldInclusion σ (n1242 (fixSubfield σ)) = n1242 K :=
    Subtype.ext (by rw [coe_fixedFieldInclusion, baseChangeGL_n1242])
  have hnr : n1242 K ∈ C3Levi K ⊔ (fixedFieldInclusion (τ := .F4) σ).range :=
    mem_sup_right ⟨_, hn⟩
  have h1242 : C3Levi1242 K ≤ C3Levi K ⊔ (fixedFieldInclusion (τ := .F4) σ).range := by
    rw [← map_conj_n1242_C3Levi]
    rintro _ ⟨x, hx, rfl⟩
    change n1242 K * x * (n1242 K)⁻¹ ∈ _
    exact mul_mem (mul_mem hnr (mem_sup_left hx)) (inv_mem hnr)
  have key : ∀ i : Fin (Tag.rank .F4),
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} ≤
        C3Levi K ⊔ (fixedFieldInclusion (τ := .F4) σ).range := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact (levi_le_C3Levi1242 zero_subset_zero_three).trans h1242
    · exact (levi_le_C3Levi fun h => hi (Finset.mem_singleton.1 h).symm).trans le_sup_left
  rw [← CFSG.LieType.Ree.closure_xElement_yElement (τ := .F4) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact key i (xElement_mem_levi_singleton i c)
  · exact key i (yElement_mem_levi_singleton i c)

end Generation

section Family

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 (fixSubfield σ)} {EX EY : Subgroup G}

theorem levi_le_sup_of_mem_of_mem_q2 {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J ≤
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} := by
  rw [eq_pair_zero_three hJ h0 h3, levi_pair]

variable (hX : Q2FieldParam σ e .X EX) (hY : Q2FieldParam σ e .Y EY)
  (hcomm : ∀ a b, Commute (hY.restrict zero_subset_Y a) (hX.restrict three_subset_X b))

@[expose] noncomputable def q2PairLift :
    ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) →* G :=
  supLift commute_levi_zero_three levi_zero_inf_levi_three_eq_bot (hY.restrict zero_subset_Y)
    (hX.restrict three_subset_X) hcomm

theorem q2PairLift_of_mem_left
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}) :
    q2PairLift hX hY hcomm z = hY.restrict zero_subset_Y ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_left commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm ⟨z, hz⟩

theorem q2PairLift_of_mem_right
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) :
    q2PairLift hX hY hcomm z = hX.restrict three_subset_X ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_right commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm ⟨z, hz⟩

@[expose] noncomputable def q2FieldFamily
    (J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}) :
    (Adjoint.f4Datum K).leviAmalgam J →* G :=
  if h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1 then
    if h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1 then
      (q2PairLift hX hY hcomm).comp
        (Subgroup.inclusion (levi_le_sup_of_mem_of_mem_q2 J.2 h0 h3))
    else hY.restrict (subset_nodes_Y_of_three_not_mem h3)
  else hX.restrict (subset_nodes_X_of_zero_not_mem h0)

variable {hX hY hcomm}

theorem q2FieldFamily_of_zero_not_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J.1) (x : (Adjoint.f4Datum K).leviAmalgam J) :
    q2FieldFamily hX hY hcomm J x = hX.restrict (subset_nodes_X_of_zero_not_mem h0) x := by
  rw [q2FieldFamily, dite_eq_right h0]

theorem q2FieldFamily_of_three_not_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∉ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    q2FieldFamily hX hY hcomm J x = hY.restrict (subset_nodes_Y_of_three_not_mem h3) x := by
  rw [q2FieldFamily, dite_eq_left h0, dite_eq_right h3]

theorem q2FieldFamily_of_mem_of_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    q2FieldFamily hX hY hcomm J x =
      q2PairLift hX hY hcomm ⟨x, levi_le_sup_of_mem_of_mem_q2 J.2 h0 h3 x.2⟩ := by
  rw [q2FieldFamily, dite_eq_left h0, dite_eq_left h3]
  rfl

theorem isCompatible_q2FieldFamily
    (hagree : ∀ x, hX.restrict one_two_subset_X x = hY.restrict one_two_subset_Y x) :
    IsCompatible (Adjoint.f4Datum K).leviAmalgam (q2FieldFamily hX hY hcomm) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ j.1 := hij
  by_cases h0j : (0 : Fin (Tag.rank .F4)) ∈ j.1
  · by_cases h3j : (3 : Fin (Tag.rank .F4)) ∈ j.1
    · have hj : (j.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three j.2 h0j h3j
      rw [q2FieldFamily_of_mem_of_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · by_cases h3i : (3 : Fin (Tag.rank .F4)) ∈ i.1
        · rw [q2FieldFamily_of_mem_of_mem h0i h3i]
          exact congrArg (q2PairLift hX hY hcomm) (Subtype.ext hxy)
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
          rw [q2FieldFamily_of_three_not_mem h0i h3i, q2PairLift_of_mem_left hX hY hcomm _ hy0]
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
        rw [q2FieldFamily_of_zero_not_mem h0i, q2PairLift_of_mem_right hX hY hcomm _ hy3]
        exact hX.restrict_eq_of_coe_eq _ _ _ _ hxy
    · have h3i : (3 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h3j (hsub h)
      rw [q2FieldFamily_of_three_not_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · rw [q2FieldFamily_of_three_not_mem h0i h3i]
        exact hY.restrict_eq_of_coe_eq _ _ _ _ hxy
      · rw [q2FieldFamily_of_zero_not_mem h0i]
        have hx12 : (x : adjointGroup .F4 K) ∈
            CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} :=
          CFSG.LieType.CurtisTits.levi_mono _ (subset_one_two_of_not_mem h0i h3i) x.2
        rw [hX.restrict_eq_of_coe_eq _ one_two_subset_X x ⟨x, hx12⟩ rfl, hagree,
          hY.restrict_eq_of_coe_eq one_two_subset_Y _ ⟨x, hx12⟩ y hxy]
  · have h0i : (0 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h0j (hsub h)
    rw [q2FieldFamily_of_zero_not_mem h0i, q2FieldFamily_of_zero_not_mem h0j]
    exact hX.restrict_eq_of_coe_eq _ _ _ _ hxy

end Family

section Twist

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)} {EX EY : Subgroup G}

theorem exists_twist_restrict_eq_q2 (hX : Q2FieldParam σ e .X EX) (hY : Q2FieldParam σ e .Y EY)
    (hr12 : (hX.restrict one_two_subset_X).range = (hY.restrict one_two_subset_Y).range) :
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
      ← MonoidHom.range_eq_map, hr12]
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
  rw [h1, hY.restrict_apply, (hY.twist ρ hρ').restrict_apply, Q2FieldParam.twist_apply]
  rfl

omit [Finite K] [CharP K 2] in
theorem q2FieldFamily_fix {hX : Q2FieldParam σ e .X EX} {hY : Q2FieldParam σ e .Y EY}
    {hcomm : ∀ a b, Commute (hY.restrict zero_subset_Y a) (hX.restrict three_subset_X b)}
    (J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2})
    (x : adjointGroup .F4 (fixSubfield σ))
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup J.1)
    (y : (Adjoint.f4Datum K).leviAmalgam J)
    (hxy : ((y : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .F4 (fixSubfield σ))) :
    q2FieldFamily hX hY hcomm J y = ((e.symm x : L) : G) := by
  by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
  · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
    · have hJ : (J.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three J.2 h0 h3
      rw [q2FieldFamily_of_mem_of_mem h0 h3]
      have hx' : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {0} ⊔
          CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {3} := by
        rw [← levi_pair, ← hJ]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute commute_levi_zero_three hx'
      obtain ⟨a', ha'⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype ha
      obtain ⟨b', hb'⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype hb
      have hyab : (⟨y, levi_le_sup_of_mem_of_mem_q2 J.2 h0 h3 y.2⟩ :
          ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
            CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3})) =
          ⟨a', mem_sup_left a'.2⟩ * ⟨b', mem_sup_right b'.2⟩ := by
        refine Subtype.ext (Subtype.ext ?_)
        change ((y : adjointGroup .F4 K) : ModGL .F4 K) =
          ((a' : adjointGroup .F4 K) : ModGL .F4 K) * ((b' : adjointGroup .F4 K) : ModGL .F4 K)
        rw [hxy, ha', hb', ← map_mul]
        rfl
      rw [hyab, map_mul, q2PairLift_of_mem_left hX hY hcomm _ a'.2,
        q2PairLift_of_mem_right hX hY hcomm _ b'.2,
        hY.restrict_fix zero_subset_Y ha _ ha', hX.restrict_fix three_subset_X hb _ hb',
        map_mul, L.coe_mul]
    · rw [q2FieldFamily_of_three_not_mem h0 h3]
      exact hY.restrict_fix _ hx y hxy
  · rw [q2FieldFamily_of_zero_not_mem h0]
    exact hX.restrict_fix _ hx y hxy

end Twist

section CT

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)} {EX EY : Subgroup G}

theorem exists_injective_q2FieldRow (hX : Q2FieldParam σ e .X EX) (hY : Q2FieldParam σ e .Y EY)
    (hagree : ∀ x, hX.restrict one_two_subset_X x = hY.restrict one_two_subset_Y x)
    (hcomm : ∀ a b, Commute (hY.restrict zero_subset_Y a) (hX.restrict three_subset_X b)) :
    ∃ ψ : adjointGroup .F4 K →* G, Function.Injective ψ ∧
      (∀ x : adjointGroup .F4 (fixSubfield σ),
        ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G)) ∧
      (C3Levi K).map ψ = EX := by
  set φ := q2FieldFamily hX hY hcomm with hφdef
  have hcompat : IsCompatible (Adjoint.f4Datum K).leviAmalgam φ :=
    isCompatible_q2FieldFamily hagree
  have hcard : ∀ i : Fin (Tag.rank .F4),
      ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2 := fun i => by simp
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (Adjoint.f4Datum K).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (Adjoint.f4Datum K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hcompat i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hX0 := (Adjoint.f4_steinbergExtras (fixSubfield σ)).ne_bot (Pi.single 0 1)
      ((CFSG.LieType.RootSystem.isCTRootSystem _ _).single_mem 0)
    obtain ⟨u, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX0
    have hu0 : (u : adjointGroup .F4 (fixSubfield σ)) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {0} := by
      rw [CFSG.LieType.CurtisTits.levi_singleton]
      exact mem_sup_left u.2
    obtain ⟨y, hy⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype hu0
    refine ⟨⟨{0}, hcard 0⟩, y, fun h => hu ?_⟩
    have h1 : φ ⟨{0}, hcard 0⟩ y = 1 := congrArg Subtype.val h
    rw [hφdef, q2FieldFamily_fix ⟨{0}, hcard 0⟩ _ hu0 y hy] at h1
    have h2 : e.symm (u : adjointGroup .F4 (fixSubfield σ)) = 1 := Subtype.ext h1
    have h3 : (u : adjointGroup .F4 (fixSubfield σ)) = 1 := by
      rw [← map_one e.symm] at h2
      exact e.symm.injective h2
    exact Subtype.ext h3
  obtain ⟨ψ₀, hψ₀, hsurj, hker⟩ := exists_surjective_of_isCompatible_f4 K φ' hφ' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans center_adjointGroup_eq_bot.le
  have hψφ : ∀ J (x : (Adjoint.f4Datum K).leviAmalgam J), (G₀.subtype.comp ψ₀) x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  set ψ := G₀.subtype.comp ψ₀ with hψdef
  have hD : ∀ (x : adjointGroup .F4 K) (hx : x ∈ C3Levi K), ψ x = (hX.Φ ⟨x, hx⟩ : G) := by
    set T : Subgroup (adjointGroup .F4 K) := (MonoidHom.eqLocus (ψ.comp (C3Levi K).subtype)
      (EX.subtype.comp hX.Φ.toMonoidHom)).map (C3Levi K).subtype with hT
    have hj : ∀ j ∈ ({1, 2, 3} : Finset (Fin (Tag.rank .F4))),
        CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup j ≤ T := by
      intro j hj x hx
      have h0 : (0 : Fin (Tag.rank .F4)) ∉ ({j} : Finset (Fin (Tag.rank .F4))) := by
        intro h
        rw [Finset.mem_singleton] at h
        rw [← h] at hj
        exact zero_not_mem_one_two_three hj
      have hxj : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {j} := by
        rw [CFSG.LieType.CurtisTits.levi_singleton]
        exact hx
      have hxD : x ∈ C3Levi K := levi_le_C3Levi h0 hxj
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      have e1 := hψφ ⟨{j}, hcard j⟩ ⟨x, hxj⟩
      rw [hφdef, q2FieldFamily_of_zero_not_mem h0, Q2FieldParam.restrict_apply] at e1
      exact e1
    intro x hx
    have hxT : x ∈ T := (C3Levi_le_levi_one_two_three.trans (iSup₂_le hj)) hx
    obtain ⟨y, hy, hyx⟩ := hxT
    have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
    subst hyx'
    exact hy
  refine ⟨ψ, G₀.subtype_injective.comp hinj₀, fun x => ?_, ?_⟩
  · have key : ∀ (i : Fin (Tag.rank .F4)) (x : adjointGroup .F4 (fixSubfield σ)),
        x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum (fixSubfield σ)).rootGroup {i} →
        ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
      intro i x hx
      obtain ⟨y, hy⟩ := exists_levi_baseChangeGL (K := K) (fixSubfield σ).subtype hx
      have hyx : (y : adjointGroup .F4 K) = fixedFieldInclusion σ x := Subtype.ext hy
      rw [← hyx]
      exact (hψφ ⟨{i}, hcard i⟩ y).trans (q2FieldFamily_fix ⟨{i}, hcard i⟩ x hx y hy)
    have h := CFSG.LieType.Ree.adjointGroup_hom_ext
      (f := ψ.comp (fixedFieldInclusion σ))
      (g := L.subtype.comp e.symm.toMonoidHom)
      (fun i c => key i _ (xElement_mem_levi_singleton i c))
      (fun i c => key i _ (yElement_mem_levi_singleton i c))
    exact DFunLike.congr_fun h x
  · ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hD x hx]
      exact (hX.Φ ⟨x, hx⟩).2
    · intro hg
      obtain ⟨y, hy⟩ := hX.Φ.surjective ⟨g, hg⟩
      refine ⟨y, y.2, ?_⟩
      rw [hD y y.2]
      exact congrArg Subtype.val hy

omit [Finite K] [CharP K 2] in
theorem range_eq_sup_of_map_C3Levi {ψ : adjointGroup .F4 K →* G}
    (hfix : ∀ x : adjointGroup .F4 (fixSubfield σ),
      ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G))
    (hD : (C3Levi K).map ψ = EX) : ψ.range = EX ⊔ L := by
  have hc : ψ.comp (fixedFieldInclusion σ) = L.subtype.comp e.symm.toMonoidHom :=
    MonoidHom.ext hfix
  have hι : (fixedFieldInclusion (τ := .F4) σ).range.map ψ = L := by
    rw [← MonoidHom.range_comp, hc, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (MulEquiv.surjective _), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [MonoidHom.range_eq_map, ← eq_top_iff.2 (top_le_C3Levi_sup_range_fixedFieldInclusion σ),
    Subgroup.map_sup, hD, hι]

end CT

end CFSG.SeitzReduction.F4Pilot
