module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapTwist
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapF4

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)

local instance f4PilotCTSwapNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Orth


variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 K} {t : G}

theorem commute_of_mem_pieceCore_zero_of_mem_pieceCore_three (hX' : SwapNeighbourIso e t .X')
    (hq : 4 ≤ Nat.card K) {g g' : G} (hg : g ∈ pieceCore e {0}) (hg' : g' ∈ pieceCore e {3}) :
    Commute g g' := by
  obtain ⟨a, b, rfl⟩ := hX'.exists_eq_of_mem_pieceCore hq zero_subset_X' (by decide) hg
  obtain ⟨c, d, rfl⟩ := hX'.exists_eq_of_mem_pieceCore hq three_subset_X' (by decide) hg'
  have hac := hX'.commute_fst zero_subset_X' three_subset_X' a c
    (commute_levi_zero_three _ a.2 _ c.2)
  have hbd := hX'.commute_snd zero_subset_X' three_subset_X' b d
    (commute_levi_zero_three _ b.2 _ d.2)
  have had := hX'.commute_fst_snd zero_subset_X' three_subset_X' a d
  have hbc := (hX'.commute_fst_snd three_subset_X' zero_subset_X' c b).symm
  exact (hac.mul_right had).mul_left (hbc.mul_right hbd)

theorem pieceCore_zero_three_le_sup (hX' : SwapNeighbourIso e t .X') (hq : 4 ≤ Nat.card K) :
    pieceCore e {0, 3} ≤ pieceCore e {0} ⊔ pieceCore e {3} := by
  intro g hg
  obtain ⟨a, b, rfl⟩ := hX'.exists_eq_of_mem_pieceCore hq zero_three_subset_X' (by decide) hg
  have hsplit : ∀ z : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0, 3},
      hX'.fst zero_three_subset_X' z ∈ pieceCore e {0} ⊔ pieceCore e {3} ∧
        hX'.snd zero_three_subset_X' z ∈ pieceCore e {0} ⊔ pieceCore e {3} := by
    intro z
    have hz : (z : adjointGroup .F4 K) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
          CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} := by
      rw [← levi_pair]
      exact z.2
    obtain ⟨z₀, hz₀, z₃, hz₃, hzz⟩ := exists_mul_eq_of_mem_sup_of_commute commute_levi_zero_three hz
    have hz₀' : z₀ ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0, 3} :=
      CFSG.LieType.CurtisTits.levi_mono _
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)) hz₀
    have hz₃' : z₃ ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0, 3} :=
      CFSG.LieType.CurtisTits.levi_mono _
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          hz₃
    have hzeq : z = ⟨z₀, hz₀'⟩ * ⟨z₃, hz₃'⟩ := Subtype.ext hzz.symm
    have h0 : hX'.fst zero_three_subset_X' ⟨z₀, hz₀'⟩ = hX'.fst zero_subset_X' ⟨z₀, hz₀⟩ :=
      hX'.fst_eq_of_coe_eq _ _ _ _ rfl
    have h3 : hX'.fst zero_three_subset_X' ⟨z₃, hz₃'⟩ = hX'.fst three_subset_X' ⟨z₃, hz₃⟩ :=
      hX'.fst_eq_of_coe_eq _ _ _ _ rfl
    have h0' : hX'.snd zero_three_subset_X' ⟨z₀, hz₀'⟩ = hX'.snd zero_subset_X' ⟨z₀, hz₀⟩ :=
      hX'.snd_eq_of_coe_eq _ _ _ _ rfl
    have h3' : hX'.snd zero_three_subset_X' ⟨z₃, hz₃'⟩ = hX'.snd three_subset_X' ⟨z₃, hz₃⟩ :=
      hX'.snd_eq_of_coe_eq _ _ _ _ rfl
    rw [hzeq, map_mul, map_mul, h0, h3, h0', h3']
    exact ⟨mul_mem (mem_sup_left (hX'.range_fst_le_pieceCore hq zero_subset_X' (by decide)
        ⟨_, rfl⟩)) (mem_sup_right (hX'.range_fst_le_pieceCore hq three_subset_X' (by decide)
        ⟨_, rfl⟩)),
      mul_mem (mem_sup_left (hX'.range_snd_le_pieceCore hq zero_subset_X' (by decide)
        ⟨_, rfl⟩)) (mem_sup_right (hX'.range_snd_le_pieceCore hq three_subset_X' (by decide)
        ⟨_, rfl⟩))⟩
  exact mul_mem (hsplit a).1 (hsplit b).2

end Orth

section Family


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G}

variable (hX : SwapNeighbourIso e t .X) (hY : SwapNeighbourIso e t .Y)
  (hcomm : ∀ a b, Commute (hY.fst zero_subset_Y a) (hX.fst three_subset_X b))

@[expose] noncomputable def swapPairLift :
    ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) →* G :=
  supLift commute_levi_zero_three levi_zero_inf_levi_three_eq_bot (hY.fst zero_subset_Y)
    (hX.fst three_subset_X) hcomm

theorem swapPairLift_of_mem_left
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}) :
    swapPairLift hX hY hcomm z = hY.fst zero_subset_Y ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_left commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm ⟨z, hz⟩

theorem swapPairLift_of_mem_right
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) :
    swapPairLift hX hY hcomm z = hX.fst three_subset_X ⟨z, hz⟩ := by
  obtain ⟨z, -⟩ := z
  exact supLift_apply_right commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm ⟨z, hz⟩

@[expose] noncomputable def swapFamily
    (J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}) :
    (Adjoint.f4Datum K).leviAmalgam J →* G :=
  if h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1 then
    if h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1 then
      (swapPairLift hX hY hcomm).comp (Subgroup.inclusion (levi_le_sup_of_mem_of_mem J.2 h0 h3))
    else hY.fst (subset_nodes_Y_of_three_not_mem h3)
  else hX.fst (subset_nodes_X_of_zero_not_mem h0)

variable {hX hY hcomm}

theorem swapFamily_of_zero_not_mem {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J.1) (x : (Adjoint.f4Datum K).leviAmalgam J) :
    swapFamily hX hY hcomm J x = hX.fst (subset_nodes_X_of_zero_not_mem h0) x := by
  rw [swapFamily, dite_eq_right h0]

theorem swapFamily_of_three_not_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∉ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    swapFamily hX hY hcomm J x = hY.fst (subset_nodes_Y_of_three_not_mem h3) x := by
  rw [swapFamily, dite_eq_left h0, dite_eq_right h3]

theorem swapFamily_of_mem_of_mem {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    swapFamily hX hY hcomm J x =
      swapPairLift hX hY hcomm ⟨x, levi_le_sup_of_mem_of_mem J.2 h0 h3 x.2⟩ := by
  rw [swapFamily, dite_eq_left h0, dite_eq_left h3]
  rfl

theorem isCompatible_swapFamily
    (hagree : ∀ x, hX.fst one_two_subset_X x = hY.fst one_two_subset_Y x) :
    IsCompatible (Adjoint.f4Datum K).leviAmalgam (swapFamily hX hY hcomm) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ j.1 := hij
  by_cases h0j : (0 : Fin (Tag.rank .F4)) ∈ j.1
  · by_cases h3j : (3 : Fin (Tag.rank .F4)) ∈ j.1
    · have hj : (j.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three j.2 h0j h3j
      rw [swapFamily_of_mem_of_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · by_cases h3i : (3 : Fin (Tag.rank .F4)) ∈ i.1
        · rw [swapFamily_of_mem_of_mem h0i h3i]
          exact congrArg (swapPairLift hX hY hcomm) (Subtype.ext hxy)
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
          rw [swapFamily_of_three_not_mem h0i h3i, swapPairLift_of_mem_left hX hY hcomm _ hy0]
          exact hY.fst_eq_of_coe_eq _ _ _ _ hxy
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
        rw [swapFamily_of_zero_not_mem h0i, swapPairLift_of_mem_right hX hY hcomm _ hy3]
        exact hX.fst_eq_of_coe_eq _ _ _ _ hxy
    · have h3i : (3 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h3j (hsub h)
      rw [swapFamily_of_three_not_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · rw [swapFamily_of_three_not_mem h0i h3i]
        exact hY.fst_eq_of_coe_eq _ _ _ _ hxy
      · rw [swapFamily_of_zero_not_mem h0i]
        have hx12 : (x : adjointGroup .F4 K) ∈
            CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} :=
          CFSG.LieType.CurtisTits.levi_mono _ (subset_one_two_of_not_mem h0i h3i) x.2
        rw [hX.fst_eq_of_coe_eq _ one_two_subset_X x ⟨x, hx12⟩ rfl, hagree,
          hY.fst_eq_of_coe_eq one_two_subset_Y _ ⟨x, hx12⟩ y hxy]
  · have h0i : (0 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h0j (hsub h)
    rw [swapFamily_of_zero_not_mem h0i, swapFamily_of_zero_not_mem h0j]
    exact hX.fst_eq_of_coe_eq _ _ _ _ hxy

end Family

section RankOne


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G}
  {hX : SwapNeighbourIso e t .X} {hY : SwapNeighbourIso e t .Y}
  {hcomm : ∀ a b, Commute (hY.fst zero_subset_Y a) (hX.fst three_subset_X b)}

theorem zero_not_mem_singleton_of_ne {i : Fin (Tag.rank .F4)} (hi : i ≠ 0) :
    (0 : Fin (Tag.rank .F4)) ∉ ({i} : Finset (Fin (Tag.rank .F4))) := by
  rw [Finset.mem_singleton]
  exact fun h => hi h.symm

theorem swapFamily_singleton_zero (h : ({0} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{0}, h⟩) :
    swapFamily hX hY hcomm ⟨{0}, h⟩ x = hY.fst zero_subset_Y x :=
  swapFamily_of_three_not_mem (Finset.mem_singleton_self _)
    (show (3 : Fin (Tag.rank .F4)) ∉ ({0} : Finset (Fin (Tag.rank .F4))) by decide) x

theorem swapFamily_singleton_of_ne {i : Fin (Tag.rank .F4)} (hi : i ≠ 0)
    (h : ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{i}, h⟩) :
    swapFamily hX hY hcomm ⟨{i}, h⟩ x =
      hX.fst (subset_nodes_X_of_zero_not_mem (zero_not_mem_singleton_of_ne hi)) x :=
  swapFamily_of_zero_not_mem (zero_not_mem_singleton_of_ne hi) x

theorem commute_swapFamily_singleton
    (hagree : ∀ x, hX.fst one_two_subset_X x = hY.fst one_two_subset_Y x ∧
      hX.snd one_two_subset_X x = hY.snd one_two_subset_Y x)
    (hM03 : ∀ a b, Commute (hY.fst zero_subset_Y a) (hX.snd three_subset_X b) ∧
      Commute (hX.fst three_subset_X b) (hY.snd zero_subset_Y a))
    (i j : Fin (Tag.rank .F4)) (hi : ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (hj : ({j} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{i}, hi⟩)
    (y : (Adjoint.f4Datum K).leviAmalgam ⟨{j}, hj⟩) :
    Commute (swapFamily hX hY hcomm ⟨{i}, hi⟩ x)
      (t * swapFamily hX hY hcomm ⟨{j}, hj⟩ y * t⁻¹) := by
  have hag : ∀ k : Fin (Tag.rank .F4), k ≠ 0 → k ≠ 3 →
      ∀ (hkX : ({k} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X.nodes)
        (hkY : ({k} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.Y.nodes)
        (z : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {k}),
        hX.fst hkX z = hY.fst hkY z ∧ hX.snd hkX z = hY.snd hkY z := by
    intro k hk0 hk3 hkX hkY z
    have hz : (z : adjointGroup .F4 K) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} :=
      CFSG.LieType.CurtisTits.levi_mono _ (subset_one_two_of_not_mem
        (zero_not_mem_singleton_of_ne hk0)
        (by rw [Finset.mem_singleton]; exact fun h => hk3 h.symm)) z.2
    refine ⟨?_, ?_⟩
    · rw [hX.fst_eq_of_coe_eq hkX one_two_subset_X z ⟨z, hz⟩ rfl, (hagree _).1,
        hY.fst_eq_of_coe_eq one_two_subset_Y hkY ⟨z, hz⟩ z rfl]
    · rw [hX.snd_eq_of_coe_eq hkX one_two_subset_X z ⟨z, hz⟩ rfl, (hagree _).2,
        hY.snd_eq_of_coe_eq one_two_subset_Y hkY ⟨z, hz⟩ z rfl]
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · subst hi0 hj0
    rw [swapFamily_singleton_zero, swapFamily_singleton_zero, hY.conj_fst]
    exact hY.commute_fst_snd _ _ x y
  · subst hi0
    rw [swapFamily_singleton_zero, swapFamily_singleton_of_ne hj0, hX.conj_fst]
    by_cases hj3 : j = 3
    · subst hj3
      exact (hM03 x y).1
    · rw [(hag j hj0 hj3 _ (subset_nodes_Y_of_three_not_mem
        (by rw [Finset.mem_singleton]; exact fun h => hj3 h.symm)) y).2]
      exact hY.commute_fst_snd _ _ x y
  · subst hj0
    rw [swapFamily_singleton_of_ne hi0, swapFamily_singleton_zero, hY.conj_fst]
    by_cases hi3 : i = 3
    · subst hi3
      exact (hM03 y x).2
    · rw [(hag i hi0 hi3 _ (subset_nodes_Y_of_three_not_mem
        (by rw [Finset.mem_singleton]; exact fun h => hi3 h.symm)) x).1]
      exact hY.commute_fst_snd _ _ x y
  · rw [swapFamily_singleton_of_ne hi0, swapFamily_singleton_of_ne hj0, hX.conj_fst]
    exact hX.commute_fst_snd _ _ x y

theorem swapFamily_singleton_mul_conj (i : Fin (Tag.rank .F4))
    (hi : ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{i}, hi⟩) :
    swapFamily hX hY hcomm ⟨{i}, hi⟩ x * (t * swapFamily hX hY hcomm ⟨{i}, hi⟩ x * t⁻¹) =
      ((e.symm (x : adjointGroup .F4 K) : L) : G) := by
  by_cases hi0 : i = 0
  · subst hi0
    rw [swapFamily_singleton_zero, hY.conj_fst, hY.fst_mul_snd]
  · rw [swapFamily_singleton_of_ne hi0, hX.conj_fst, hX.fst_mul_snd]

end RankOne

section Generation


variable {K : Type} [Field K]

theorem iSup_levi_singleton_eq_top :
    ⨆ i : Fin (Tag.rank .F4),
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} = ⊤ := by
  have hgenK : ⨆ J, (Adjoint.f4Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem (Adjoint.f4Datum K).isFiniteType
        (Adjoint.f4Datum K).divisible) (Adjoint.f4_isCTGroupDatum K)
  rw [eq_top_iff, ← hgenK]
  refine iSup_le fun J => iSup₂_le fun j _ => ?_
  rw [← CFSG.LieType.CurtisTits.levi_singleton]
  exact le_iSup (fun i : Fin (Tag.rank .F4) =>
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i}) j

theorem top_le_of_forall_levi_singleton_le {H : Subgroup (adjointGroup .F4 K)}
    (h : ∀ i : Fin (Tag.rank .F4),
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} ≤ H) : ⊤ ≤ H := by
  rw [← iSup_levi_singleton_eq_top]
  exact iSup_le h

theorem hom_ext_of_forall_levi_singleton {M : Type*} [Group M] {f g : adjointGroup .F4 K →* M}
    (h : ∀ (i : Fin (Tag.rank .F4)) (x : adjointGroup .F4 K),
      x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} → f x = g x) : f = g := by
  have hle : ⊤ ≤ MonoidHom.eqLocus f g :=
    top_le_of_forall_levi_singleton_le fun i x hx => h i x hx
  exact MonoidHom.ext fun x => hle (mem_top x)

end Generation

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 K} {t : G}

theorem exists_injective_swapRow (hX : SwapNeighbourIso e t .X) (hY : SwapNeighbourIso e t .Y)
    (hX' : SwapNeighbourIso e t .X') (hq : 4 ≤ Nat.card K) :
    ∃ ψ : adjointGroup .F4 K →* G, Function.Injective ψ ∧
      (∀ x y, Commute (ψ x) (t * ψ y * t⁻¹)) ∧
      (∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G)) ∧
      ψ.range ⊔ ψ.range.map (MulAut.conj t).toMonoidHom =
        ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 := by
  obtain ⟨hY', hagree⟩ := exists_swapNeighbourIso_fst_eq hX hY hq
  have hM03 : ∀ g ∈ pieceCore e {0}, ∀ g' ∈ pieceCore e {3}, Commute g g' :=
    fun g hg g' hg' => commute_of_mem_pieceCore_zero_of_mem_pieceCore_three hX' hq hg hg'
  have hcomm : ∀ a b, Commute (hY'.fst zero_subset_Y a) (hX.fst three_subset_X b) := fun a b =>
    hM03 _ (hY'.range_fst_le_pieceCore hq zero_subset_Y (by decide) ⟨a, rfl⟩) _
      (hX.range_fst_le_pieceCore hq three_subset_X (by decide) ⟨b, rfl⟩)
  have hM03' : ∀ a b, Commute (hY'.fst zero_subset_Y a) (hX.snd three_subset_X b) ∧
      Commute (hX.fst three_subset_X b) (hY'.snd zero_subset_Y a) := fun a b =>
    ⟨hM03 _ (hY'.range_fst_le_pieceCore hq zero_subset_Y (by decide) ⟨a, rfl⟩) _
      (hX.range_snd_le_pieceCore hq three_subset_X (by decide) ⟨b, rfl⟩),
      (hM03 _ (hY'.range_snd_le_pieceCore hq zero_subset_Y (by decide) ⟨a, rfl⟩) _
        (hX.range_fst_le_pieceCore hq three_subset_X (by decide) ⟨b, rfl⟩)).symm⟩
  have hφ : IsCompatible (Adjoint.f4Datum K).leviAmalgam (swapFamily hX hY' hcomm) :=
    isCompatible_swapFamily fun x => (hagree x).1
  have hcard : ∀ i : Fin (Tag.rank .F4),
      ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2 := fun i => by simp
  set G₁ : Subgroup G := ⨆ J, (swapFamily hX hY' hcomm J).range with hG₁
  have hle : ∀ J x, swapFamily hX hY' hcomm J x ∈ G₁ := fun J x =>
    le_iSup (fun J => (swapFamily hX hY' hcomm J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (Adjoint.f4Datum K).leviAmalgam J →* G₁ :=
    fun J => (swapFamily hX hY' hcomm J).codRestrict G₁ (hle J) with hφ'def
  have hφ' : IsCompatible (Adjoint.f4Datum K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₁.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₁.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hX0 := (Adjoint.f4_steinbergExtras K).ne_bot (Pi.single 0 1)
      ((CFSG.LieType.RootSystem.isCTRootSystem _ _).single_mem 0)
    obtain ⟨u, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX0
    have hu0 : (u : adjointGroup .F4 K) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} := by
      rw [CFSG.LieType.CurtisTits.levi_singleton]
      exact mem_sup_left u.2
    refine ⟨⟨{0}, hcard 0⟩, ⟨u, hu0⟩, fun h => hu ?_⟩
    have h1 : swapFamily hX hY' hcomm ⟨{0}, hcard 0⟩ ⟨u, hu0⟩ = 1 := congrArg Subtype.val h
    rw [swapFamily_singleton_zero] at h1
    have h2 := hY'.fst_injective zero_subset_Y (h1.trans (map_one _).symm)
    have h3 : (u : adjointGroup .F4 K) = 1 := congrArg Subtype.val h2
    exact Subtype.ext h3
  obtain ⟨ψ₀, hψ₀, hsurj, hker⟩ := exists_surjective_of_isCompatible_f4 K φ' hφ' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans center_adjointGroup_eq_bot.le
  have hψφ : ∀ J (x : adjointGroup .F4 K) (hx : x ∈ (Adjoint.f4Datum K).leviAmalgam J),
      (G₁.subtype.comp ψ₀) x = swapFamily hX hY' hcomm J ⟨x, hx⟩ :=
    fun J x hx => congrArg Subtype.val (hψ₀ J ⟨x, hx⟩)
  have hrange : (G₁.subtype.comp ψ₀).range = G₁ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hinj : Function.Injective (G₁.subtype.comp ψ₀) := G₁.subtype_injective.comp hinj₀
  generalize G₁.subtype.comp ψ₀ = ψ at hrange hinj hψφ
  have hpair : ∀ (i j : Fin (Tag.rank .F4)) (x y : adjointGroup .F4 K),
      x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} →
      y ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {j} →
      Commute (ψ x) (t * ψ y * t⁻¹) := by
    intro i j x y hx hy
    rw [hψφ ⟨{i}, hcard i⟩ x hx, hψφ ⟨{j}, hcard j⟩ y hy]
    exact commute_swapFamily_singleton hagree hM03' i j (hcard i) (hcard j) ⟨x, hx⟩ ⟨y, hy⟩
  have hall : ∀ x y, Commute (ψ x) (t * ψ y * t⁻¹) := by
    have h1 : ∀ (i : Fin (Tag.rank .F4)) (x : adjointGroup .F4 K),
        x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} →
        ∀ y, Commute (ψ x) (t * ψ y * t⁻¹) := by
      intro i x hx y
      have hH : ⊤ ≤ (centralizer ({ψ x} : Set G)).comap ((MulAut.conj t).toMonoidHom.comp ψ) :=
        top_le_of_forall_levi_singleton_le fun j y' hy' => by
          rw [mem_comap, mem_centralizer_iff]
          rintro _ rfl
          exact (hpair i j x y' hx hy').eq
      have hy := hH (mem_top y)
      rw [mem_comap, mem_centralizer_iff] at hy
      exact hy _ rfl
    intro x y
    have hH : ⊤ ≤ (centralizer ({t * ψ y * t⁻¹} : Set G)).comap ψ :=
      top_le_of_forall_levi_singleton_le fun i x' hx' => by
        rw [mem_comap, mem_centralizer_iff]
        rintro _ rfl
        exact (h1 i x' hx' y).symm.eq
    have hx := hH (mem_top x)
    rw [mem_comap, mem_centralizer_iff] at hx
    exact (hx _ rfl).symm
  obtain ⟨δ, hδ⟩ : ∃ δ : adjointGroup .F4 K →* G, ∀ x, δ x = ψ x * (t * ψ x * t⁻¹) :=
    ⟨{ toFun := fun x => ψ x * (t * ψ x * t⁻¹)
       map_one' := by simp
       map_mul' := fun x y => by
         simp only [map_mul]
         have hc := (hall y x).eq
         calc ψ x * ψ y * (t * (ψ x * ψ y) * t⁻¹) =
             ψ x * (ψ y * (t * ψ x * t⁻¹)) * (t * ψ y * t⁻¹) := by group
           _ = ψ x * ((t * ψ x * t⁻¹) * ψ y) * (t * ψ y * t⁻¹) := by rw [hc]
           _ = ψ x * (t * ψ x * t⁻¹) * (ψ y * (t * ψ y * t⁻¹)) := by group }, fun x => rfl⟩
  have hδe : δ = L.subtype.comp e.symm.toMonoidHom :=
    hom_ext_of_forall_levi_singleton fun i x hx => by
      rw [hδ, hψφ ⟨{i}, hcard i⟩ x hx]
      exact swapFamily_singleton_mul_conj i (hcard i) ⟨x, hx⟩
  have hdiag : ∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G) := fun x => by
    rw [← hδ, hδe]
    rfl
  refine ⟨ψ, hinj, hall, hdiag, ?_⟩
  have hsupM : ∀ i : Fin (Tag.rank .F4), pieceCore e ({i} : Finset (Fin (Tag.rank .F4))) ≤
      ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 := fun i =>
    le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1)
      ⟨{i}, by simp⟩
  have hpiece1 : ∀ (i : Fin (Tag.rank .F4)) (x : adjointGroup .F4 K),
      x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} →
      ψ x ∈ pieceCore e ({i} : Finset (Fin (Tag.rank .F4))) ∧
        t * ψ x * t⁻¹ ∈ pieceCore e ({i} : Finset (Fin (Tag.rank .F4))) := by
    intro i x hx
    rw [hψφ ⟨{i}, hcard i⟩ x hx]
    by_cases hi0 : i = 0
    · subst hi0
      rw [swapFamily_singleton_zero, hY'.conj_fst]
      exact ⟨hY'.range_fst_le_pieceCore hq zero_subset_Y (by decide) ⟨_, rfl⟩,
        hY'.range_snd_le_pieceCore hq zero_subset_Y (by decide) ⟨_, rfl⟩⟩
    · rw [swapFamily_singleton_of_ne hi0, hX.conj_fst]
      exact ⟨hX.range_fst_le_pieceCore hq _ (by simp) ⟨_, rfl⟩,
        hX.range_snd_le_pieceCore hq _ (by simp) ⟨_, rfl⟩⟩
  have hle1 : ψ.range ≤ ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 := by
    rintro _ ⟨x, rfl⟩
    have hH : ⊤ ≤ (⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
        pieceCore e J.1).comap ψ :=
      top_le_of_forall_levi_singleton_le fun i x hx => hsupM i (hpiece1 i x hx).1
    exact hH (mem_top x)
  have hle2 : ψ.range.map (MulAut.conj t).toMonoidHom ≤
      ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hH : ⊤ ≤ (⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
        pieceCore e J.1).comap ((MulAut.conj t).toMonoidHom.comp ψ) :=
      top_le_of_forall_levi_singleton_le fun i x hx => hsupM i (hpiece1 i x hx).2
    exact hH (mem_top x)
  have hclaim : ∀ (N : AmalgamNeighbour) (h : SwapNeighbourIso e t N)
      {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2),
      (∀ x, h.fst hJ x ∈ ψ.range) →
        pieceCore e J ≤ ψ.range ⊔ ψ.range.map (MulAut.conj t).toMonoidHom := by
    intro N h J hJ hJ2 hmem
    rw [← h.range_fst_sup_range_snd hq hJ hJ2]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact hmem x
    · rintro _ ⟨x, rfl⟩
      rw [← h.conj_fst]
      exact ⟨_, hmem x, rfl⟩
  have hY0 : pieceCore e {0} ≤ ψ.range ⊔ ψ.range.map (MulAut.conj t).toMonoidHom :=
    hclaim .Y hY' zero_subset_Y (by decide) fun x =>
      ⟨x, (hψφ ⟨{0}, hcard 0⟩ x x.2).trans (swapFamily_singleton_zero _ _)⟩
  have hX3 : pieceCore e {3} ≤ ψ.range ⊔ ψ.range.map (MulAut.conj t).toMonoidHom :=
    hclaim .X hX three_subset_X (by decide) fun x =>
      ⟨x, (hψφ ⟨{3}, hcard 3⟩ x x.2).trans (swapFamily_singleton_of_ne
        (show (3 : Fin (Tag.rank .F4)) ≠ 0 by decide) _ _)⟩
  refine le_antisymm (sup_le hle1 hle2) (iSup_le fun J => ?_)
  by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
  · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
    · rw [eq_pair_zero_three J.2 h0 h3]
      exact (pieceCore_zero_three_le_sup hX' hq).trans (sup_le hY0 hX3)
    · exact hclaim .Y hY' (subset_nodes_Y_of_three_not_mem h3) J.2 fun x =>
        ⟨x, (hψφ ⟨J.1, J.2⟩ x x.2).trans (swapFamily_of_three_not_mem h0 h3 _)⟩
  · exact hclaim .X hX (subset_nodes_X_of_zero_not_mem h0) J.2 fun x =>
      ⟨x, (hψφ ⟨J.1, J.2⟩ x x.2).trans (swapFamily_of_zero_not_mem h0 _)⟩

theorem exists_injective_swapRow_of_mem_centralizer (hX : SwapNeighbourIso e t .X)
    (hY : SwapNeighbourIso e t .Y) (htL : t ∈ centralizer (L : Set G)) (hq : 4 ≤ Nat.card K) :
    ∃ ψ : adjointGroup .F4 K →* G, Function.Injective ψ ∧
      (∀ x y, Commute (ψ x) (t * ψ y * t⁻¹)) ∧
      (∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G)) ∧
      ψ.range ⊔ ψ.range.map (MulAut.conj t).toMonoidHom =
        ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 :=
  exists_injective_swapRow hX hY (hX.toX' (commute_symm_n1242_of_mem_centralizer htL)) hq

theorem exists_swapFactors (hX : SwapNeighbourIso e t .X) (hY : SwapNeighbourIso e t .Y)
    (hX' : SwapNeighbourIso e t .X') (hq : 4 ≤ Nat.card K) :
    ∃ (G₁ G₂ : Subgroup G) (ε : G₁ ≃* adjointGroup .F4 K),
      G₂ ≤ centralizer (G₁ : Set G) ∧ G₁.map (MulAut.conj t).toMonoidHom = G₂ ∧
      G₁ ⊔ G₂ = ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 ∧
      ∀ g : G₁, (g : G) * (t * g * t⁻¹) = ((e.symm (ε g) : L) : G) := by
  obtain ⟨ψ, hinj, hall, hdiag, hsup⟩ := exists_injective_swapRow hX hY hX' hq
  refine ⟨ψ.range, ψ.range.map (MulAut.conj t).toMonoidHom, (MonoidHom.ofInjective hinj).symm,
    ?_, rfl, hsup, ?_⟩
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact (hall x y).eq
  · rintro ⟨_, y, rfl⟩
    have hy : (MonoidHom.ofInjective hinj).symm ⟨ψ y, y, rfl⟩ = y :=
      (MulEquiv.symm_apply_eq _).2 (Subtype.ext rfl)
    rw [hy]
    exact hdiag y

theorem false_of_simple_of_swapRow [IsSimpleGroup G] (hX : SwapNeighbourIso e t .X)
    (hY : SwapNeighbourIso e t .Y) (hX' : SwapNeighbourIso e t .X') (hq : 4 ≤ Nat.card K)
    (ht : orderOf t = 2) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ J : {J : Finset (Fin (Tag.rank .F4)) //
        J.card ≤ 2}, pieceCore e J.1 : Subgroup G) : Set G) →
      g ∈ normalizer ((⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
        pieceCore e J.1 : Subgroup G) : Set G)) : False := by
  obtain ⟨G₁, G₂, ε, h₁₂, hswap, hsup, -⟩ := exists_swapFactors hX hY hX' hq
  rw [← hsup] at huniq
  exact false_of_simple_of_swap_F4 ht hf hK ε h₁₂ hswap huniq

end Main

end CFSG.SeitzReduction.F4Pilot
