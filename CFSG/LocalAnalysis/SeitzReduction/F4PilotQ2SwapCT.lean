module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapRigid
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2SwapCTNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Pieces


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem coe_symm_mem_subgroupToG (e : L ≃* adjointGroup .F4 K)
    {A : Subgroup (adjointGroup .F4 K)} {x : adjointGroup .F4 K} (hx : x ∈ A) :
    ((e.symm x : L) : G) ∈ subgroupToG e A :=
  Subgroup.mem_map_of_mem L.subtype (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx)

theorem exists_eq_of_mem_subgroupToG (e : L ≃* adjointGroup .F4 K)
    {A : Subgroup (adjointGroup .F4 K)} {g : G} (hg : g ∈ subgroupToG e A) :
    ∃ x ∈ A, ((e.symm x : L) : G) = g := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hg
  exact ⟨x, hx, rfl⟩

theorem subgroupToG_mono (e : L ≃* adjointGroup .F4 K) {A B : Subgroup (adjointGroup .F4 K)}
    (h : A ≤ B) : subgroupToG e A ≤ subgroupToG e B :=
  map_mono (map_mono h)

theorem subgroupToG_le (e : L ≃* adjointGroup .F4 K) (A : Subgroup (adjointGroup .F4 K)) :
    subgroupToG e A ≤ L :=
  map_subtype_le _

variable {t : G} {D : Subgroup G}

@[expose] noncomputable def paramLft (P : SwapParam t D) (e : L ≃* adjointGroup .F4 K)
    {A : Subgroup (adjointGroup .F4 K)} (hA : subgroupToG e A ≤ D) : A →* G :=
  P.Ψ.comp ((MonoidHom.inl D D).comp
    ((L.subtype.comp (e.symm.toMonoidHom.comp A.subtype)).codRestrict D fun x =>
      hA (coe_symm_mem_subgroupToG e x.2)))

theorem paramLft_apply (P : SwapParam t D) (e : L ≃* adjointGroup .F4 K)
    {A : Subgroup (adjointGroup .F4 K)} (hA : subgroupToG e A ≤ D) (x : A) :
    paramLft P e hA x = P.lft ((e.symm x : L) : G) := by
  rw [P.lft_of_mem (hA (coe_symm_mem_subgroupToG e x.2))]
  rfl

end Pieces

section Family


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem subgroupToG_trans_graphAutF4_symm_C3Levi (e : L ≃* adjointGroup .F4 K) :
    subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K) = subgroupToG e (B3Levi K) := by
  rw [subgroupToG, subgroupToG, ← map_graphAutF4_C3Levi, Subgroup.map_map, Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem subgroupToG_levi_le_C3Levi (e : L ≃* adjointGroup .F4 K)
    {J : Finset (Fin (Tag.rank .F4))} (h0 : (0 : Fin (Tag.rank .F4)) ∉ J) :
    subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) ≤
      subgroupToG e (C3Levi K) :=
  subgroupToG_mono e (levi_le_C3Levi h0)

theorem subgroupToG_levi_le_B3Levi (e : L ≃* adjointGroup .F4 K)
    {J : Finset (Fin (Tag.rank .F4))} (h3 : (3 : Fin (Tag.rank .F4)) ∉ J) :
    subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) ≤
      subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K) := by
  rw [subgroupToG_trans_graphAutF4_symm_C3Levi]
  exact subgroupToG_mono e (levi_le_B3Levi h3)

variable {t : G} (e : L ≃* adjointGroup .F4 K) (P : SwapParam t (subgroupToG e (C3Levi K)))
  (P' : SwapParam t (subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K)))

theorem zero_not_mem_three : (0 : Fin (Tag.rank .F4)) ∉ ({3} : Finset (Fin (Tag.rank .F4))) := by
  decide

theorem three_not_mem_zero : (3 : Fin (Tag.rank .F4)) ∉ ({0} : Finset (Fin (Tag.rank .F4))) := by
  decide

@[expose] noncomputable def q2SwapPairLift
    (hcomm : ∀ a b, Commute (paramLft P' e (subgroupToG_levi_le_B3Levi e three_not_mem_zero) a)
      (paramLft P e (subgroupToG_levi_le_C3Levi e zero_not_mem_three) b)) :
    ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) →* G :=
  supLift commute_levi_zero_three levi_zero_inf_levi_three_eq_bot
    (paramLft P' e (subgroupToG_levi_le_B3Levi e three_not_mem_zero))
    (paramLft P e (subgroupToG_levi_le_C3Levi e zero_not_mem_three)) hcomm

variable {e P P'}

theorem q2SwapPairLift_of_mem_left
    {hcomm : ∀ a b, Commute (paramLft P' e (subgroupToG_levi_le_B3Levi e three_not_mem_zero) a)
      (paramLft P e (subgroupToG_levi_le_C3Levi e zero_not_mem_three) b)}
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}) :
    q2SwapPairLift e P P' hcomm z = P'.lft ((e.symm z : L) : G) := by
  have h := supLift_apply_left commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm
    (⟨z, hz⟩ : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0})
  rw [paramLft_apply] at h
  exact h

theorem q2SwapPairLift_of_mem_right
    {hcomm : ∀ a b, Commute (paramLft P' e (subgroupToG_levi_le_B3Levi e three_not_mem_zero) a)
      (paramLft P e (subgroupToG_levi_le_C3Levi e zero_not_mem_three) b)}
    (z : ↥(CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ⊔
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))
    (hz : (z : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) :
    q2SwapPairLift e P P' hcomm z = P.lft ((e.symm z : L) : G) := by
  have h := supLift_apply_right commute_levi_zero_three levi_zero_inf_levi_three_eq_bot hcomm
    (⟨z, hz⟩ : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3})
  rw [paramLft_apply] at h
  exact h

variable (e P P')

@[expose] noncomputable def q2SwapFamily
    (hcomm : ∀ a b, Commute (paramLft P' e (subgroupToG_levi_le_B3Levi e three_not_mem_zero) a)
      (paramLft P e (subgroupToG_levi_le_C3Levi e zero_not_mem_three) b))
    (J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}) :
    (Adjoint.f4Datum K).leviAmalgam J →* G :=
  if h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1 then
    if h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1 then
      (q2SwapPairLift e P P' hcomm).comp
        (Subgroup.inclusion (levi_le_sup_of_mem_of_mem J.2 h0 h3))
    else paramLft P' e (subgroupToG_levi_le_B3Levi e h3)
  else paramLft P e (subgroupToG_levi_le_C3Levi e h0)

variable {e P P'}
  {hcomm : ∀ a b, Commute (paramLft P' e (subgroupToG_levi_le_B3Levi e three_not_mem_zero) a)
      (paramLft P e (subgroupToG_levi_le_C3Levi e zero_not_mem_three) b)}

theorem q2SwapFamily_of_zero_not_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J.1) (x : (Adjoint.f4Datum K).leviAmalgam J) :
    q2SwapFamily e P P' hcomm J x = P.lft ((e.symm x : L) : G) := by
  rw [q2SwapFamily, dite_eq_right h0, paramLft_apply]

theorem q2SwapFamily_of_three_not_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∉ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    q2SwapFamily e P P' hcomm J x = P'.lft ((e.symm x : L) : G) := by
  rw [q2SwapFamily, dite_eq_left h0, dite_eq_right h3, paramLft_apply]

theorem q2SwapFamily_of_mem_of_mem
    {J : {J : Finset (Fin (Adjoint.f4Datum K).rank) // J.card ≤ 2}}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1)
    (x : (Adjoint.f4Datum K).leviAmalgam J) :
    q2SwapFamily e P P' hcomm J x =
      q2SwapPairLift e P P' hcomm ⟨x, levi_le_sup_of_mem_of_mem J.2 h0 h3 x.2⟩ := by
  rw [q2SwapFamily, dite_eq_left h0, dite_eq_left h3]
  rfl

theorem isCompatible_q2SwapFamily
    (hagree : AgreeOn P P'
      (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2}))) :
    IsCompatible (Adjoint.f4Datum K).leviAmalgam (q2SwapFamily e P P' hcomm) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .F4))) ⊆ j.1 := hij
  by_cases h0j : (0 : Fin (Tag.rank .F4)) ∈ j.1
  · by_cases h3j : (3 : Fin (Tag.rank .F4)) ∈ j.1
    · have hj : (j.1 : Finset (Fin (Tag.rank .F4))) = {0, 3} := eq_pair_zero_three j.2 h0j h3j
      rw [q2SwapFamily_of_mem_of_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · by_cases h3i : (3 : Fin (Tag.rank .F4)) ∈ i.1
        · rw [q2SwapFamily_of_mem_of_mem h0i h3i]
          exact congrArg (q2SwapPairLift e P P' hcomm) (Subtype.ext hxy)
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
          rw [q2SwapFamily_of_three_not_mem h0i h3i, q2SwapPairLift_of_mem_left _ hy0, hxy]
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
        rw [q2SwapFamily_of_zero_not_mem h0i, q2SwapPairLift_of_mem_right _ hy3, hxy]
    · have h3i : (3 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h3j (hsub h)
      rw [q2SwapFamily_of_three_not_mem h0j h3j]
      by_cases h0i : (0 : Fin (Tag.rank .F4)) ∈ i.1
      · rw [q2SwapFamily_of_three_not_mem h0i h3i, hxy]
      · rw [q2SwapFamily_of_zero_not_mem h0i, ← hxy]
        have hx12 : (x : adjointGroup .F4 K) ∈
            CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} :=
          CFSG.LieType.CurtisTits.levi_mono _ (subset_one_two_of_not_mem h0i h3i) x.2
        exact (hagree _ (coe_symm_mem_subgroupToG e hx12)).symm
  · have h0i : (0 : Fin (Tag.rank .F4)) ∉ i.1 := fun h => h0j (hsub h)
    rw [q2SwapFamily_of_zero_not_mem h0i, q2SwapFamily_of_zero_not_mem h0j, hxy]

theorem q2SwapFamily_singleton_zero
    (h : ({0} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{0}, h⟩) :
    q2SwapFamily e P P' hcomm ⟨{0}, h⟩ x = P'.lft ((e.symm x : L) : G) :=
  q2SwapFamily_of_three_not_mem (Finset.mem_singleton_self _) three_not_mem_zero x

theorem q2SwapFamily_singleton_of_ne {i : Fin (Tag.rank .F4)} (hi : i ≠ 0)
    (h : ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{i}, h⟩) :
    q2SwapFamily e P P' hcomm ⟨{i}, h⟩ x = P.lft ((e.symm x : L) : G) :=
  q2SwapFamily_of_zero_not_mem (zero_not_mem_singleton_of_ne hi) x

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem commute_conj_of_commute_conj {t : G} (ht2 : t * t = 1) {a b : G}
    (h : Commute a (t * b * t⁻¹)) : Commute b (t * a * t⁻¹) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h1 := h.map (MulAut.conj t).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have e1 : t * (t * b * t⁻¹) * t⁻¹ = b := by
    rw [htinv]
    calc t * (t * b * t) * t = (t * t) * b * (t * t) := by group
      _ = b := by rw [ht2, one_mul, mul_one]
  rw [e1] at h1
  exact h1.symm

theorem commute_q2SwapFamily_singleton (ht2 : t * t = 1)
    (hagree : AgreeOn P P'
      (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2})))
    (hcomm' : ∀ a ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}),
      ∀ b ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}),
      Commute (P'.lft a) (t * P.lft b * t⁻¹))
    (i j : Fin (Tag.rank .F4)) (hi : ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (hj : ({j} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{i}, hi⟩)
    (y : (Adjoint.f4Datum K).leviAmalgam ⟨{j}, hj⟩) :
    Commute (q2SwapFamily e P P' hcomm ⟨{i}, hi⟩ x)
      (t * q2SwapFamily e P P' hcomm ⟨{j}, hj⟩ y * t⁻¹) := by
  have hag : ∀ k : Fin (Tag.rank .F4), k ≠ 0 → k ≠ 3 → ∀ z : adjointGroup .F4 K,
      z ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {k} →
      P.lft ((e.symm z : L) : G) = P'.lft ((e.symm z : L) : G) := by
    intro k hk0 hk3 z hz
    have hz12 : z ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2} :=
      CFSG.LieType.CurtisTits.levi_mono _ (subset_one_two_of_not_mem
        (zero_not_mem_singleton_of_ne hk0)
        (by rw [Finset.mem_singleton]; exact fun h => hk3 h.symm)) hz
    exact (hagree _ (coe_symm_mem_subgroupToG e hz12)).symm
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · subst hi0 hj0
    rw [q2SwapFamily_singleton_zero, q2SwapFamily_singleton_zero]
    exact P'.commute_lft_conj_lft _ _
  · subst hi0
    rw [q2SwapFamily_singleton_zero, q2SwapFamily_singleton_of_ne hj0]
    by_cases hj3 : j = 3
    · subst hj3
      exact hcomm' _ (coe_symm_mem_subgroupToG e x.2) _ (coe_symm_mem_subgroupToG e y.2)
    · rw [hag j hj0 hj3 _ y.2]
      exact P'.commute_lft_conj_lft _ _
  · subst hj0
    rw [q2SwapFamily_singleton_of_ne hi0, q2SwapFamily_singleton_zero]
    by_cases hi3 : i = 3
    · subst hi3
      exact commute_conj_of_commute_conj ht2
        (hcomm' _ (coe_symm_mem_subgroupToG e y.2) _ (coe_symm_mem_subgroupToG e x.2))
    · rw [hag i hi0 hi3 _ x.2]
      exact P'.commute_lft_conj_lft _ _
  · rw [q2SwapFamily_singleton_of_ne hi0, q2SwapFamily_singleton_of_ne hj0]
    exact P.commute_lft_conj_lft _ _

theorem q2SwapFamily_singleton_mul_conj (i : Fin (Tag.rank .F4))
    (hi : ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2)
    (x : (Adjoint.f4Datum K).leviAmalgam ⟨{i}, hi⟩) :
    q2SwapFamily e P P' hcomm ⟨{i}, hi⟩ x * (t * q2SwapFamily e P P' hcomm ⟨{i}, hi⟩ x * t⁻¹) =
      ((e.symm (x : adjointGroup .F4 K) : L) : G) := by
  by_cases hi0 : i = 0
  · subst hi0
    rw [q2SwapFamily_singleton_zero]
    exact P'.lft_mul_conj_lft
      (subgroupToG_levi_le_B3Levi e three_not_mem_zero (coe_symm_mem_subgroupToG e x.2))
  · rw [q2SwapFamily_singleton_of_ne hi0]
    exact P.lft_mul_conj_lft (subgroupToG_levi_le_C3Levi e
      (zero_not_mem_singleton_of_ne hi0) (coe_symm_mem_subgroupToG e x.2))

end Family

section Main


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem range_inf_map_conj_eq_bot_F4 {t : G} {ψ : adjointGroup .F4 K →* G}
    (hinj : Function.Injective ψ) (hall : ∀ x y, Commute (ψ x) (t * ψ y * t⁻¹)) :
    ψ.range ⊓ ψ.range.map (MulAut.conj t).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨⟨c, rfl⟩, ⟨_, ⟨c', rfl⟩, hz⟩⟩
  have hz' : t * ψ c' * t⁻¹ = ψ c := hz
  have hc : c ∈ center (adjointGroup .F4 K) := by
    rw [mem_center_iff]
    intro a
    apply hinj
    rw [map_mul, map_mul, ← hz']
    exact (hall a c').eq
  rw [center_adjointGroup_eq_bot, mem_bot] at hc
  rw [mem_bot, hc, map_one]

theorem exists_swapFactors_of_coherent_F4_two {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (P : SwapParam t (subgroupToG e (C3Levi K)))
    (hinj : Function.Injective P.Ψ)
    (hrange : P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀))
    (P' : SwapParam t (subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K)))
    (hagree : AgreeOn P P'
      (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2})))
    (hcomm : ∀ a ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}),
      ∀ b ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}),
      Commute (P'.lft a) (P.lft b) ∧ Commute (P'.lft a) (t * P.lft b * t⁻¹)) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      centralizerPerfectCore (subgroupToG e X₀) ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hc : ∀ a b, Commute (paramLft P' e (subgroupToG_levi_le_B3Levi e three_not_mem_zero) a)
      (paramLft P e (subgroupToG_levi_le_C3Levi e zero_not_mem_three) b) := fun a b => by
    rw [paramLft_apply, paramLft_apply]
    exact (hcomm _ (coe_symm_mem_subgroupToG e a.2) _ (coe_symm_mem_subgroupToG e b.2)).1
  have hφ : IsCompatible (Adjoint.f4Datum K).leviAmalgam (q2SwapFamily e P P' hc) :=
    isCompatible_q2SwapFamily hagree
  have hcard : ∀ i : Fin (Tag.rank .F4),
      ({i} : Finset (Fin (Adjoint.f4Datum K).rank)).card ≤ 2 := fun i => by simp
  set G₁ : Subgroup G := ⨆ J, (q2SwapFamily e P P' hc J).range with hG₁
  have hle : ∀ J x, q2SwapFamily e P P' hc J x ∈ G₁ := fun J x =>
    le_iSup (fun J => (q2SwapFamily e P P' hc J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (Adjoint.f4Datum K).leviAmalgam J →* G₁ :=
    fun J => (q2SwapFamily e P P' hc J).codRestrict G₁ (hle J) with hφ'def
  have hφ' : IsCompatible (Adjoint.f4Datum K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₁.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₁.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hX1 := (Adjoint.f4_steinbergExtras K).ne_bot (Pi.single 1 1)
      ((CFSG.LieType.RootSystem.isCTRootSystem _ _).single_mem 1)
    obtain ⟨u, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX1
    have hu1 : (u : adjointGroup .F4 K) ∈
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} := by
      rw [CFSG.LieType.CurtisTits.levi_singleton]
      exact mem_sup_left u.2
    have h10 : (1 : Fin (Tag.rank .F4)) ≠ 0 := by decide
    refine ⟨⟨{1}, hcard 1⟩, ⟨u, hu1⟩, fun h => hu ?_⟩
    have h1 : q2SwapFamily e P P' hc ⟨{1}, hcard 1⟩ ⟨u, hu1⟩ = 1 := congrArg Subtype.val h
    rw [q2SwapFamily_singleton_of_ne h10] at h1
    have hmem := subgroupToG_levi_le_C3Levi e (zero_not_mem_singleton_of_ne h10)
      (coe_symm_mem_subgroupToG e hu1)
    have h2 := swapParam_lft_injOn P hinj hmem (one_mem _)
      (h1.trans (swapParam_lft_one P).symm)
    have h3 : e.symm (u : adjointGroup .F4 K) = 1 := Subtype.ext h2
    have h4 : (u : adjointGroup .F4 K) = 1 := by
      have := congrArg e h3
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact Subtype.ext h4
  obtain ⟨ψ₀, hψ₀, hsurj, hker⟩ := exists_surjective_of_isCompatible_f4 K φ' hφ' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans center_adjointGroup_eq_bot.le
  have hψφ : ∀ J (x : adjointGroup .F4 K) (hx : x ∈ (Adjoint.f4Datum K).leviAmalgam J),
      (G₁.subtype.comp ψ₀) x = q2SwapFamily e P P' hc J ⟨x, hx⟩ :=
    fun J x hx => congrArg Subtype.val (hψ₀ J ⟨x, hx⟩)
  have hinjψ : Function.Injective (G₁.subtype.comp ψ₀) := G₁.subtype_injective.comp hinj₀
  generalize G₁.subtype.comp ψ₀ = ψ at hinjψ hψφ
  have hcomm' : ∀ a ∈ subgroupToG e
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}),
      ∀ b ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}),
      Commute (P'.lft a) (t * P.lft b * t⁻¹) := fun a ha b hb => (hcomm a ha b hb).2
  have hpair : ∀ (i j : Fin (Tag.rank .F4)) (x y : adjointGroup .F4 K),
      x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} →
      y ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {j} →
      Commute (ψ x) (t * ψ y * t⁻¹) := by
    intro i j x y hx hy
    rw [hψφ ⟨{i}, hcard i⟩ x hx, hψφ ⟨{j}, hcard j⟩ y hy]
    exact commute_q2SwapFamily_singleton htt hagree hcomm' i j (hcard i) (hcard j) ⟨x, hx⟩
      ⟨y, hy⟩
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
      exact q2SwapFamily_singleton_mul_conj i (hcard i) ⟨x, hx⟩
  have hdiag : ∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G) := fun x => by
    rw [← hδ, hδe]
    rfl
  have hQ : CFSG.Open.IsQuasisimple (adjointGroup .F4 K) :=
    ⟨(Adjoint.isQuasisimple_f4 K).1.commutator_eq_top, (Adjoint.isQuasisimple_f4 K).2.1⟩
  have hq : CFSG.Open.IsQuasisimple ψ.range :=
    isQuasisimple_open_of_mulEquiv (MonoidHom.ofInjective hinjψ) hQ
  have h₁₂ : ψ.range.map (MulAut.conj t).toMonoidHom ≤ centralizer (ψ.range : Set G) := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact (hall x y).eq
  refine ⟨ψ.range, hq, h₁₂, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [hdiag x]
    exact (e.symm x).2
  · intro y hy
    refine ⟨ψ (e ⟨y, hy⟩), ⟨_, rfl⟩, ?_⟩
    rw [hdiag, MulEquiv.symm_apply_apply]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨-, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set D₁ : Subgroup G := (C3Levi K).map ψ with hD₁def
  have htX : t ∈ centralizer (X : Set G) :=
    centralizer_le (subgroupToG_le e X₀) hw.mem_centralizer
  have hD₁X : D₁ ≤ centralizer (X : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := exists_eq_of_mem_subgroupToG e hx
    have hcx : c * x₀ = x₀ * c := mem_centralizer_iff.1 (hX₀D hx₀) c hc
    have h1 : Commute (ψ c) (ψ x₀) := by
      change ψ c * ψ x₀ = ψ x₀ * ψ c
      rw [← map_mul, ← map_mul, hcx]
    rw [← hdiag x₀]
    exact ((h1.mul_right (hall c x₀)).eq).symm
  have hC3perf : ⁅C3Levi K, C3Levi K⁆ = C3Levi K := isPerfect_iff.mp isQuasisimple_C3Levi.1
  have hD₁perf : ⁅D₁, D₁⁆ = D₁ := by rw [hD₁def, ← map_commutator, hC3perf]
  have hD₁E : D₁ ≤ centralizerPerfectCore X :=
    CFSG.Quasithin.le_perfectCore_of_perfect hD₁X hD₁perf
  have hD₁tE : D₁.map (MulAut.conj t).toMonoidHom ≤ centralizerPerfectCore X := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_centralizerPerfectCore_of_mem_centralizer htX (hD₁E hy)
  have hcomm₁ : ∀ a ∈ D₁, ∀ b ∈ D₁.map (MulAut.conj t).toMonoidHom, Commute a b := by
    rintro _ ⟨c, -, rfl⟩ _ ⟨_, ⟨c', -, rfl⟩, rfl⟩
    exact hall c c'
  have hdisj : D₁ ⊓ D₁.map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (inf_le_inf (map_mono le_top) (map_mono (map_mono le_top))) ?_
    rw [← MonoidHom.range_eq_map, range_inf_map_conj_eq_bot_F4 hinjψ hall]
  have hcardD₁ : Nat.card D₁ = Nat.card (C3Levi K) :=
    Subgroup.card_map_of_injective hinjψ
  have hcardD₁t : Nat.card (D₁.map (MulAut.conj t).toMonoidHom) = Nat.card (C3Levi K) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hcardD₁]
  have hcardD : Nat.card (subgroupToG e (C3Levi K)) = Nat.card (C3Levi K) := by
    rw [subgroupToG, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hcardE :
      Nat.card (centralizerPerfectCore X) = Nat.card (C3Levi K) * Nat.card (C3Levi K) := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hcardD]
  have hcardS : Nat.card (D₁ ⊔ D₁.map (MulAut.conj t).toMonoidHom : Subgroup G) =
      Nat.card (C3Levi K) * Nat.card (C3Levi K) := by
    rw [Nat.card_congr (supMulEquivProd hcomm₁ hdisj).toEquiv, Nat.card_prod, hcardD₁,
      hcardD₁t]
  have hEq : D₁ ⊔ D₁.map (MulAut.conj t).toMonoidHom = centralizerPerfectCore X :=
    Subgroup.eq_of_le_of_card_ge (sup_le hD₁E hD₁tE) (by rw [hcardE, hcardS])
  rw [← hEq]
  exact sup_le_sup (map_le_range ψ (C3Levi K)) (map_mono (map_le_range ψ (C3Levi K)))

end Main

end CFSG.SeitzReduction.F4Pilot
