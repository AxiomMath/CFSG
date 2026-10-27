module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.RankThree.PartOne.S12K.OrdRigid
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatCovers

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification

@[expose] def SL2EvenTypeDet : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
    LieModel X .PSL 2 2 f → StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' →
      t = .PSL ∧ n = 2 ∧ f' = f

theorem evenLieOrder_eq_ordA_one {t : StatedLieTag} {n g f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hf : 1 ≤ f)
    (h : F4Pilot.evenLieOrder t n g = Open.ordA 1 (2 ^ f)) : t = .PSL ∧ n = 2 ∧ g = f := by
  have h' : RankThree.PartOne.S12K.charTwoOrder t n g = Open.ordA 1 (2 ^ f) := by
    cases t
    case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
    all_goals exact h
  exact RankThree.PartOne.S12K.rigid_L hadm hf h'

theorem card_of_lieModel_PSL_two_two {X : Type} [Group X] {f : ℕ} (h : LieModel X .PSL 2 2 f) :
    Nat.card X = Open.ordA 1 (2 ^ f) :=
  LinearPilot.card_of_lieModel_PSL_two h

theorem two_le_of_lieModel_PSL_two_two {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSL 2 2 f) : 2 ≤ f := by
  obtain ⟨-, hf, -, h22, -⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
  by_contra hlt
  obtain rfl : f = 1 := by omega
  exact h22 rfl

theorem lieModel_PSL_two_two_unique_classicalOrSuzuki_of_card_eq
    {X Y : Type} [Group X] [Group Y] {f : ℕ} (hX : LieModel X .PSL 2 2 f) {t : StatedLieTag}
    {n f' : ℕ} (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSL ∧ n = 2 ∧ f' = f := by
  have he := F4Pilot.card_eq_evenLieOrder_of_classicalOrSuzuki ht h
  rw [hcard, card_of_lieModel_PSL_two_two hX] at he
  exact evenLieOrder_eq_ordA_one (F4Pilot.statedLieAdmissible_of_lieModel h)
    (F4Pilot.statedLieAdmissible_of_lieModel hX).2.1 he.symm

section Orders


theorem lieModel_PSL_two_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {f : ℕ}
    (hX : LieModel X .PSL 2 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSL ∧ n = 2 ∧ f' = f := by
  have he := F4Pilot.card_eq_evenLieOrder h
  rw [hcard, card_of_lieModel_PSL_two_two hX] at he
  exact evenLieOrder_eq_ordA_one (F4Pilot.statedLieAdmissible_of_lieModel h)
    (F4Pilot.statedLieAdmissible_of_lieModel hX).2.1 he.symm

theorem sl2EvenTypeDet : SL2EvenTypeDet :=
  fun _ _ _ _ _ _ hX _ h => lieModel_PSL_two_two_unique_of_card_eq hX h rfl

end Orders

theorem sl2TypeDet_of_simple (hdet : SL2EvenTypeDet) {D : Type} [Group D]
    (hq : IsQuasisimple D) (hs : IsSimpleGroup D) {f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 f) {t : StatedLieTag} {n f' : ℕ}
    (hadm : StatedLieAdmissible t n 2 f') (hD : LieModel D t n 2 f') :
    t = .PSL ∧ n = 2 ∧ f' = f :=
  hdet (D ⧸ center D) f t n f' hDm hadm
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot
      (F4Pilot.center_eq_bot_of_isQuasisimple hq hs) hD)

theorem sixty_le_ordA_one {f : ℕ} (hf : 2 ≤ f) : 60 ≤ Open.ordA 1 (2 ^ f) := by
  rw [RankThree.PartOne.S12K.ordA_one_eq (by omega)]
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h16 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
  have : 15 ≤ (2 ^ f) ^ 2 - 1 := by omega
  nlinarith

theorem ordA_one_ne_360 {f : ℕ} (hf : 1 ≤ f) : Open.ordA 1 (2 ^ f) ≠ 360 := by
  intro h
  rw [RankThree.PartOne.S12K.ordA_one_eq hf] at h
  have h3 : f = 3 := Timmesfeld.Orders.eq_of_two_pow_mul_odd
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by omega)) (by decide : Odd 45)
    (h.trans (by norm_num : (360 : ℕ) = 2 ^ 3 * 45))
  subst h3
  revert h
  decide

theorem eq_commutator_of_isComponent {G : Type*} [Group G] {D : Subgroup G} (hD : IsComponent D)
    (hs : IsSimpleGroup (commutator G)) : D = commutator G := by
  have : Group.IsPerfect D := hD.1.1
  have hle : D ≤ commutator G := by
    calc D = ⁅D, D⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (commutator_def G).symm
  have hsub : (D.subgroupOf (commutator G)).IsSubnormal := hD.2.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs hsub with h | h
  · exfalso
    have hne : D ≠ ⊥ := (nontrivial_iff_ne_bot D).mp (LocalCores.isQuasisimple_nontrivial hD.1)
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hle hx⟩ : ↥(commutator G)) ∈ D.subgroupOf (commutator G) := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

theorem card_eq_of_isComponent_statedSp_two_two {X : Type} [Group X] {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2) (Φ : X ≃* StatedSp 2 k) {D : Subgroup X}
    (hD : IsComponent D) : IsSimpleGroup D ∧ Nat.card D = 360 := by
  have := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  let e : X ≃* Equiv.Perm (Fin 6) :=
    Φ.trans (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm k hk')
  have hmap : (commutator X).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def,
      alternatingGroup.commutator_perm_eq (by simp)]
  let eA : ↥(commutator X) ≃* ↥(alternatingGroup (Fin 6)) :=
    ((commutator X).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hA6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥(commutator X) := eA.isSimpleGroup
  have hDc := eq_commutator_of_isComponent hD hs
  have hcard6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hDc]
    exact hs
  · rw [hDc, Nat.card_congr eA.toEquiv, hcard6]

theorem rank_eq_one_of_isComponent_statedSp (hdet : SL2EvenTypeDet) {X : Type} [Group X]
    [Finite X] {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 f) : r = 1 ∧ g = f := by
  have hg : 1 ≤ g := by
    by_contra h0
    have hk1 : Nat.card k = 1 := by rw [hk, show g = 0 by omega, pow_zero]
    exact absurd hk1 (ne_of_gt Finite.one_lt_card)
  have hf : 2 ≤ f := two_le_of_lieModel_PSL_two_two hDm
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have hcardX : Nat.card X = Nat.card k ^ (r ^ 2) *
      ∏ j ∈ Finset.Icc 1 r, (Nat.card k ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv]
    exact LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r
  have hdvdX : Open.ordA 1 (2 ^ f) ∣ Nat.card X := by
    rw [← card_of_lieModel_PSL_two_two hDm]
    exact (card_quotient_dvd_card (center D)).trans (Subgroup.card_subgroup_dvd_card D)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · rw [hcardX, hk, pow_one] at hdvdX
      have h6 : Open.ordA 1 (2 ^ f) ∣ 6 := hdvdX.trans (dvd_of_eq (by decide))
      have h1 := Nat.le_of_dvd (by norm_num) h6
      have h2 := sixty_le_ordA_one hf
      omega
    · obtain ⟨hDs, hD360⟩ :=
        card_eq_of_isComponent_statedSp_two_two (by rw [hk, pow_one]) Φ hD
      have hZ : center D = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hD.1 hDs
      have hcard : Nat.card (D ⧸ center D) = Nat.card D := by
        rw [hZ]
        exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
      rw [card_of_lieModel_PSL_two_two hDm, hD360] at hcard
      exact ordA_one_ne_360 (by omega) hcard
  obtain ⟨t, r', hX, hadm, hmX, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ),
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g ∧
        (t = .PSL → r = 1) := by
    rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
    · have hg2 : 2 ≤ g := by omega
      obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := k)
      have h4 : 4 ≤ 2 ^ g :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hadm : StatedLieAdmissible .PSL 2 2 g := ⟨Nat.prime_two, hg, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel X .PSL 2 2 g :=
        ⟨hadm, k, inferInstance, inferInstance, hk,
          ⟨(Φ.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm).trans
            e₂⟩⟩
      exact ⟨.PSL, 2, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩, fun _ => rfl⟩
    · have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
        · exact Or.inr (Or.inr ⟨by rw [hk, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r k) hk (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        fun h => absurd h (by decide)⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  have hDs : IsSimpleGroup D := eD.isSimpleGroup
  obtain ⟨htt, -, hgf⟩ := sl2TypeDet_of_simple hdet hD.1 hDs hDm hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hmX)
  exact ⟨ht htt, hgf⟩

end CFSG.SeitzReduction.RankOne
