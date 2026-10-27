module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerFusion
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotClassOrders
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2Center
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLongRootPlane
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteBAut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.E6Pilot (IsAutConjIn)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Field K] {n : ℕ}

section Data

variable (K n) in
@[expose] def spCoreRadical : SpTwoCentral → Subgroup (StatedSp (n + 3) K)
  | .b1 => transvRadical K (1 : Fin (n + 3))
  | .a2 => wRadical K (1 : Fin (n + 3)) 2
  | .c2 => wRadical K (1 : Fin (n + 3)) 2

variable (K n) in
@[expose] noncomputable def spCoreLevi : SpTwoCentral → Subgroup (StatedSp (n + 3) K)
  | .b1 => complSp K (1 : Fin (n + 3))
  | .a2 => a2Levi K n
  | .c2 => spCompl12 K n

variable (K n) in
@[expose] noncomputable def spCoreFactor : SpTwoCentral → Subgroup (StatedSp (n + 3) K)
  | .b1 => complSp K (1 : Fin (n + 3))
  | .a2 => spCompl12 K n
  | .c2 => spCompl12 K n

theorem one_ne_zero_fin3 : (1 : Fin (n + 3)) ≠ 0 := by simp

theorem isPGroup_spCoreRadical [CharP K 2] (κ : SpTwoCentral) :
    IsPGroup 2 (spCoreRadical K n κ) := by
  cases κ
  · exact isPGroup_transvRadical
  · exact isPGroup_wRadical one_ne_two_fin
  · exact isPGroup_wRadical one_ne_two_fin

theorem a2Levi_le_range_leviHom [CharP K 2] :
    a2Levi K n ≤ (leviHom (one_ne_two_fin (n := n)) 0 (one_ne_zero (α := K))).range :=
  sup_le (range_shortBlock_le_range_leviHom one_ne_zero) (spCompl12_le_range_leviHom one_ne_zero)

theorem spCompl12_le_range_leviHom_c2 :
    spCompl12 K n ≤ (leviHom (one_ne_two_fin (n := n)) 1 (one_ne_zero (α := K))).range :=
  spCompl12_le_range_leviHom one_ne_zero

theorem spCoreLevi_le_normalizer_spCoreRadical [CharP K 2] (κ : SpTwoCentral) :
    spCoreLevi K n κ ≤ normalizer (spCoreRadical K n κ : Set (StatedSp (n + 3) K)) := by
  cases κ
  · exact complSp_le_normalizer_transvRadical
  · exact a2Levi_le_range_leviHom.trans
      (range_leviHom_le_normalizer_wRadical one_ne_two_fin one_ne_zero)
  · exact spCompl12_le_range_leviHom_c2.trans
      (range_leviHom_le_normalizer_wRadical one_ne_two_fin one_ne_zero)

theorem disjoint_spCoreRadical_spCoreLevi [CharP K 2] (κ : SpTwoCentral) :
    Disjoint (spCoreRadical K n κ) (spCoreLevi K n κ) := by
  cases κ
  · exact disjoint_transvRadical_complSp
  · exact (disjoint_wRadical_range_leviHom one_ne_two_fin one_ne_zero).mono_right
      a2Levi_le_range_leviHom
  · exact (disjoint_wRadical_range_leviHom one_ne_two_fin one_ne_zero).mono_right
      spCompl12_le_range_leviHom_c2

theorem perfectCore_centralizer_spRep_eq_sup [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (κ : SpTwoCentral) :
    perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))) =
      spCoreRadical K n κ ⊔ spCoreLevi K n κ := by
  cases κ
  · have hperf := commutator_centralizer_siegDiag (K := K) (m := n + 2) hK (p := 1) (by omega)
    rw [spRep_b1_eq_siegDiag, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf,
      centralizer_siegDiag_eq_sup]
    rfl
  · rw [spRep_a2_eq]
    exact (perfectCore_centralizer_a2 hK).1
  · rw [spRep_c2_eq]
    exact perfectCore_centralizer_c2 hK

theorem forall_normal_isPGroup_spCoreLevi [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (κ : SpTwoCentral) :
    ∀ N : Subgroup (spCoreLevi K n κ), N.Normal → IsPGroup 2 N → N = ⊥ := by
  cases κ
  · intro N hN hN2
    exact @eq_bot_of_normal_of_isPGroup_complSp K _ (n + 2) _ _ hK (by omega) 1 N hN hN2
  · change ∀ N : Subgroup (a2Levi K n), N.Normal → IsPGroup 2 N → N = ⊥
    exact fun N hN hN2 => eq_bot_of_normal_of_isPGroup_a2Levi hK N hN2
  · change ∀ N : Subgroup (spCompl12 K n), N.Normal → IsPGroup 2 N → N = ⊥
    exact fun N hN hN2 =>
      eq_bot_of_normal_of_isPGroup_of_mulEquiv hK (by omega) (spCompl12Equiv K n).symm N hN2

theorem longRootSp2_le_spCoreFactor (κ : SpTwoCentral) :
    longRootSp2 K (n + 3) 0 ≤ spCoreFactor K n κ := by
  cases κ
  · exact longRootSp2_le_complSp one_ne_zero_fin3
  · exact longRootSp2_le_spCompl12 n
  · exact longRootSp2_le_spCompl12 n

theorem spCoreFactor_le_spCoreLevi (κ : SpTwoCentral) : spCoreFactor K n κ ≤ spCoreLevi K n κ := by
  cases κ
  · exact le_rfl
  · exact le_sup_right
  · exact le_rfl

theorem longRootSp2_le_spCoreLevi (κ : SpTwoCentral) :
    longRootSp2 K (n + 3) 0 ≤ spCoreLevi K n κ :=
  (longRootSp2_le_spCoreFactor κ).trans (spCoreFactor_le_spCoreLevi κ)

theorem inf_centralizer_bot {G : Type*} [Group G] (M : Subgroup G) :
    M ⊓ centralizer (((⊥ : Subgroup G)) : Set G) = M := by
  rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]

theorem spCoreFactor_eq_perfectCore [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (κ : SpTwoCentral) :
    spCoreFactor K n κ = perfectCore (spCoreLevi K n κ ⊓
      centralizer (spIntrinsic κ (spCoreRadical K n κ) : Set (StatedSp (n + 3) K))) := by
  cases κ
  · change complSp K (1 : Fin (n + 3)) = perfectCore (complSp K (1 : Fin (n + 3)) ⊓
      centralizer (((⊥ : Subgroup (StatedSp (n + 3) K))) : Set (StatedSp (n + 3) K)))
    rw [inf_centralizer_bot, CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_complSp (m := n + 2) hK 1)]
  · exact (perfectCore_a2Levi_inf_centralizer_wCenter hK).symm
  · change spCompl12 K n = perfectCore (spCompl12 K n ⊓
      centralizer (((⊥ : Subgroup (StatedSp (n + 3) K))) : Set (StatedSp (n + 3) K)))
    rw [inf_centralizer_bot, CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_spCompl12 n hK)]

theorem spIntrinsic_le {G : Type*} [Group G] (κ : SpTwoCentral) (Q : Subgroup G) :
    spIntrinsic κ Q ≤ Q := by
  cases κ
  · exact bot_le
  · exact map_subtype_le _
  · exact bot_le

theorem le_centralizer_spIntrinsic {G : Type*} [Group G] (κ : SpTwoCentral) (Q : Subgroup G) :
    Q ≤ centralizer (spIntrinsic κ Q : Set G) := by
  cases κ
  · intro x _
    rw [mem_centralizer_iff]
    intro y hy
    rw [show y = 1 from hy, one_mul, mul_one]
  · intro x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val ((mem_center_iff.1 hy ⟨x, hx⟩).symm)
  · intro x _
    rw [mem_centralizer_iff]
    intro y hy
    rw [show y = 1 from hy, one_mul, mul_one]

end Data

section Intrinsic

variable {C : Type*} [Group C] {Q M : Subgroup C}

theorem coe_symm_mem_iff_of_map_eq {β : (Q ⊔ M : Subgroup C) ≃* (Q ⊔ M : Subgroup C)}
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M))
    (x : (Q ⊔ M : Subgroup C)) : (β.symm x : C) ∈ Q ↔ (x : C) ∈ Q := by
  have h := EPilot.coe_mem_iff_of_map_eq hβ (β.symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem coe_symm_mem_spIntrinsic {β : (Q ⊔ M : Subgroup C) ≃* (Q ⊔ M : Subgroup C)}
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) (κ : SpTwoCentral)
    (x : (Q ⊔ M : Subgroup C)) (hx : (x : C) ∈ spIntrinsic κ Q) :
    (β.symm x : C) ∈ spIntrinsic κ Q := by
  have hbot : ∀ y : (Q ⊔ M : Subgroup C), (y : C) ∈ (⊥ : Subgroup C) →
      (β.symm y : C) ∈ (⊥ : Subgroup C) := by
    intro y hy
    have hy1 : y = 1 := Subtype.ext (mem_bot.1 hy)
    rw [hy1, map_one]
    exact one_mem _
  cases κ
  · exact hbot x hx
  · obtain ⟨y, hy, hyx⟩ := hx
    have hxQ : (x : C) ∈ Q := hyx ▸ y.2
    refine ⟨⟨β.symm x, (coe_symm_mem_iff_of_map_eq hβ x).2 hxQ⟩, mem_center_iff.2 fun w => ?_, rfl⟩
    apply Subtype.ext
    set ww : (Q ⊔ M : Subgroup C) := ⟨w, mem_sup_left w.2⟩
    have hu : (β ww : C) ∈ Q := (EPilot.coe_mem_iff_of_map_eq hβ ww).2 w.2
    have hyu : (x : C) * (β ww : C) = (β ww : C) * (x : C) := by
      have h := mem_center_iff.1 hy ⟨β ww, hu⟩
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at h'
      rw [← hyx]
      exact h'.symm
    have hxu : x * β ww = β ww * x := Subtype.ext (by simpa using hyu)
    have hw : (w : C) = (β.symm (β ww) : C) := by rw [MulEquiv.symm_apply_apply]
    simp only [Subgroup.coe_mul]
    rw [hw, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hxu]
  · exact hbot x hx

theorem leviAutOfAut_mem_centralizer (hQM : Disjoint Q M) (hMN : M ≤ normalizer (Q : Set C))
    {β : (Q ⊔ M : Subgroup C) ≃* (Q ⊔ M : Subgroup C)}
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) {Z : Subgroup C}
    (hZQ : Z ≤ Q) (hQZ : Q ≤ centralizer (Z : Set C))
    (hZβ : ∀ x : (Q ⊔ M : Subgroup C), (x : C) ∈ Z → (β.symm x : C) ∈ Z) (m : M)
    (hm : (m : C) ∈ centralizer (Z : Set C)) :
    (EPilot.leviAutOfAut Q M hQM hMN β hβ m : C) ∈ centralizer (Z : Set C) := by
  have h1 := EPilot.inv_mul_leviAutOfAut_mem hQM hMN hβ m
  have hβm : (β (inclusion le_sup_right m) : C) ∈ centralizer (Z : Set C) := by
    rw [mem_centralizer_iff]
    intro z hz
    set zz : (Q ⊔ M : Subgroup C) := ⟨z, mem_sup_left (hZQ hz)⟩
    have hw := hZβ zz hz
    have hmw : (m : C) * (β.symm zz : C) = (β.symm zz : C) * (m : C) :=
      (mem_centralizer_iff.1 hm _ hw).symm
    have hmw' : inclusion le_sup_right m * β.symm zz = β.symm zz * inclusion le_sup_right m :=
      Subtype.ext (by simpa using hmw)
    have hz' : z = (β (β.symm zz) : C) := by rw [MulEquiv.apply_symm_apply]
    rw [hz', ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hmw']
  have e : (EPilot.leviAutOfAut Q M hQM hMN β hβ m : C) = (β (inclusion le_sup_right m) : C) *
      ((β (inclusion le_sup_right m) : C)⁻¹ * (EPilot.leviAutOfAut Q M hQM hMN β hβ m : C)) := by
    group
  rw [e]
  exact mul_mem hβm (hQZ h1)

variable [Finite C]

theorem map_leviAutOfAut_perfectCore (hQM : Disjoint Q M) (hMN : M ≤ normalizer (Q : Set C))
    {β : (Q ⊔ M : Subgroup C) ≃* (Q ⊔ M : Subgroup C)}
    (hβ : (Q.subgroupOf (Q ⊔ M)).map β.toMonoidHom = Q.subgroupOf (Q ⊔ M)) {Z : Subgroup C}
    (hZQ : Z ≤ Q) (hQZ : Q ≤ centralizer (Z : Set C))
    (hZβ : ∀ x : (Q ⊔ M : Subgroup C), (x : C) ∈ Z → (β.symm x : C) ∈ Z) :
    ((perfectCore (M ⊓ centralizer (Z : Set C))).subgroupOf M).map
        (EPilot.leviAutOfAut Q M hQM hMN β hβ).toMonoidHom =
      (perfectCore (M ⊓ centralizer (Z : Set C))).subgroupOf M := by
  set ι := EPilot.leviAutOfAut Q M hQM hMN β hβ with hι
  set T := (M ⊓ centralizer (Z : Set C)).subgroupOf M with hT
  have hle : T.map ι.toMonoidHom ≤ T := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hx
    have hm' : (m : C) ∈ M ⊓ centralizer (Z : Set C) := mem_subgroupOf.1 hm
    refine mem_subgroupOf.2 ⟨(ι m).2, ?_⟩
    exact leviAutOfAut_mem_centralizer hQM hMN hβ hZQ hQZ hZβ m hm'.2
  have hTeq : T.map ι.toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective ι.injective])
  rw [← LinearPilot.perfectCore_subgroupOf inf_le_left, ← hT, CFSG.Quasithin.map_perfectCore,
    hTeq]

end Intrinsic

section Restrict

variable {C : Type*} [Group C] {M S : Subgroup C}

theorem coe_apply_mem_iff_of_map_eq {ι : M ≃* M}
    (hι : (S.subgroupOf M).map ι.toMonoidHom = S.subgroupOf M) (m : M) :
    ((ι m : M) : C) ∈ S ↔ (m : C) ∈ S := by
  have h : ι m ∈ (S.subgroupOf M).map ι.toMonoidHom ↔ m ∈ S.subgroupOf M :=
    mem_map_iff_mem (f := ι.toMonoidHom) ι.injective
  rw [hι, mem_subgroupOf, mem_subgroupOf] at h
  exact h

@[expose] noncomputable def restrictMulEquiv (hSM : S ≤ M) (ι : M ≃* M)
    (hι : (S.subgroupOf M).map ι.toMonoidHom = S.subgroupOf M) : S ≃* S where
  toFun s := ⟨ι ⟨s, hSM s.2⟩, (coe_apply_mem_iff_of_map_eq hι _).2 s.2⟩
  invFun s := ⟨ι.symm ⟨s, hSM s.2⟩,
    (coe_apply_mem_iff_of_map_eq hι _).1 (by rw [MulEquiv.apply_symm_apply]; exact s.2)⟩
  left_inv s := by
    apply Subtype.ext
    simp only
    have e : (⟨(ι ⟨s, hSM s.2⟩ : C), hSM ((coe_apply_mem_iff_of_map_eq hι _).2 s.2)⟩ : M) =
        ι ⟨s, hSM s.2⟩ := rfl
    rw [e, MulEquiv.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    simp only
    have e : (⟨(ι.symm ⟨s, hSM s.2⟩ : C), hSM ((coe_apply_mem_iff_of_map_eq hι _).1
        (by rw [MulEquiv.apply_symm_apply]; exact s.2))⟩ : M) = ι.symm ⟨s, hSM s.2⟩ := rfl
    rw [e, MulEquiv.apply_symm_apply]
  map_mul' s s' := by
    apply Subtype.ext
    change ((ι ⟨((s * s' : S) : C), hSM (s * s').2⟩ : M) : C) =
      ((ι ⟨s, hSM s.2⟩ : M) : C) * ((ι ⟨s', hSM s'.2⟩ : M) : C)
    rw [show (⟨((s * s' : S) : C), hSM (s * s').2⟩ : M) = ⟨s, hSM s.2⟩ * ⟨s', hSM s'.2⟩ from rfl,
      map_mul, Subgroup.coe_mul]

theorem coe_restrictMulEquiv_apply (hSM : S ≤ M) (ι : M ≃* M)
    (hι : (S.subgroupOf M).map ι.toMonoidHom = S.subgroupOf M) (s : S) :
    ((restrictMulEquiv hSM ι hι s : S) : C) = ((ι ⟨s, hSM s.2⟩ : M) : C) := rfl

theorem exists_conj_of_isAutConjIn_of_map_eq {J : Subgroup C} (h : IsAutConjIn S J) (hJS : J ≤ S)
    (hSM : S ≤ M) (ι : M ≃* M) (hι : (S.subgroupOf M).map ι.toMonoidHom = S.subgroupOf M) :
    ∃ s ∈ S, ((J.subgroupOf M).map ι.toMonoidHom).map M.subtype =
      J.map (MulAut.conj s).toMonoidHom := by
  obtain ⟨s, hs, hJ⟩ := h (restrictMulEquiv hSM ι hι)
  refine ⟨s, hs, ?_⟩
  rw [← hJ]
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    have hmJ : (m : C) ∈ J := mem_subgroupOf.1 hm
    refine ⟨_, ⟨⟨m, hJS hmJ⟩, mem_subgroupOf.2 hmJ, rfl⟩, ?_⟩
    rfl
  · rintro ⟨_, ⟨s', hs', rfl⟩, rfl⟩
    have hs'J : (s' : C) ∈ J := mem_subgroupOf.1 hs'
    exact ⟨_, ⟨⟨s', hSM s'.2⟩, mem_subgroupOf.2 hs'J, rfl⟩, rfl⟩

end Restrict

section F5

theorem map_leviAutOfAut_spCoreFactor [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (κ : SpTwoCentral)
    (β : (spCoreRadical K n κ ⊔ spCoreLevi K n κ : Subgroup (StatedSp (n + 3) K)) ≃*
      (spCoreRadical K n κ ⊔ spCoreLevi K n κ : Subgroup (StatedSp (n + 3) K)))
    (hβ : ((spCoreRadical K n κ).subgroupOf (spCoreRadical K n κ ⊔ spCoreLevi K n κ)).map
      β.toMonoidHom = (spCoreRadical K n κ).subgroupOf (spCoreRadical K n κ ⊔ spCoreLevi K n κ)) :
    ((spCoreFactor K n κ).subgroupOf (spCoreLevi K n κ)).map
        (EPilot.leviAutOfAut (spCoreRadical K n κ) (spCoreLevi K n κ)
          (disjoint_spCoreRadical_spCoreLevi κ) (spCoreLevi_le_normalizer_spCoreRadical κ) β
            hβ).toMonoidHom =
      (spCoreFactor K n κ).subgroupOf (spCoreLevi K n κ) := by
  rw [spCoreFactor_eq_perfectCore hK κ]
  exact map_leviAutOfAut_perfectCore _ _ hβ (spIntrinsic_le κ _) (le_centralizer_spIntrinsic κ _)
    (coe_symm_mem_spIntrinsic hβ κ)

variable (K n) in
@[expose] def SpLongRootF5 [CharP K 2] (κ : SpTwoCentral) : Prop :=
  ∀ (β : (spCoreRadical K n κ ⊔ spCoreLevi K n κ : Subgroup (StatedSp (n + 3) K)) ≃*
      (spCoreRadical K n κ ⊔ spCoreLevi K n κ : Subgroup (StatedSp (n + 3) K)))
    (hβ : ((spCoreRadical K n κ).subgroupOf (spCoreRadical K n κ ⊔ spCoreLevi K n κ)).map
      β.toMonoidHom = (spCoreRadical K n κ).subgroupOf (spCoreRadical K n κ ⊔ spCoreLevi K n κ)),
    ∃ c : StatedSp (n + 3) K,
      (((longRootSp2 K (n + 3) 0).subgroupOf (spCoreLevi K n κ)).map
        (EPilot.leviAutOfAut (spCoreRadical K n κ) (spCoreLevi K n κ)
          (disjoint_spCoreRadical_spCoreLevi κ) (spCoreLevi_le_normalizer_spCoreRadical κ) β
            hβ).toMonoidHom).map (spCoreLevi K n κ).subtype =
        (longRootSp2 K (n + 3) 0).map (MulAut.conj c).toMonoidHom

theorem spLongRootF5_of_isAutConjIn [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {κ : SpTwoCentral} (h : IsAutConjIn (spCoreFactor K n κ) (longRootSp2 K (n + 3) 0)) :
    SpLongRootF5 K n κ := by
  intro β hβ
  obtain ⟨s, -, hs⟩ := exists_conj_of_isAutConjIn_of_map_eq h (longRootSp2_le_spCoreFactor κ)
    (spCoreFactor_le_spCoreLevi κ) _ (map_leviAutOfAut_spCoreFactor hK κ β hβ)
  exact ⟨s, hs⟩

theorem spLongRootF5_b1 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 1 ≤ n) :
    SpLongRootF5 K n .b1 :=
  spLongRootF5_of_isAutConjIn hK (isAutConjIn_complSp_longRootSp2 hn)

theorem spLongRootF5_a2 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) :
    SpLongRootF5 K n .a2 :=
  spLongRootF5_of_isAutConjIn hK (isAutConjIn_spCompl12_longRootSp2 n hn)

theorem spLongRootF5_c2 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) :
    SpLongRootF5 K n .c2 :=
  spLongRootF5_of_isAutConjIn hK (isAutConjIn_spCompl12_longRootSp2 n hn)

theorem spLongRootF5_of_two_le [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n)
    (κ : SpTwoCentral) : SpLongRootF5 K n κ := by
  cases κ
  · exact spLongRootF5_b1 hK (by omega)
  · exact spLongRootF5_a2 hK hn
  · exact spLongRootF5_c2 hK hn

theorem spLongRootF5_a2_zero [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    SpLongRootF5 K 0 .a2 :=
  spLongRootF5_of_isAutConjIn hK isAutConjIn_spCompl12_zero

theorem spLongRootF5_c2_zero [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    SpLongRootF5 K 0 .c2 :=
  spLongRootF5_of_isAutConjIn hK isAutConjIn_spCompl12_zero

theorem spLongRootF5_zero [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hb1 : SpLongRootF5 K 0 .b1) (κ : SpTwoCentral) : SpLongRootF5 K 0 κ := by
  cases κ
  · exact hb1
  · exact spLongRootF5_a2_zero hK
  · exact spLongRootF5_c2_zero hK

theorem spLongRootF5_one [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (ha2 : SpLongRootF5 K 1 .a2) (hc2 : SpLongRootF5 K 1 .c2) (κ : SpTwoCentral) :
    SpLongRootF5 K 1 κ := by
  cases κ
  · exact spLongRootF5_b1 hK le_rfl
  · exact ha2
  · exact hc2

theorem centralizer_longRootSp2 [CharP K 2] (hK : 4 ≤ Nat.card K) {m : ℕ} (k : Fin m) :
    centralizer (longRootSp2 K m k : Set (StatedSp m K)) = complSp K k := by
  refine le_antisymm (fun x hx => ?_) (complSp_le_centralizer_longRootSp2 k)
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  have hxX : x ∈ centralizer (rootTorusSp K k : Set (StatedSp m K)) :=
    centralizer_le (rootTorusSp_le_longRootSp2 k) hx
  obtain ⟨u, y, hy, rfl⟩ :=
    exists_eq_mul_of_mem_centralizer hκ (rootTorusHom_mem_rootTorusSp k κ) hxX
  have hyJ : y ∈ centralizer (longRootSp2 K m k : Set (StatedSp m K)) :=
    complSp_le_centralizer_longRootSp2 k hy
  have hu : rootTorusHom K m k u ∈ centralizer (longRootSp2 K m k : Set (StatedSp m K)) := by
    have h := mul_mem hx (inv_mem hyJ)
    rwa [mul_inv_cancel_right] at h
  have hu' : rootTorusHom K m k u ∈ centralizer ({siegDiag K k 1} : Set (StatedSp m K)) :=
    centralizer_le (Set.singleton_subset_iff.2 (siegDiag_mem_longRootSp2 k 1)) hu
  have hcol := (mem_centralizer_siegDiag_iff.1 hu') (Sum.inl k)
  simp only [mat_rootTorusHom_apply, ↓reduceIte, diagSpEntry_mulSingle_inl_self,
    Matrix.one_apply_eq] at hcol
  rw [Units.val_eq_one.1 hcol, map_one, one_mul]
  exact hy

theorem nonempty_centralizer_conj_longRootSp2 [CharP K 2] (hK : 4 ≤ Nat.card K) {m : ℕ}
    (k : Fin m) (c : StatedSp m K) :
    Nonempty (centralizer (((longRootSp2 K m k).map (MulAut.conj c).toMonoidHom :
      Subgroup (StatedSp m K)) : Set (StatedSp m K)) ≃* complSp K k) := by
  have hcen : centralizer (((longRootSp2 K m k).map (MulAut.conj c).toMonoidHom :
      Subgroup (StatedSp m K)) : Set (StatedSp m K)) =
        (complSp K k).map (MulAut.conj c).toMonoidHom := by
    rw [← F4Pilot.map_centralizer_mulEquiv (MulAut.conj c), centralizer_longRootSp2 hK k]
  exact ⟨(MulEquiv.subgroupCongr hcen).trans
    ((complSp K k).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

theorem nonempty_centralizer_leviAutOfAut [CharP K 2] (hK : 4 ≤ Nat.card K)
    {κ : SpTwoCentral} (hF5 : SpLongRootF5 K n κ)
    (β : (spCoreRadical K n κ ⊔ spCoreLevi K n κ : Subgroup (StatedSp (n + 3) K)) ≃*
      (spCoreRadical K n κ ⊔ spCoreLevi K n κ : Subgroup (StatedSp (n + 3) K)))
    (hβ : ((spCoreRadical K n κ).subgroupOf (spCoreRadical K n κ ⊔ spCoreLevi K n κ)).map
      β.toMonoidHom = (spCoreRadical K n κ).subgroupOf (spCoreRadical K n κ ⊔ spCoreLevi K n κ)) :
    Nonempty (centralizer (((((longRootSp2 K (n + 3) 0).subgroupOf (spCoreLevi K n κ)).map
      (EPilot.leviAutOfAut (spCoreRadical K n κ) (spCoreLevi K n κ)
        (disjoint_spCoreRadical_spCoreLevi κ) (spCoreLevi_le_normalizer_spCoreRadical κ) β
          hβ).toMonoidHom).map (spCoreLevi K n κ).subtype :
          Subgroup (StatedSp (n + 3) K)) : Set (StatedSp (n + 3) K)) ≃*
      complSp K (0 : Fin (n + 3))) := by
  obtain ⟨c, hc⟩ := hF5 β hβ
  rw [hc]
  exact nonempty_centralizer_conj_longRootSp2 hK 0 c

theorem eq_of_nonempty_mulEquiv_spCoreRadical_sup [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {κ₁ κ₂ : SpTwoCentral}
    (h : Nonempty ((spCoreRadical K n κ₁ ⊔ spCoreLevi K n κ₁ : Subgroup (StatedSp (n + 3) K)) ≃*
      (spCoreRadical K n κ₂ ⊔ spCoreLevi K n κ₂ : Subgroup (StatedSp (n + 3) K)))) : κ₁ = κ₂ := by
  obtain ⟨φ⟩ := h
  apply card_perfectCore_centralizer_spRep_injective n hK
  rw [perfectCore_centralizer_spRep_eq_sup hK, perfectCore_centralizer_spRep_eq_sup hK]
  exact Nat.card_congr φ.toEquiv

end F5

section Fusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_coords_conjugate_of_mem {C : Type*} [Group C] (e : L ≃* C) (g : G) {a : G}
    (ha : a ∈ CFSG.conjugate L g) :
    ∃ φ' : C →* G, Function.Injective φ' ∧ φ'.range = CFSG.conjugate L g ∧
      ∀ y, φ' y = a * (g⁻¹ * (e.symm y : G) * g) * a⁻¹ := by
  refine ⟨(MulAut.conj (a * g⁻¹)).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom),
    (MulAut.conj (a * g⁻¹)).injective.comp (L.subtype_injective.comp e.symm.injective), ?_,
    fun y => ?_⟩
  · rw [MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    have hmap : L.map (MulAut.conj (a * g⁻¹)).toMonoidHom =
        (CFSG.conjugate L g).map (MulAut.conj a).toMonoidHom := by
      rw [CFSG.conjugate, Subgroup.map_map]
      congr 1
      ext x
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
        MulAut.conj_apply]
      group
    rw [hmap]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      coe_subtype, MulAut.conj_apply]
    group

theorem exists_conj_eq_mul_spRep_coords (hset : SeitzSetting G L) [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp (n + 3) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (g : G) (κ κ' : SpTwoCentral), g⁻¹ * t * g = t * (e.symm (spRep n κ) : G) ∧
      ∃ φ' : StatedSp (n + 3) K →* G, Function.Injective φ' ∧
        φ'.range = CFSG.conjugate L g ∧
        ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = φ' (spRep n κ') * l * (φ' (spRep n κ'))⁻¹ := by
  obtain ⟨x, z, -, hxz, ⟨κ, c, hc⟩, ⟨κ', c', hc'⟩, hact⟩ :=
    exists_conj_eq_mul_spRep_twoSided hset hK e ht hKt
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hct : (c : G) * t = t * (c : G) := mem_centralizer_iff.1 htC _ c.2
  rw [coe_conjugateMulEquiv] at hc'
  set g : G := x * (c : G)⁻¹ with hgdef
  have hg : g⁻¹ * t * g = t * (e.symm (spRep n κ) : G) := by
    calc g⁻¹ * t * g = (c : G) * (x⁻¹ * t * x) * (c : G)⁻¹ := by rw [hgdef]; group
      _ = ((c : G) * t) * z * (c : G)⁻¹ := by rw [hxz]; group
      _ = t * ((c : G) * z * (c : G)⁻¹) := by rw [hct]; group
      _ = t * (e.symm (spRep n κ) : G) := by rw [hc]
  obtain ⟨d, hdL, hd⟩ := c'.2
  have hd' : (c' : G) = x⁻¹ * d * x := by
    rw [← hd]
    simp
  set a : G := (c : G) * (c' : G)⁻¹ * (c : G)⁻¹ with hadef
  have ha : a ∈ CFSG.conjugate L g := by
    refine ⟨d⁻¹, inv_mem hdL, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hadef, hd', hgdef]
    group
  obtain ⟨φ', hφ', hφ'r, hφ'y⟩ := exists_coords_conjugate_of_mem e g ha
  have hφ'rep : φ' (spRep n κ') = (c : G) * z * (c : G)⁻¹ := by
    rw [hφ'y]
    have e1 : g⁻¹ * (e.symm (spRep n κ') : G) * g =
        (c : G) * (x⁻¹ * (e.symm (spRep n κ') : G) * x) * (c : G)⁻¹ := by rw [hgdef]; group
    rw [e1, ← hc', hadef]
    group
  refine ⟨g, κ, κ', hg, φ', hφ', hφ'r, fun l hl => ?_⟩
  rw [hφ'rep]
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  have hl' : x⁻¹ * l₀ * x ∈ CFSG.conjugate L x :=
    ⟨l₀, hl₀, by simp⟩
  have h1 := hact _ hl'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have e2 : g⁻¹ * l₀ * g = (c : G) * (x⁻¹ * l₀ * x) * (c : G)⁻¹ := by rw [hgdef]; group
  rw [e2]
  calc t * ((c : G) * (x⁻¹ * l₀ * x) * (c : G)⁻¹) * t⁻¹ =
      (t * (c : G)) * (x⁻¹ * l₀ * x) * (t * (c : G))⁻¹ := by group
    _ = ((c : G) * t) * (x⁻¹ * l₀ * x) * ((c : G) * t)⁻¹ := by rw [hct]
    _ = (c : G) * (t * (x⁻¹ * l₀ * x) * t⁻¹) * (c : G)⁻¹ := by group
    _ = (c : G) * (z * (x⁻¹ * l₀ * x) * z⁻¹) * (c : G)⁻¹ := by rw [h1]
    _ = (c : G) * z * (c : G)⁻¹ * ((c : G) * (x⁻¹ * l₀ * x) * (c : G)⁻¹) *
          ((c : G) * z * (c : G)⁻¹)⁻¹ := by group

end Fusion

section LemmaB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

noncomputable def mapSymmEquiv {C : Type*} [Group C] (e : L ≃* C) (B : Subgroup C) :
    B ≃* ((B.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  (B.equivMapOfInjective _ e.symm.injective).trans
    ((B.map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

theorem exists_conj_eq_mul_spRep_le_centralizer_mulEquiv (hset : SeitzSetting G L) [Finite K]
    [CharP K 2] (hK : 4 ≤ Nat.card K) (hF5 : ∀ κ, SpLongRootF5 K n κ)
    (e : L ≃* StatedSp (n + 3) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((longRootSp2 K (n + 3) 0).map e.symm.toMonoidHom).map L.subtype) :
    ∃ (g : G) (κ : SpTwoCentral), g⁻¹ * t * g = t * (e.symm (spRep n κ) : G) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓
          centralizer ({t * (e.symm (spRep n κ) : G)} : Set G) ∧
        Nonempty (P ≃* ((complSp K (0 : Fin (n + 3))).map e.symm.toMonoidHom).map L.subtype) := by
  obtain ⟨g, κ, κ', hg, φ', hφ', hφ'r, hact⟩ := exists_conj_eq_mul_spRep_coords hset hK e ht hKt
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  obtain ⟨P, hP, ⟨eP⟩⟩ := EPilot.exists_le_centralizer_mulEquiv_of_coords_aut
    hset.standardSetting hOut e ht htC (spRep n) (k := κ) (k' := κ') (Or.inr hg) hφ' hφ'r hact
    (spCoreRadical K n) (spCoreLevi K n) (fun k => perfectCore_centralizer_spRep_eq_sup hK k)
    (fun k => isPGroup_spCoreRadical k) (fun k => spCoreLevi_le_normalizer_spCoreRadical k)
    (fun k => disjoint_spCoreRadical_spCoreLevi k) (fun k => forall_normal_isPGroup_spCoreLevi hK k)
    (J := longRootSp2 K (n + 3) 0) (fun k => longRootSp2_le_spCoreLevi k)
    (fun _ _ h => eq_of_nonempty_mulEquiv_spCoreRadical_sup hK h) (D := complSp K (0 : Fin (n + 3)))
    (fun k β hβ => nonempty_centralizer_leviAutOfAut hK (hF5 k) β hβ) hXodd hXJ
  refine ⟨g, κ, hg, P, ?_, ⟨eP.trans (mapSymmEquiv e (complSp K (0 : Fin (n + 3))))⟩⟩
  rw [← hg]
  exact hP

theorem exists_conj_eq_mul_spRep_le_centralizer_mulEquiv_of_two_le (hset : SeitzSetting G L)
    [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 3) K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((longRootSp2 K (n + 3) 0).map e.symm.toMonoidHom).map L.subtype) :
    ∃ (g : G) (κ : SpTwoCentral), g⁻¹ * t * g = t * (e.symm (spRep n κ) : G) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓
          centralizer ({t * (e.symm (spRep n κ) : G)} : Set G) ∧
        Nonempty (P ≃* ((complSp K (0 : Fin (n + 3))).map e.symm.toMonoidHom).map L.subtype) :=
  exists_conj_eq_mul_spRep_le_centralizer_mulEquiv hset hK (spLongRootF5_of_two_le hK hn) e ht
    hKt hXodd hXJ

end LemmaB

end CFSG.SeitzReduction.SymplecticPilot
