module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWZero
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2FiveSixKinds
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section General

variable {Y : Type*} [Group Y]

theorem normal_of_isComponent_of_card_le_two [Finite Y] {Kc D P : Subgroup Y}
    (hKc : IsComponent Kc) (hDK : D ≤ Kc)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hP : IsPGroup 2 P) (hPK : P ≤ Kc) (hP2 : 2 < Nat.card P) : Kc.Normal := by
  constructor
  intro k hk g
  have hK' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hKc
  rcases CFSG.LocalCores.distinct_components_commute hK' hKc with h | h
  · rw [← h]
    exact ⟨k, hk, rfl⟩
  · exfalso
    have hle : Kc.map (MulAut.conj g).toMonoidHom ≤ centralizer (D : Set Y) :=
      (commutator_eq_bot_iff_le_centralizer.1 h).trans (centralizer_le hDK)
    have hcard : Nat.card (P.map (MulAut.conj g).toMonoidHom) = Nat.card P :=
      card_map_of_injective (MulAut.conj g).injective
    have h2 := hsyl _ (hP.map _) ((map_mono hPK).trans hle)
    omega

theorem eq_one_of_mem_oddCore_of_mul_self [Finite Y] {h : Y} (hO : h ∈ oddCore Y)
    (h2 : h * h = 1) : h = 1 := by
  have hodd : Odd (Nat.card (oddCore Y)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hd1 : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h2])
  have hd2 : orderOf h ∣ Nat.card (oddCore Y) := (oddCore Y).orderOf_dvd_natCard hO
  have hcop : Nat.Coprime 2 (Nat.card (oddCore Y)) := Nat.coprime_two_left.2 hodd
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

theorem card_map_mk_oddCore_of_mul_self [Finite Y] {P : Subgroup Y}
    (hP : ∀ x ∈ P, x * x = 1) :
    Nat.card (P.map (QuotientGroup.mk' (oddCore Y))) = Nat.card P := by
  have hinj : Function.Injective ((QuotientGroup.mk' (oddCore Y)).comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 := eq_one_of_mem_oddCore_of_mul_self hx (hP x x.2)
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have hrange : P.map (QuotientGroup.mk' (oddCore Y)) =
      ((QuotientGroup.mk' (oddCore Y)).comp P.subtype).range := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end General

@[expose] def LFiveSmallIdentInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.IsQuasisimple S → center S = ⊥ →
    ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), IsComponent D → LieModel (D ⧸ center D) .PSL 3 2 1 →
      (F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) →
      SLmSmall (S ⧸ center S) 3 1 →
      LieModel S .PSL 2 7 2 ∨ LieModel S .PSL 3 7 1 ∨ LieModel S .PSU 3 7 1 ∨
        Nonempty (S ≃* NativeSporadic.J2)

@[expose] def LFiveSmallKindRankInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.IsQuasisimple S → center S = ⊥ →
    ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), IsComponent D → LieModel (D ⧸ center D) .PSL 3 2 1 →
      (F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) →
      SLmSmall (S ⧸ center S) 3 1 →
      (∀ E : Subgroup S, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 8) ∨
        Nonempty (S ≃* NativeSporadic.J2)

@[expose] def LFiveJTwoInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.J2) →
    ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), IsComponent D → LieModel (D ⧸ center D) .PSL 3 2 1 →
    ∀ W : Subgroup S, Nat.card W = 16 → (∀ x ∈ W, x * x = 1) → W.map τ.toMonoidHom = W →
      W ⊓ fixedSubgroup τ ≤ D.map (fixedSubgroup τ).subtype → False

theorem false_of_lFive_smallKind_of_wZero {G : Type} [Group G] [Finite G]
    (hrk : LFiveSmallKindRankInput) (hJ : LFiveJTwoInput) {H D W₀ : Subgroup G} {t y : G}
    (ht : orderOf t = 2) (htX : t ∈ H) (hDX : D ≤ H) (hDq : CFSG.IsQuasisimple D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (hcomp : CFSG.Open.IsComponentOf ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))
      (centralizer ({QuotientGroup.mk' (oddCore H) ⟨t, htX⟩} : Set (H ⧸ oddCore H))))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :
        Subgroup (H ⧸ oddCore H)) : Set (H ⧸ oddCore H)) → Nat.card U ≤ 2)
    (hW₀c : Nat.card W₀ = 2 ^ 4) (hW₀2 : ∀ w ∈ W₀, w * w = 1) (hW₀X : W₀ ≤ H)
    (htW₀ : t ∈ normalizer (W₀ : Set G)) (hV₀D : W₀ ⊓ centralizer ({t} : Set G) ≤ D)
    (hV₀c : Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 2) (hyD : y ∈ D)
    (hyW₀ : y ∈ normalizer (W₀ : Set G)) (hW₀y : W₀ ⊓ centralizer ({y} : Set G) = ⊥)
    {Kc : Subgroup (H ⧸ oddCore H)} (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) < Kc)
    (hKt' : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩)).toMonoidHom = Kc)
    (hsC : QuotientGroup.mk' (oddCore H) ⟨t, htX⟩ ∉ centralizer (Kc : Set (H ⧸ oddCore H)))
    (hZ : center Kc = ⊥) (hsm : SLmSmall (Kc ⧸ center Kc) 3 1) : False := by
  have hWc : ∀ v ∈ W₀, ∀ w ∈ W₀, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₀2 hv hw
  have hyH : y ∈ H := hDX hyD
  have hDK' := hDK.le
  have hyK : QuotientGroup.mk' (oddCore H) ⟨y, hyH⟩ ∈ Kc :=
    hDK' ⟨⟨y, hyH⟩, mem_subgroupOf.2 hyD, rfl⟩
  have hcardW : ∀ P : Subgroup G, P ≤ W₀ →
      Nat.card ((P.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) = Nat.card P := by
    intro P hPW
    rw [card_map_mk_oddCore_of_mul_self (fun x hx => Subtype.ext (hW₀2 _ (hPW (mem_subgroupOf.1 hx)))),
      Nat.card_congr (subgroupOfEquivOfLe (hPW.trans hW₀X)).toEquiv]
  have hV₀card : Nat.card (((W₀ ⊓ centralizer ({t} : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (oddCore H))) = 2 ^ 2 := by
    rw [hcardW _ inf_le_left, hV₀c]
  have hV₀K : ((W₀ ⊓ centralizer ({t} : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (oddCore H)) ≤ Kc :=
    (map_mono fun x hx => mem_subgroupOf.2 (hV₀D (mem_subgroupOf.1 hx))).trans hDK'
  have hKn : Kc.Normal := normal_of_isComponent_of_card_le_two hKc hDK' hsyl
    (IsPGroup.of_card hV₀card) hV₀K (by rw [hV₀card]; norm_num)
  have hWbK : (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≤ Kc := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hw'eq⟩ :=
      exists_commutator_eq_of_inf_centralizer_eq_bot hWc hyW₀ hW₀y (mem_subgroupOf.1 hw)
    have hw'H : w' ∈ H := hW₀X hw'
    have hweq : w = ⟨w', hw'H⟩ * ⟨y, hyH⟩ * ⟨w', hw'H⟩⁻¹ * ⟨y, hyH⟩⁻¹ :=
      Subtype.ext hw'eq.symm
    rw [hweq, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact Kc.mul_mem (hKn.conj_mem _ hyK _) (Kc.inv_mem hyK)
  have hWbcard : Nat.card ((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) = 16 := by
    rw [hcardW _ le_rfl, hW₀c]
    norm_num
  have hWb2 : ∀ z ∈ (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)), z * z = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, show w * w = 1 from Subtype.ext (hW₀2 _ (mem_subgroupOf.1 hw)), map_one]
  have hWbs : ∀ z ∈ (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)),
      QuotientGroup.mk' (oddCore H) ⟨t, htX⟩ * z * (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩)⁻¹ ∈
        (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨t, htX⟩ * w * ⟨t, htX⟩⁻¹, mem_subgroupOf.2 ?_, by simp only [map_mul, map_inv]⟩
    exact (mem_normalizer_iff.1 htW₀ _).1 (mem_subgroupOf.1 hw)
  have hWbC : ∀ z ∈ (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)),
      z ∈ centralizer ({QuotientGroup.mk' (oddCore H) ⟨t, htX⟩} : Set (H ⧸ oddCore H)) →
      z ∈ (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) := by
    rintro _ ⟨w, hw, rfl⟩ hz
    rw [mem_centralizer_singleton_iff] at hz
    have hc : ⟨t, htX⟩ * w * ⟨t, htX⟩⁻¹ * w⁻¹ ∈ oddCore H := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (oddCore H) (⟨t, htX⟩ * w * ⟨t, htX⟩⁻¹ * w⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hz]
      group
    have hc2 : (⟨t, htX⟩ * w * ⟨t, htX⟩⁻¹ * w⁻¹) * (⟨t, htX⟩ * w * ⟨t, htX⟩⁻¹ * w⁻¹) =
        (1 : H) :=
      Subtype.ext (hW₀2 _ (tcomm_mem htW₀ (mem_subgroupOf.1 hw)))
    have hc1 := eq_one_of_mem_oddCore_of_mul_self hc hc2
    have hwt : (w : G) ∈ centralizer ({t} : Set G) :=
      tcomm_eq_one_iff.1 (congrArg Subtype.val hc1)
    exact ⟨w, mem_subgroupOf.2 (hV₀D (Subgroup.mem_inf.2 ⟨mem_subgroupOf.1 hw, hwt⟩)), rfl⟩
  have hs2 : orderOf (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩) = 2 :=
    orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hs2' : QuotientGroup.mk' (oddCore H) ⟨t, htX⟩ ^ 2 = 1 := by
    rw [← hs2, pow_orderOf_eq_one]
  have hsN : QuotientGroup.mk' (oddCore H) ⟨t, htX⟩ ∈ normalizer (Kc : Set (H ⧸ oddCore H)) :=
    mem_normalizer_iff_map_conj_eq.2 hKt'
  have hKs : ¬ Kc ≤ centralizer ({QuotientGroup.mk' (oddCore H) ⟨t, htX⟩} :
      Set (H ⧸ oddCore H)) := fun h =>
    hsC (mem_centralizer_iff.2 fun k hk => mem_centralizer_singleton_iff.1 (h hk))
  have hτ2 := F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2' hKs
  have hDs := hcomp.1
  have hDc : IsComponent (((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf
      (centralizer ({QuotientGroup.mk' (oddCore H) ⟨t, htX⟩} : Set (H ⧸ oddCore H)))) :=
    (isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK'
  have hDbm : LieModel (((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) ⧸
      center ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))) .PSL 3 2 1 :=
    lieModel_quotient_center_map_oddCore hDX hDq hDm (ne_bot_of_isQuasisimple hcomp.2.2)
  obtain ⟨hD'c, hD'm, hD'map⟩ :=
    isComponent_fixedSubgroup_of_le_of_quotient hsN hDK' hDs hDcomp hDbm
  have h2cond : F4Pilot.FixedCentralizerTwoFree (Kc.normalizerMonoidHom ⟨_, hsN⟩)
        ((((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc).subgroupOf
          (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))) ∨
      (Kc.normalizerMonoidHom ⟨_, hsN⟩ ∈ (MulAut.conj : Kc →* MulAut Kc).range ∧
        FixedCentralizerTwoSmall (Kc.normalizerMonoidHom ⟨_, hsN⟩)
          ((((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc).subgroupOf
            (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)))) := by
    by_cases hsK : QuotientGroup.mk' (oddCore H) ⟨t, htX⟩ ∈ Kc
    · exact .inr ⟨F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK,
        E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK' hsyl _ hD'map⟩
    · exact .inl (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs2 hsK hDs hDK' hsyl _
        hD'map)
  have hW'card : Nat.card (((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc) =
      16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWbK).toEquiv, hWbcard]
  have hW'2 : ∀ k ∈ ((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc,
      k * k = 1 := fun k hk => Subtype.ext (hWb2 _ (mem_subgroupOf.1 hk))
  have hW'τ : (((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc).map
      (Kc.normalizerMonoidHom ⟨_, hsN⟩).toMonoidHom =
        ((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc := by
    have hle : (((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc).map
        (Kc.normalizerMonoidHom ⟨_, hsN⟩).toMonoidHom ≤
          ((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc := by
      rintro _ ⟨k, hk, rfl⟩
      rw [mem_subgroupOf, MulEquiv.coe_toMonoidHom, F4Pilot.coe_normalizerMonoidHom_mk_apply]
      exact hWbs _ (mem_subgroupOf.1 hk)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    exact (card_map_of_injective (f := (Kc.normalizerMonoidHom ⟨_, hsN⟩).toMonoidHom)
      (Kc.normalizerMonoidHom ⟨_, hsN⟩).injective).ge
  have hW'D : ((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc ⊓
      fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩) ≤
        ((((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc).subgroupOf
          (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))).map
            (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)).subtype := by
    rw [hD'map]
    intro k hk
    obtain ⟨hkW, hkfix⟩ := Subgroup.mem_inf.1 hk
    rw [F4Pilot.fixedSubgroup_normalizerMonoidHom, mem_subgroupOf] at hkfix
    exact mem_subgroupOf.2 (hWbC _ (mem_subgroupOf.1 hkW) hkfix)
  rcases hrk (↥Kc) hKc.1 hZ _ hτ2 _ hD'c hD'm h2cond hsm with hE | hJ2
  · have h8 := hE _ hW'2
    rw [hW'card] at h8
    norm_num at h8
  · exact hJ (↥Kc) hJ2 _ hτ2 _ hD'c hD'm _ hW'card hW'2 hW'τ hW'D

theorem linearTwoSmallKindAtInput_five_of (hW : LFiveWOneInput) (hrk : LFiveSmallKindRankInput)
    (hJ : LFiveJTwoInput) : LinearTwoSmallKindAtInput 5 := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt a b hab X₀ hX₀ hX₀c htX hsmall
  subst hn
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  obtain ⟨-, hDX, hDq, hDm, hcomp, hsyl, -, -⟩ :=
    neighbour_hyps_linear_two (X := modelToG e X₀)
      (D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ))) hset hK e (by norm_num)
      htC ht hab hX₀ hX₀c rfl htX rfl
  obtain ⟨W₀, hW₀c, hW₀2, hW₀X, htW₀, hV₀D, hV₀c, y, hyD, hyW₀, hW₀y⟩ :=
    exists_wZero_lFive hW hset hK e ht hKt hab hX₀ hX₀c
  obtain ⟨Kc, hKc, hDK, hKt', hsC, hZ, hsm⟩ := hsmall
  exact false_of_lFive_smallKind_of_wZero hrk hJ ht htX hDX hDq hDm hcomp hsyl hW₀c hW₀2 hW₀X
    htW₀ hV₀D hV₀c hyD hyW₀ hW₀y hKc hDK hKt' hsC hZ hsm

end CFSG.SeitzReduction.LinearPilot
