module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWZero
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallAltK
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def SixSmallKindRankInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.IsQuasisimple S → center S = ⊥ →
    NativeSporadic.SporadicRep S → ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), IsComponent D → LieModel (D ⧸ center D) .PSL 4 2 1 →
      (F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) →
      ∀ E : Subgroup S, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 2 ^ 5

theorem false_of_lSix_smallKind_of_wZero {G : Type} [Group G] [Finite G]
    (hrk : SixSmallKindRankInput) {H D W₀ : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htX : t ∈ H) (hDX : D ≤ H) (hDq : CFSG.IsQuasisimple D)
    (hDm : LieModel (D ⧸ center D) .PSL 4 2 1)
    (hcomp : CFSG.Open.IsComponentOf ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))
      (centralizer ({QuotientGroup.mk' (oddCore H) ⟨t, htX⟩} : Set (H ⧸ oddCore H))))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :
        Subgroup (H ⧸ oddCore H)) : Set (H ⧸ oddCore H)) → Nat.card U ≤ 2)
    (hW₀c : Nat.card W₀ = 2 ^ 6) (hW₀2 : ∀ w ∈ W₀, w * w = 1) (hW₀X : W₀ ≤ H)
    (hV₀D : W₀ ⊓ centralizer ({t} : Set G) ≤ D)
    (hV₀c : Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 3)
    (hWN : ∀ N : Subgroup (H ⧸ oddCore H), N.Normal →
      (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≤ N →
      (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≤ N)
    {Kc : Subgroup (H ⧸ oddCore H)} (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) < Kc)
    (hKt' : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩)).toMonoidHom = Kc)
    (hsC : QuotientGroup.mk' (oddCore H) ⟨t, htX⟩ ∉ centralizer (Kc : Set (H ⧸ oddCore H)))
    (hZ : center Kc = ⊥) (hsp : NativeSporadic.SporadicRep (Kc ⧸ center Kc)) : False := by
  have hDK' := hDK.le
  have hcardW : ∀ P : Subgroup G, P ≤ W₀ →
      Nat.card ((P.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) = Nat.card P := by
    intro P hPW
    rw [card_map_mk_oddCore_of_mul_self
        (fun x hx => Subtype.ext (hW₀2 _ (hPW (mem_subgroupOf.1 hx)))),
      Nat.card_congr (subgroupOfEquivOfLe (hPW.trans hW₀X)).toEquiv]
  have hV₀card : Nat.card (((W₀ ⊓ centralizer ({t} : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (oddCore H))) = 2 ^ 3 := by
    rw [hcardW _ inf_le_left, hV₀c]
  have hV₀K : ((W₀ ⊓ centralizer ({t} : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (oddCore H)) ≤ Kc :=
    (map_mono fun x hx => mem_subgroupOf.2 (hV₀D (mem_subgroupOf.1 hx))).trans hDK'
  have hKn : Kc.Normal := normal_of_isComponent_of_card_le_two hKc hDK' hsyl
    (IsPGroup.of_card hV₀card) hV₀K (by rw [hV₀card]; norm_num)
  have hWbK : (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) ≤ Kc := hWN Kc hKn hDK'
  have hWbcard : Nat.card ((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))) = 2 ^ 6 := by
    rw [hcardW _ le_rfl, hW₀c]
  have hWb2 : ∀ z ∈ (W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H)), z * z = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, show w * w = 1 from Subtype.ext (hW₀2 _ (mem_subgroupOf.1 hw)), map_one]
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
      center ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)))) .PSL 4 2 1 :=
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
  have hspK : NativeSporadic.SporadicRep Kc := by
    obtain ⟨nm, ⟨φ⟩⟩ := hsp
    exact ⟨nm, ⟨(quotientCenterMulEquiv hZ).symm.trans φ⟩⟩
  have hW'card : Nat.card (((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc) =
      2 ^ 6 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWbK).toEquiv, hWbcard]
  have hW'2 : ∀ k ∈ ((W₀.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).subgroupOf Kc,
      k * k = 1 := fun k hk => Subtype.ext (hWb2 _ (mem_subgroupOf.1 hk))
  have h32 := hrk (↥Kc) hKc.1 hZ hspK _ hτ2 _ hD'c hD'm h2cond _ hW'2
  rw [hW'card] at h32
  norm_num at h32

theorem linearTwoSmallKindAtInput_six_of (hW : LinearTwoWOneAtInput 6)
    (hrk : SixSmallKindRankInput) : LinearTwoSmallKindAtInput 6 := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt a b hab X₀ hX₀ hX₀c htX hsmall
  subst hn
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  obtain ⟨-, hDX, hDq, hDm, hcomp, hsyl, -, -⟩ :=
    neighbour_hyps_linear_two (X := modelToG e X₀)
      (D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ))) hset hK e (by norm_num)
      htC ht hab hX₀ hX₀c rfl htX rfl
  obtain ⟨W₀, hW₀c, hW₀2, hW₀X, -, hV₀D, hV₀c, -, hWN⟩ :=
    map_wZero_le_of_normal_lSix hW hset hK e ht hKt hab hX₀ hX₀c
  obtain ⟨Kc, hKc, hDK, hKt', hsC, hZ, hsp⟩ := sporadic_of_neighbourOvergroupSLmSmall_six
    (X := modelToG e X₀) (D := modelToG e (blockSL (K := K) ({a, b} : Finset (Fin 6))ᶜ)) hset hK
    e htC ht hab hX₀ hX₀c rfl htX rfl hsmall
  exact false_of_lSix_smallKind_of_wZero hrk ht htX hDX hDq hDm hcomp hsyl hW₀c hW₀2 hW₀X
    hV₀D hV₀c hWN hKc hDK hKt' hsC hZ hsp

end CFSG.SeitzReduction.LinearPilot
