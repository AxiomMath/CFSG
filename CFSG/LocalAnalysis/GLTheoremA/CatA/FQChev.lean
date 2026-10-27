module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Index
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem twoPart_card_entrywiseFixedGroup {τ : Tag} {M : Type} [Field M] [Finite M] {e : ℕ}
    (σ : M ≃+* M) (he : Nat.card (fixSubfield σ) = 2 ^ e) (he1 : 1 ≤ e) :
    twoPart (Nat.card (entrywiseFixedGroup τ σ)) =
      twoPart (Nat.card (adjointGroup τ (fixSubfield σ))) := by
  set Γ := entrywiseFixedGroup τ σ with hΓ
  set J := fixedFieldImage τ σ with hJ
  set Jg := J.subgroupOf Γ with hJg
  have h1 : Nat.card Jg * Jg.index = Nat.card Γ := Subgroup.card_mul_index Jg
  have h2 : Nat.card Jg = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixedFieldImage_le).toEquiv
  have h3 : Nat.card J = Nat.card (adjointGroup τ (fixSubfield σ)) :=
    (Nat.card_congr (fixedFieldImageEquiv (τ := τ) σ).toEquiv).symm
  obtain ⟨-, hdq⟩ := fixedFieldImage_index_dvd_card (τ := τ) σ
  have hodd : Odd Jg.index := by
    refine Odd.of_dvd_nat ?_ hdq
    rw [he]
    exact (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one).pow
  rw [← h1, h2, h3, mul_comm]
  exact (FP.twoPart_mul_odd hodd Nat.card_pos.ne')

@[expose] def chevExp : Tag → ℕ
  | .G2 => 6
  | .F4 => 24
  | .E6 => 36
  | .E7 => 63
  | .E8 => 120
  | _ => 0

theorem card_adjointGroup_spec {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [Finite L]
    {e : ℕ} (he : 1 ≤ e) (hL : Nat.card L = 2 ^ e) :
    ∃ r, Odd r ∧ Nat.card (adjointGroup τ L) = 2 ^ (e * chevExp τ) * r := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hL]
    exact (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' he).two
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hL]
    exact (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordF4' he).two
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hL]
    exact (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE6' he).two
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hL]
    exact (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE7' he).two
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hL]
    exact (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE8' he).two

theorem twoPart_card_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [Finite L]
    {e : ℕ} (he : 1 ≤ e) (hL : Nat.card L = 2 ^ e) :
    twoPart (Nat.card (adjointGroup τ L)) = 2 ^ (e * chevExp τ) := by
  obtain ⟨r, hr, h⟩ := card_adjointGroup_spec hτ he hL
  rw [h]
  exact twoPart_two_pow_mul_odd hr

section Bridge

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.YS09Field

noncomputable def fixCountS (τ : Tag) (K : Type) [Field K] (S : (Fin τ.rank → ℤ) → Prop)
    (σ : K ≃+* K) : ℕ :=
  Nat.card {g : MarkChev.GLS S K // g ∈ MarkChev.chevH τ.cartan S K false ∧
    MarkChev.entrywise S K σ (map_zero σ) (g : Module.End K (MarkChev.Space S K)) =
      (g : Module.End K (MarkChev.Space S K))}

theorem fixNum_chev (τ : Tag) (K : Type) [Field K] (σ : K ≃+* K) :
    fixNum (stableAct (chevAct τ.cartan K) (chevAct_one τ.cartan K) (chevAct_mul τ.cartan K)
      (LargeEvenChevH τ.cartan K false) (chevH_stable τ.cartan K false) σ) =
      fixCountS τ K (LargeEvenIsRoot τ.cartan) σ := by
  rw [fixNum_stableAct]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [largeEvenChevH_eq, Units.ext_iff, chevAct_val]
  rfl

theorem fixCountS_eq (τ : Tag) (K : Type) [Field K] (σ : K ≃+* K) :
    fixCountS τ K (LargeEvenIsRoot τ.cartan) σ = Nat.card (entrywiseFixedGroup τ σ) := by
  rw [largeEvenIsRoot_eq_isRoot τ]
  unfold fixCountS entrywiseFixedGroup
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [chevH_false_eq_adjointGroup K τ, Subgroup.mem_inf]
  refine and_congr_right fun _ => ?_
  change _ ↔ Units.map (Chevalley.entrywiseHom σ.toRingHom) g = g
  rw [Units.ext_iff]
  rfl

noncomputable def cardChevS (τ : Tag) (K : Type) [Field K] (S : (Fin τ.rank → ℤ) → Prop) : ℕ :=
  Nat.card (MarkChev.chevH τ.cartan S K false)

noncomputable def cardCenterChevS (τ : Tag) (K : Type) [Field K] (S : (Fin τ.rank → ℤ) → Prop) : ℕ :=
  Nat.card (Subgroup.center (MarkChev.chevH τ.cartan S K false))

theorem card_chevH (τ : Tag) (K : Type) [Field K] :
    Nat.card (LargeEvenChevH τ.cartan K false) = Nat.card (adjointGroup τ K) := by
  have h1 : Nat.card (LargeEvenChevH τ.cartan K false) = cardChevS τ K (LargeEvenIsRoot τ.cartan) := by
    rw [largeEvenChevH_eq]
    rfl
  rw [h1, largeEvenIsRoot_eq_isRoot τ]
  unfold cardChevS
  rw [chevH_false_eq_adjointGroup K τ]

theorem card_center_chevH (τ : Tag) (K : Type) [Field K] [Finite K] :
    Nat.card (Subgroup.center (LargeEvenChevH τ.cartan K false)) = 1 := by
  have h1 : Nat.card (Subgroup.center (LargeEvenChevH τ.cartan K false)) =
      cardCenterChevS τ K (LargeEvenIsRoot τ.cartan) := by
    rw [largeEvenChevH_eq]
    rfl
  rw [h1, largeEvenIsRoot_eq_isRoot τ]
  unfold cardCenterChevS
  rw [chevH_false_eq_adjointGroup K τ, center_adjointGroup_eq_bot]
  exact Subgroup.card_bot

end Bridge

section Main

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.YS09Field

@[expose] noncomputable def chevRho (τ : Tag) (K : Type) [Field K] :
    (K ≃+* K) →* MulAut ↥(LargeEvenChevH τ.cartan K false) :=
  stableAct (chevAct τ.cartan K) (chevAct_one τ.cartan K) (chevAct_mul τ.cartan K)
    (LargeEvenChevH τ.cartan K false) (chevH_stable τ.cartan K false)

theorem stOrderBody_chevalley {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : ℕ} (hm : 1 ≤ m) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) {p : ℕ} (hp : p.Prime)
    (I : Set (MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)))) :
    StOrderBody p (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)) I
      (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
  have hu : 0 < chevExp τ := by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> decide
  haveI : Finite ↥(LargeEvenChevH τ.cartan K false) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_chevH]
    obtain ⟨r, hr, h⟩ := card_adjointGroup_spec hτ hm hK
    rw [h]
    exact (Nat.mul_pos (by positivity) hr.pos).ne'
  refine stOrderBody_of_action (u := chevExp τ) (v := 1) hm hK
    (Subgroup.center (LargeEvenChevH τ.cartan K false)) le_rfl ?_ (chevRho τ K)
    (fun _ => True) (fun _ _ _ => trivial) hu one_pos ?_ ?_ hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩) I _ ?_
  · rw [card_center_chevH]
    exact odd_one
  · rw [pow_one, card_chevH]
    exact twoPart_card_adjointGroup hτ hm hK
  · intro σ _ e he
    have hk : Nat.card (fixSubfield σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, chevRho, fixNum_chev, fixCountS_eq,
      twoPart_card_entrywiseFixedGroup σ hk (one_le_of_card_fixed he)]
    exact twoPart_card_adjointGroup hτ (one_le_of_card_fixed he) hk
  · rintro f ⟨σ, hσ⟩
    refine ⟨σ, fun x => ?_⟩
    exact hσ x (chevRho τ K σ x) (by
      show ((chevAct τ.cartan K σ (x : LargeEvenChevGL τ.cartan K) : LargeEvenChevGL τ.cartan K) :
        Module.End K (LargeEvenChevModule τ.cartan K)) = _
      rw [chevAct_val])

end Main

end FQ

end CFSG.LocalAnalysis.GLTheoremA
