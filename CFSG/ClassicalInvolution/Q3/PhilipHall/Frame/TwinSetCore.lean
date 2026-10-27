module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetReduce
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

section Core

structure TwinCoreHypS (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) : Prop where
  card : Nat.card Y = n
  simple : IsSimpleGroup ↥(genFittingFStar Y)
  nonab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a
  below : CIT3Below n
  tbelow : TightBelow n
  twinBelow : Thm1RTwinLiftSetBelow n
  datum : QuaternionBridge.Q8TwinDatum R S t
  q8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)
  gen : TightSelfGen R
  oddFree : TightOddFree Y
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore R))
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R

theorem TwinCoreHypS.toHyp {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (h : TwinCoreHypS n Y R S t) : TwinCoreHyp n Y R S t :=
  ⟨h.card, h.simple, h.nonab, h.below, h.tbelow, h.twinBelow.toHasLift, h.datum, h.q8, h.gen,
    h.oddFree, h.hyp, h.aEmpty, h.twin⟩

@[expose] def TwinCoreDiscPerpS' (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypS n Y R S t → ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) ≠
        twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) → False

@[expose] def TwinCoreConnSE' (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypS n Y R S t → Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      LongFundSetE3 R t

@[expose] def TwinCorePerpSE' (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypS n Y R S t → ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      TwinE4 Y ∨ LongFundSetE3 R t

@[expose] def Thm1RTwinCoreAtSE (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    IsSimpleGroup ↥(genFittingFStar Y) → (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R) →
      TwinE4 Y ∨ LongFundSetE3 R t

theorem thm1RTwinCoreAtSE_of_cases {n : ℕ} (hA : TwinCoreConnSE' n) (hB : TwinCoreDiscPerpS' n)
    (hC : TwinCorePerpSE' n) (hBelow : CIT3Below n) (hT : TightBelow n)
    (hL : Thm1RTwinLiftSetBelow n) : Thm1RTwinCoreAtSE n := by
  intro Y _ _ hcard hF hnab R S t hd hq hg hO hΩ hAe htw
  have h : TwinCoreHypS n Y R S t := ⟨hcard, hF, hnab, hBelow, hT, hL, hd, hq, hg, hO, hΩ, hAe, htw⟩
  by_cases hD : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  · exact Or.inr (hA Y R S t h hD)
  · by_cases hP : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)
    · exact hC Y R S t h hD hP
    · exact (hB Y R S t h hD hP).elim

end Core

@[expose] def Thm1RTwinCoreAtGen (P : ∀ (Y : Type) [Group Y], Subgroup Y → Y → Prop) (n : ℕ) :
    Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    IsSimpleGroup ↥(genFittingFStar Y) → (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R) →
      TwinE4 Y ∨ P Y R t

@[expose] def TwinXfer (P : ∀ (Y : Type) [Group Y], Subgroup Y → Y → Prop) (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    QuaternionBridge.Q8TwinDatum R S t →
    Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
    HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
    AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
    (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R) →
    ∀ (N : Subgroup Y) [N.Normal], Nat.card (Y ⧸ N) < n → N ≤ Subgroup.center Y →
      IsPGroup 2 ↥N → t ∉ N →
      P (Y ⧸ N) (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t) → P Y R t

theorem thm1RTwinLiftGenBelow_succ {P : ∀ (Y : Type) [Group Y], Subgroup Y → Y → Prop} {n : ℕ}
    (hX : TwinXfer P n) (hB : Thm1RTwinLiftGenBelow P n) (hcore : Thm1RTwinCoreAtGen P n) :
    Thm1RTwinLiftGenBelow P (n + 1) := by
  intro Y _ _ hlt R S t hd hq8 hgen hO hΩ hA htw
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
  · exact hB Y hlt' R S t hd hq8 hgen hO hΩ hA htw
  by_cases hE2 : TightInO2 t
  · exact Or.inl hE2
  have hE2' : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P := hE2
  have hO' : classicalInvolutionOddCore Y = ⊥ := hO
  right
  have hNn : (genFittingFitting Y).Normal := genFittingFitting_normal
  have hN2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hO'
  have htN : t ∉ genFittingFitting Y := fun h => hE2' ⟨_, hNn, hN2, h⟩
  have hNc : genFittingFitting Y ≤ Subgroup.center Y :=
    TwinRed.le_center_of_normal_two hd hgen hΩ hNn hN2 htN
  by_cases hN1 : genFittingFitting Y = ⊥
  · rcases twinDichotomy_of hd hq8 hgen hO hΩ with h | h | ⟨L, -, -, -, -, -, -, hFL⟩
    · exact absurd h hE2
    · obtain ⟨hs, hnab⟩ := TwinRed.fstar_simple_of_fitting_eq_bot h hN1
      rcases hcore Y heq hs hnab R S t hd hq8 hgen hO hΩ hA htw with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · exact absurd (hN1 ▸ bot_le) hFL
  · have : (genFittingFitting Y).Normal := hNn
    set N := genFittingFitting Y with hNdef
    have hRN : R ⊓ N = ⊥ := TwinRed.inf_eq_bot hd hN2 htN
    have h0 : tightCore R ⊓ N = ⊥ := TwinRed.core_inf_eq_bot hd hN2 htN
    have hlt2 : Nat.card (Y ⧸ N) < n := heq ▸ TwistQ.card_lt hN1
    rcases hB (Y ⧸ N) hlt2 (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S)
      (QuotientGroup.mk' N t) (TwinRed.q8TwinDatum_map hd hRN htN) (TwinRed.q8_map hRN hq8)
      (TwinRed.selfGen_map hRN hgen) (TwistQ.oddFree hNc hN2 hO')
      (TwinRed.hyp_map hΩ hNc hRN h0) (TwinRed.aEmpty_map hΩ hA hNc hRN h0)
      (TwinRed.twin_map hΩ hNc hRN h0 htw) with h | h | h
    · exact absurd (TwistQ.inO2_of hN2 h) hE2
    · exact Or.inl (TwinRed.twinE4_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hN2) h)
    · exact Or.inr (hX Y R S t hd hq8 hgen hO hΩ hA htw N hlt2 hNc hN2 htN h)

theorem twinXfer_E (n : ℕ) : TwinXfer (fun _ _ R t => LongFundSetE3 R t) n := by
  intro Y _ _ R S t hd hq8 hgen hO hΩ hA htw N _ hlt hNc hN2 htN h
  exact TwinSet.longFundSetE3_of_quot hd hΩ hNc hN2 htN h

theorem Thm1RTwinLiftSetEBelow.toSet {n : ℕ} (h : Thm1RTwinLiftSetEBelow n) :
    Thm1RTwinLiftSetBelow n := by
  intro Y _ _ hlt R S t hd hq hg hO hΩ hA htw
  rcases h Y hlt R S t hd hq hg hO hΩ hA htw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.toSet (Inner.isUniqueInvolution_core hd)))

theorem thm1RTwinLiftSetEBelow_succ {n : ℕ} (hB : Thm1RTwinLiftSetEBelow n)
    (hcore : Thm1RTwinCoreAtSE n) : Thm1RTwinLiftSetEBelow (n + 1) :=
  thm1RTwinLiftGenBelow_succ (P := fun _ _ R t => LongFundSetE3 R t) (twinXfer_E n) hB hcore

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
