module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt2Exit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

section Sec

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
@[expose] def LiftedAtSec (R : Subgroup Y) (c t : Y) (htc : t ∈ Subgroup.centralizer ({c} : Set Y)) :
    Prop :=
  ∃ ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c,
    TightHasLift (tightCore (secR R c))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) (⟨⟨t, htc⟩, ht⟩ : secH R c))


variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem classicalOrQuiet_or_of_cent_sec {n : ℕ} (h : TwinCoreHyp n Y R S t)
    (hRc : tightCore R = R) (hZ : Subgroup.center Y = ⊥) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    (W : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c → Prop)
    (hex : ∀ (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c)
      (Sb : Sylow 2 ↥(tightCore (secR R c))),
      (TightEx (SecQ R c) (tightCore (secR R c)) Sb
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) ⟨⟨t, htc⟩, ht⟩) ∨
        TwinE4 (SecQ R c)) →
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)) ∨ W ht)
    (hA : ∀ (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c),
      AEmpty (CoreAssembly.conjClass (tightCore (secR R c))) (tightCore (secR R c)) ∨
        TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)) ∨ W ht) :
    Quiet c t htc ∨ LiftedAtSec R c t htc ∨ ∃ ht, W ht := by
  classical
  have hd := h.datum
  have hB2 : IsPGroup 2 ↥(Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hBR : Subgroup.zpowers c ≤ centralizerModOdd ⊤ R := Subgroup.zpowers_le.mpr hcm
  obtain ⟨S', hS'⟩ := exists_sylow_le_centralizer hd hB2 hBR
  have hdS := ofSylow hd S'
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({c} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := restrict hdS hS'u
  have hq8 : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) ≃*
      QuaternionGroup 2) :=
    ⟨e₁.trans ((Sylow.equiv S' S).trans h.q8.some)⟩
  obtain ⟨ht', S'', hdH, hgenH, hq8H⟩ := exists_sec hd₁ hq8
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    with hH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hdq := oddQuot hdH hHodd
  have hgenq := oddQuot_selfGen (N := classicalInvolutionOddCore ↥H) hgenH
  obtain ⟨e⟩ := hq8H
  have hq8q := (sylowEquiv hdH hHodd).symm.trans e
  have hOq : TightOddFree (SecQ R c) := CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
  obtain ⟨S₀, hdc, ⟨e₀⟩⟩ := toCore hdq
  have hidem := tightCore_idem (secR R c)
  have hgenc : TightSelfGen (tightCore (secR R c)) := by
    unfold TightSelfGen
    rw [hidem]
    exact hgenq
  have hq8c : Nonempty (↥(S₀ : Subgroup ↥(tightCore (secR R c))) ≃* QuaternionGroup 2) :=
    ⟨e₀.trans hq8q⟩
  have hΩ' := twinSecHyp_cent hd hRc h.hyp hc2 hc1 hcm
  rw [← hidem] at hΩ'
  have hlt : Nat.card (SecQ R c) < n := by
    have h1 : Nat.card (SecQ R c) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) :=
      Subgroup.card_le_card_group H
    have h3 := card_centralizer_lt_of_center hZ hc1
    rw [← h.card]
    omega
  have hquiet : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨⟨t, htc⟩, ht'⟩ : H)) → Quiet c t htc ∨ LiftedAtSec R c t htc ∨ ∃ ht, W ht :=
    fun h2 => Or.inl (TL4.quiet_of_inO2_sub (isSubnormal_subnormalClosure _) ht' h2)
  have hlift : TightHasLift (tightCore (secR R c))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨⟨t, htc⟩, ht'⟩ : H)) →
        Quiet c t htc ∨ LiftedAtSec R c t htc ∨ ∃ ht, W ht := by
    intro h2
    exact Or.inr (Or.inl ⟨ht', h2⟩)
  have hboth : (TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨⟨t, htc⟩, ht'⟩ : H)) ∨ W ht') → Quiet c t htc ∨ LiftedAtSec R c t htc ∨ ∃ ht, W ht :=
    fun h2 => h2.elim hquiet (fun h3 => Or.inr (Or.inr ⟨ht', h3⟩))
  rcases hA ht' with hAE | hA2
  swap
  · exact hboth hA2
  have hAE' := hAE
  rw [← hidem] at hAE'
  have hout := datumLift_of_IH h.twinBelow h.tbelow hlt hdc hq8c hgenc hOq hidem hΩ' hAE'
  by_cases htw : HasTwin (tightCore (secR R c))
  · rcases hout.1 htw with h2 | h2 | h2
    · exact hquiet h2
    · exact hboth (hex ht' S₀ (Or.inr h2))
    · exact hlift h2
  · rcases hout.2 htw with h2 | h2
    · exact hboth (hex ht' S₀ (Or.inl h2))
    · exact hlift h2


theorem quietLiftedSecExit_of_twin {n : ℕ} (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (h : TwinCoreHyp n Y R S t) (hRc : tightCore R = R)
    (hZ : Subgroup.center Y = ⊥) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    {K' : Subgroup Y} (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'ne : K' ≠ tightCore R) (hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K') :
    Quiet c t htc ∨ LiftedAtSec R c t htc ∨
      ((∃ _ : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c,
          ExitE4At (SecQ R c)) ∧ MovedOddFreeAt c t htc) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := h.hyp; rwa [hRc] at this
  have hA : ∀ M ∈ CoreAssembly.conjClass R, AEmpty (CoreAssembly.conjClass R) M := by
    have := h.aEmpty
    rw [hRc] at this
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩ.conjInvariant this g
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hcK : c ∈ Balance.Bootstrap.trivialOnQuot R := ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩
  have hΩs := twinSecHyp_cent h.datum hRc h.hyp hc2 hc1 hcm
  rcases classicalOrQuiet_or_of_cent_sec h hRc hZ hc2 hc1 hcm htc
      (fun ht => ExitE4At (SecQ R c) ∧
        SecOddFree R c (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)))
      (fun ht Sb hx => by
        rcases TwinExitPf2.hasTwin_or_inO2 h4 h hRc hc2 hc1 hcm htc ht hK' hK'ne hcK' with htw | i
        · have hΩ' : HypOmegaGen (CoreAssembly.conjClass (tightCore (tightCore (secR R c)))) := by
            rw [TwinEdge.tightCore_idem]; exact hΩs
          rcases hx with hx | hx
          · rcases hx with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4'
            · exact Or.inl h2
            · exact absurd he (TwinExitPf.not_tightEdgeless_of_hasTwin hΩ' htw)
            · exact absurd he (TwinExitPf.not_tightEdgeless_of_hasTwin hΩ' htw)
            · exact Or.inr ⟨Or.inr (Or.inl h4'), movedOddFreeIn_of_tightE4 hSp hD4 h4' _⟩
          · exact Or.inr ⟨Or.inl hx, movedOddFreeIn_of_twinE4 hSp hD4 hx _⟩
        · exact Or.inl i)
      (fun ht => Or.inl (TwinADescent2.aEmpty_section' hΩ (hA R (CoreAssembly.mem_conjClass_self R)) hc2' hcK)) with h1 | h1 | ⟨ht, he, o⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨⟨ht, he⟩,
      movedOddFreeAt_of_sec (isSubnormal_subnormalClosure _) ht rfl o⟩)

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
