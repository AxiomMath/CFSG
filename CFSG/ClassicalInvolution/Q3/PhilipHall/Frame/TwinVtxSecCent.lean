module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecFam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecBridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecOddFree
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecLift
public import CFSG.ClassicalInvolution.Q3.TL4OddSecEdge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

section Basic

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem twinSecHyp_cent (hd : Q8TwinDatum R S t) (hRc : tightCore R = R)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {c : Y} (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hcm : c ∈ centralizerModOdd ⊤ R) :
    HypOmegaGen (CoreAssembly.conjClass (tightCore (secR R c))) := by
  have hB2 : IsPGroup 2 ↥(Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hBR : Subgroup.zpowers c ≤ centralizerModOdd ⊤ R := Subgroup.zpowers_le.mpr hcm
  obtain ⟨S', hS'⟩ := exists_sylow_le_centralizer hd hB2 hBR
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({c} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  have hΩ' : HypOmegaGen (CoreAssembly.conjClass R) := by rw [← hRc]; exact hΩ
  have hP : ∃ P : Subgroup Y, IsSylow2In P R ∧ P ≤ Subgroup.centralizer ({c} : Set Y) :=
    ⟨_, isSylow2In_map_sylow R S', hS'u⟩
  have hF := hypOmegaGen_sectionFamily hΩ' hP (H := secH R c) (le_subnormalClosure _)
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(secH R c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(secH R c)
  have hq := hypOmegaGen_quotFamily_odd hF hHodd
  rw [conjClass_tightCore_secR]
  exact hq

end Basic

section Main

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem classicalOrQuiet_or_of_cent {n : ℕ} (h : TwinCoreHyp n Y R S t)
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
    TL4.ClassicalOrQuiet c t htc ∨ ∃ ht, W ht := by
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
      (⟨⟨t, htc⟩, ht'⟩ : H)) → TL4.ClassicalOrQuiet c t htc ∨ ∃ ht, W ht :=
    fun h2 => Or.inl (Or.inr (TL4.quiet_of_inO2_sub (isSubnormal_subnormalClosure _) ht' h2))
  have hlift : TightHasLift (tightCore (secR R c))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨⟨t, htc⟩, ht'⟩ : H)) →
        TL4.ClassicalOrQuiet c t htc ∨ ∃ ht, W ht := by
    rintro ⟨L, -, hL⟩
    obtain ⟨K, hK⟩ := exists_sectionMember_of_oddQuot (isSubnormal_subnormalClosure _) ht'
      (Subtype.ext (TwinEdge.t_mul_t hd)) hL
    exact Or.inl (Or.inl ⟨K, hK⟩)
  have hboth : (TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨⟨t, htc⟩, ht'⟩ : H)) ∨ W ht') → TL4.ClassicalOrQuiet c t htc ∨ ∃ ht, W ht :=
    fun h2 => h2.elim hquiet (fun h3 => Or.inr ⟨ht', h3⟩)
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

theorem classicalOrQuietOrOddFree_of_cent {n : ℕ} (h : TwinCoreHyp n Y R S t)
    (hRc : tightCore R = R) (hZ : Subgroup.center Y = ⊥) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    (hex : ∀ (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c)
      (Sb : Sylow 2 ↥(tightCore (secR R c))),
      (TightEx (SecQ R c) (tightCore (secR R c)) Sb
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) ⟨⟨t, htc⟩, ht⟩) ∨
        TwinE4 (SecQ R c)) →
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)) ∨
        SecOddFree R c (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)))
    (hA : ∀ (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c),
      AEmpty (CoreAssembly.conjClass (tightCore (secR R c))) (tightCore (secR R c)) ∨
        TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)) ∨
        SecOddFree R c (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c))) :
    TL4.ClassicalOrQuiet c t htc ∨ MovedOddFreeAt c t htc := by
  rcases classicalOrQuiet_or_of_cent h hRc hZ hc2 hc1 hcm htc
      (fun ht => SecOddFree R c (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
        (⟨⟨t, htc⟩, ht⟩ : secH R c))) hex hA with h1 | ⟨ht, h2⟩
  · exact Or.inl h1
  · exact Or.inr (movedOddFreeAt_of_sec (isSubnormal_subnormalClosure _) ht rfl h2)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
