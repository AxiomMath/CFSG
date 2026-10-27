module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnQuiet
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SubnormalE2

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

section InO2Cent


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {r n : ℕ}

theorem inO2_cent_of_twin_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n Y R S t) (hRc : tightCore R = R) (hZ : Subgroup.center Y = ⊥) {c : Y}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hcm : c ∈ centralizerModOdd ⊤ R)
    (htc : t ∈ Subgroup.centralizer ({c} : Set Y)) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'ne : K' ≠ tightCore R) (hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K') :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set Y)))
      (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y))) := by
  classical
  have hd := h.datum
  have hB2 : IsPGroup 2 ↥(Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hBR : Subgroup.zpowers c ≤ centralizerModOdd ⊤ R := Subgroup.zpowers_le.mpr hcm
  obtain ⟨S', hS'⟩ := TwinEdge.exists_sylow_le_centralizer hd hB2 hBR
  have hdS := TwinEdge.ofSylow hd S'
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({c} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := TwinEdge.restrict hdS hS'u
  have hq8 : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) ≃*
      QuaternionGroup (2 ^ (r - 2))) :=
    ⟨e₁.trans ((Sylow.equiv S' S).trans h.quat.some)⟩
  obtain ⟨ht', S'', hdH, hgenH, hq8H⟩ := exists_secK hd₁ hq8
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    with hH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hdq := TwinEdge.oddQuot hdH hHodd
  have hgenq := TwinEdge.oddQuot_selfGen (N := classicalInvolutionOddCore ↥H) hgenH
  obtain ⟨e⟩ := hq8H
  have hq8q := (TwinEdge.sylowEquiv hdH hHodd).symm.trans e
  have hOq : TightOddFree (SecQ R c) := CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
  obtain ⟨S₀, hdc, ⟨e₀⟩⟩ := TwinEdge.toCore hdq
  have hidem := TwinEdge.tightCore_idem (secR R c)
  have hgenc : TightSelfGen (tightCore (secR R c)) := by
    unfold TightSelfGen
    rw [hidem]
    exact hgenq
  have hq8c : Nonempty (↥(S₀ : Subgroup ↥(tightCore (secR R c))) ≃*
      QuaternionGroup (2 ^ (r - 2))) := ⟨e₀.trans hq8q⟩
  have hΩ' := TwinVtx.twinSecHyp_cent hd hRc h.hyp hc2 hc1 hcm
  rw [← hidem] at hΩ'
  have hlt : Nat.card (SecQ R c) < n := by
    have h1 : Nat.card (SecQ R c) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) :=
      Subgroup.card_le_card_group H
    have h3 := TwinEdge.card_centralizer_lt_of_center hZ hc1
    rw [← h.card]
    omega
  have hΩ : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := h.hyp; rwa [hRc] at this
  have hA : ∀ M ∈ CoreAssembly.conjClass R, AEmpty (CoreAssembly.conjClass R) M := by
    have := h.aEmpty
    rw [hRc] at this
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩ.conjInvariant this g
  have hcK : c ∈ Balance.Bootstrap.trivialOnQuot R := ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩
  have hAE := TwinADescent2.aEmpty_section' hΩ (hA R (CoreAssembly.mem_conjClass_self R)) hB2 hcK
  have hAE' := hAE
  rw [← hidem] at hAE'
  rcases hasTwin_or_inO2_R h4 h hRc hc2 hc1 hcm htc ht' hK' hK'ne hcK' with htw | hi
  · exact tightInO2_oddQuot_of_subnormal (isSubnormal_subnormalClosure _) ht'
      (hT (SecQ R c) hlt (tightCore (secR R c)) S₀ _ hdc hq8c hgenc hOq hΩ' hAE' htw)
  · exact tightInO2_oddQuot_of_subnormal (isSubnormal_subnormalClosure _) ht' hi

end InO2Cent

end CFSG.CGT.PushingUpLit.SolKNA.R4
