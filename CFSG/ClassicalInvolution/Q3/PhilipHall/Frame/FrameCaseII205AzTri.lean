module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.AzTri

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

structure SecCoreHyp (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) : Prop where
  tbelow : TightBelow n
  twinBelow : Thm1RTwinHasLiftBelow n
  datum : QuaternionBridge.Q8TwinDatum R S t
  q8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore R))

section PairFam

variable {A : Type} [Group A]

@[expose] def pairFam (K₁ K₂ : Subgroup A) : Set (Subgroup A) :=
  {L | ∃ y : A, L = conjSub y K₁ ∨ L = conjSub y K₂}

theorem conjInvariant_pairFam (K₁ K₂ : Subgroup A) : ConjInvariant (pairFam K₁ K₂) := by
  rintro n L ⟨y, hL⟩
  refine ⟨n * y, ?_⟩
  rcases hL with rfl | rfl
  · exact Or.inl (conjSub_mul n y K₁).symm
  · exact Or.inr (conjSub_mul n y K₂).symm

theorem pairFam_subset {Φ : Set (Subgroup A)} (hΦ : ConjInvariant Φ) {K₁ K₂ : Subgroup A}
    (h₁ : K₁ ∈ Φ) (h₂ : K₂ ∈ Φ) : pairFam K₁ K₂ ⊆ Φ := by
  rintro L ⟨y, rfl | rfl⟩
  · exact hΦ y K₁ h₁
  · exact hΦ y K₂ h₂

theorem left_mem_pairFam (K₁ K₂ : Subgroup A) : K₁ ∈ pairFam K₁ K₂ :=
  ⟨1, Or.inl (conjSub_one K₁).symm⟩

theorem right_mem_pairFam (K₁ K₂ : Subgroup A) : K₂ ∈ pairFam K₁ K₂ :=
  ⟨1, Or.inr (conjSub_one K₂).symm⟩

end PairFam

section Sec

variable {Y : Type} [Group Y] [Finite Y]

open CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL

variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem classicalOrQuiet_or_of_cent_sec' {n : ℕ} (h : SecCoreHyp n R S t)
    (hRc : tightCore R = R) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hlt0 : Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) < n)
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

theorem liftedAt_of_liftedAtSec {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (h : SecCoreHyp n R S t) {c : Y} {htc : t ∈ Subgroup.centralizer ({c} : Set Y)}
    (l : LiftedAtSec R c t htc) : LiftedAt R c t := by
  obtain ⟨ht', L, hLle, hL⟩ := l
  have hd := h.datum
  have hidem := tightCore_idem (secR R c)
  rw [hidem] at hLle
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    with hH
  set Kc : Subgroup ↥(Subgroup.centralizer ({c} : Set Y)) :=
    tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) with hKc
  have hKcH : Kc ≤ H := le_subnormalClosure _
  set A : Subgroup ↥H := Kc.subgroupOf H with hAdef
  have hAt : A ≤ Subgroup.centralizer ({(⟨⟨t, htc⟩, ht'⟩ : ↥H)} : Set ↥H) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have haK : (a : ↥(Subgroup.centralizer ({c} : Set Y))) ∈ Kc := ha
    have haR : ((a : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) ∈ R :=
      Subgroup.mem_subgroupOf.mp (tightCore_le _ haK)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hd.cent haR)
    apply Subtype.ext
    apply Subtype.ext
    exact this
  have hAL : A.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) ≤ L := by
    refine le_trans ?_ hLle
    have h1 : tightCore ((R.subgroupOf (Subgroup.centralizer ({c} : Set Y))).subgroupOf H) =
        A := CFSG.ClassicalInvolution.Q3.tightCore_subgroupOf hKcH
    rw [← h1]
    exact map_tightCore_le _ _
  obtain ⟨K, hK, hAK⟩ := exists_sectionMember_of_oddQuot' (isSubnormal_subnormalClosure _) ht'
    (Subtype.ext (TwinEdge.t_mul_t hd)) hL hAt hAL
  refine ⟨K, hK, ?_⟩
  have h2 : A.map H.subtype = Kc := Subgroup.map_subgroupOf_eq_of_le hKcH
  rw [h2] at hAK
  exact hAK

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.AzTri
