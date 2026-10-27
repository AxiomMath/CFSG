module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLay
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkE2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan ThmDHyp)

section General

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {r : ℕ}

theorem isPGroup_of_inO2_typeR (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore X = ⊥)
    {L : Subgroup X} (hL : L ∈ Φ) {u : X} (hu : IsUniqueInvolution L u) {Q : Subgroup X}
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 ↥Q) (huQ : u ∈ Q) : IsPGroup 2 ↥L :=
  PhilipHall.Frame.isPGroup_of_oddCent h.hyp hL hu
    (TC.oddCoreImg_centralizer_eq_bot hO hQn hQ2 huQ) (h.twoGroup L hL)

omit [Finite X] in
theorem card_of_isPGroup_typeR (h : TypeRFam 3 Φ) {L : Subgroup X} (hL : L ∈ Φ)
    (h2 : IsPGroup 2 ↥L) : Nat.card ↥L = 2 ^ 3 := by
  obtain ⟨e⟩ := h.quat L hL L (AlphaFr.E2A.isSylow2In_self h2)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

end General

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem thmDHyp_linkFam (hL : TightLargeHypR 3 n Y R S t)
    (htr : ∀ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
      ∀ L' ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
        ∃ g : ↥(linkGrp R t), conjSub g L = L')
    (hO2 : ∃ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t), ∃ a : ↥(linkGrp R t),
      IsUniqueInvolution L a ∧ TightInO2 a) :
    ThmDHyp 3 (restrictFamily (coreLinkFam R t) (linkGrp R t)) := by
  have h := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hodd := oddCore_linkGrp_eq_bot hL
  obtain ⟨L₁, hL₁, a, ha, P, hPn, hP2, haP⟩ := hO2
  have hin : ∀ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t), ∀ u : ↥(linkGrp R t),
      IsUniqueInvolution L u → ∃ Q : Subgroup ↥(linkGrp R t), Q.Normal ∧ IsPGroup 2 ↥Q ∧ u ∈ Q := by
    intro L hL u hu
    obtain ⟨g, rfl⟩ := htr L₁ hL₁ L hL
    refine ⟨P, hPn, hP2, ?_⟩
    rw [← (ha.conj g).eq hu]
    exact hPn.conj_mem a haP g
  have htwo : ∀ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t), IsPGroup 2 ↥L := by
    intro L hL
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hin L hL u hu
    exact isPGroup_of_inO2_typeR h hodd hL hu hQn hQ2 huQ
  exact ⟨h.hyp, htwo, fun L hL => card_of_isPGroup_typeR h hL (htwo L hL),
    fun L hL => aEmpty_of_noTwins h.hyp hL (h.noTwins L hL), omegaGen_linkRestrict, htr, hodd,
    hin⟩

theorem natCard_linkGrp_lt (hL : TightLargeHypR 3 n Y R S t) : Nat.card ↥(linkGrp R t) < n :=
  (Subgroup.card_le_card_group (linkGrp R t)).trans_lt (AlphaFr.natCard_secQuot_lt_of_large hL)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.LinkE2
