module

public import CFSG.ClassicalInvolution.Q3.Sec13StarHyp
public import CFSG.ClassicalInvolution.Q3.TL3T39
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2E8
public import CFSG.ClassicalInvolution.Asc77.AscS22B
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916Coh
public import CFSG.ClassicalInvolution.AschTight.S1916Inv
public import CFSG.ClassicalInvolution.AschTight.S19QT68
public import CFSG.ClassicalInvolution.AschTight.S19QTInv
public import CFSG.ClassicalInvolution.AschTight.S19QTSign
public import CFSG.ClassicalInvolution.AschTight.S19TF1
public import CFSG.ClassicalInvolution.Balance.CentralizedDeltaBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LargeFrameExits
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.PairInfCenter
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfPerfect
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnFinalFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnFinalModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf6Q8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf8Exit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtSylow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPairOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEApply
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf2Base
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeA
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Sq
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Nbr
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AET
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2W
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem omegaStarNbr_of_quotZ {r : ℕ} {Ω : Set (Subgroup G)} {Z : Subgroup G} [Z.Normal]
    (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G) (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' Z) ∈
      omegaStarNbr (quotFamZ Z Ω) (K.map (QuotientGroup.mk' Z))) :
    J ∈ omegaStarNbr Ω K := by
  set πz := QuotientGroup.mk' Z
  have hΩ' : HypOmegaGen (quotFamZ Z Ω) := (thmDHypO_quotZ hD hZc hZK).hyp
  obtain ⟨-, hne, U', hU', hU'J, hU'N⟩ := h
  obtain ⟨-, -, -, u', hu'U', -, hzp'⟩ := TC.Thin.exists_of_mem_USet hΩ' hU'
  obtain ⟨u, huJ, rfl⟩ := hU'J hu'U'
  set U := Subgroup.zpowers u with hUdef
  have hUmap : U.map πz = U' := by rw [hUdef, MonoidHom.map_zpowers, hzp']
  have hUJ : U ≤ J := Subgroup.zpowers_le.mpr huJ
  have hU : U ∈ USet Ω := by
    refine ⟨J, TC.mem_RSet_of_isPGroup hJ (hD.two J hJ), hUJ, inferInstance, ?_⟩
    obtain ⟨R', hR', hU'R', -, hidx'⟩ := hU'
    obtain ⟨L'', hL'', hR'L'', -, hmax'⟩ := mem_RSet_iff.mp hR'
    obtain ⟨L₂, hL₂, rfl⟩ := hL''
    beta_reduce at hR'L'' hmax'
    have hL₂2 : IsPGroup 2 ↥(L₂.map πz) := (hD.two L₂ hL₂).map _
    have hR'eq : L₂.map πz = R' := hmax' _ le_rfl hL₂2 hR'L''
    have hcard : Nat.card ↥(L₂.map πz) = Nat.card L₂ := by
      have hinj := TwistQ.subgroupMap_injective (N := Z)
        (show L₂ ⊓ Z = ⊥ by rw [inf_comm]; exact hZK L₂ hL₂)
      exact (Nat.card_eq_of_bijective _ ⟨hinj, MonoidHom.subgroupMap_surjective πz L₂⟩).symm
    have hcU : Nat.card U = Nat.card U' := by
      rw [← hzp', Nat.card_zpowers, Nat.card_zpowers, TC.Thin.orderOf_mk_eq (hZK J hJ) huJ]
    have h1 := Subgroup.relIndex_mul_card U' R'
    rw [inf_eq_left.mpr hU'R', hidx', ← hR'eq, hcard, hD.card L₂ hL₂] at h1
    have h3 := Subgroup.relIndex_mul_card U J
    rw [inf_eq_left.mpr hUJ, hcU, hD.card J hJ] at h3
    have h4 : U.relIndex J * Nat.card U' = 2 * Nat.card U' := by rw [h3, h1]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h4
  refine ⟨hJ, fun h => hne (by rw [h]), U, hU, hUJ, fun x hx => ?_⟩
  have hx' : πz x ∈ U' := hUmap ▸ ⟨x, hx, rfl⟩
  have h1 := mem_normalizer_iff_conjSub_eq.mp (hU'N hx')
  rw [← TwistQ.conjSub_map] at h1
  exact mem_normalizer_iff_conjSub_eq.mpr
    (TC.Thin.eq_of_map_eq hD.hyp hD.two hZc hZK (hD.hyp.conjInvariant x K hK) hK h1)

private theorem mem_dstarComp_of_spanQuot {r : ℕ} {Ω : Set (Subgroup G)} (hD : ThmDHyp r Ω)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hc : T3.DStarConnected
      (quotFamZ (classicalInvolutionOddCore ↥(pSpan P)) (restrictFamily P (pSpan P))))
    {K L : Subgroup G} (hK : K ∈ P) (hL : L ∈ P) : L ∈ dstarComp Ω K := by
  set X := pSpan P
  set R := classicalInvolutionOddCore ↥X
  set q := QuotientGroup.mk' R
  have hLX : ∀ M ∈ P, M ≤ X := fun M hM => le_pSpan hM
  have hO := thmDHypO_restrict (r := r) hD.hyp hD.two hD.card hD.aEmpty hD.inO2 hPΩ hinv
  have hRc : R ≤ Subgroup.center ↥X := oddCore_le_center hD.hyp hD.two hD.inO2 hPΩ hinv
  have hRK : ∀ M ∈ restrictFamily P X, R ⊓ M = ⊥ := fun M hM =>
    oddCore_inf_eq_bot (hO.two M hM)
  have hmemX : ∀ M ∈ P, M.subgroupOf X ∈ restrictFamily P X := fun M hM =>
    ⟨M, hM, hLX M hM, rfl⟩
  have heq : ∀ {M M' : Subgroup G}, M ∈ P → M' ∈ P →
      (M.subgroupOf X).map q = (M'.subgroupOf X).map q → M = M' := by
    intro M M' hM hM' h
    have h1 := TC.Thin.eq_of_map_eq hO.hyp hO.two hRc hRK (hmemX M hM) (hmemX M' hM') h
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr (hLX M hM), inf_eq_left.mpr (hLX M' hM')] at h2
  have hstar : ∀ {M M' : Subgroup G}, M ∈ P → M' ∈ P →
      (M'.subgroupOf X).map q ∈
        omegaStarNbr (quotFamZ R (restrictFamily P X)) ((M.subgroupOf X).map q) →
      M' ∈ omegaStarNbr Ω M := by
    intro M M' hM hM' h
    obtain ⟨-, hne, U, hU, hUM, hUN⟩ := omegaStarNbr_of_restrict (hLX M hM) (hLX M' hM')
      (omegaStarNbr_of_quotZ hO hRc hRK (hmemX M hM) (hmemX M' hM') h)
    exact ⟨hPΩ hM', hne, U, TC.Thin.USet_mono hPΩ hU, hUM, hUN⟩
  have hlift : ∀ M' ∈ dstarComp (quotFamZ R (restrictFamily P X)) ((K.subgroupOf X).map q),
      ∃ M ∈ P, (M.subgroupOf X).map q = M' ∧ M ∈ dstarComp Ω K := by
    intro M' hM'
    induction hM' with
    | refl => exact ⟨K, hK, rfl, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      obtain ⟨N, hN, rfl, hNK⟩ := ih
      obtain ⟨_, ⟨M, hM, -, rfl⟩, rfl⟩ := hbc.1
      refine ⟨M, hM, rfl, hNK.tail ⟨hPΩ hM, ?_⟩⟩
      rcases hbc.2 with h' | h'
      · exact Or.inl (hstar hN hM h')
      · exact Or.inr (hstar hM hN h')
  obtain ⟨M, hM, hML, hMK⟩ := hlift _ (hc _ ⟨_, hmemX K hK, rfl⟩ _ ⟨_, hmemX L hL, rfl⟩)
  rwa [heq hM hL hML] at hMK

private theorem q8Fam_spanQuot {Ω : Set (Subgroup G)} (hD : ThmDHyp 3 Ω) {P : Set (Subgroup G)}
    (hPΩ : P ⊆ Ω) (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) :
    PhilipHall.Frame.TwinDisc.ExitO2.Q8Fam (↥(pSpan P) ⧸ classicalInvolutionOddCore ↥(pSpan P))
      (quotFamZ (classicalInvolutionOddCore ↥(pSpan P)) (restrictFamily P (pSpan P))) := by
  set R := classicalInvolutionOddCore ↥(pSpan P)
  have hO := thmDHypO_restrict (r := 3) hD.hyp hD.two hD.card hD.aEmpty hD.inO2 hPΩ hinv
  have hRc : R ≤ Subgroup.center ↥(pSpan P) := oddCore_le_center hD.hyp hD.two hD.inO2 hPΩ hinv
  have hRK : ∀ M ∈ restrictFamily P (pSpan P), R ⊓ M = ⊥ := fun M hM =>
    oddCore_inf_eq_bot (hO.two M hM)
  have hQ := thmDHypO_quotZ hO hRc hRK
  refine ⟨hQ.hyp, hQ.two, fun L hL => ?_, hQ.aEmpty, hQ.gen, ?_,
    QuaternionStructure.oddCore_quotient_oddCore_eq_bot _, hQ.inO2⟩
  ·
    obtain ⟨k, -, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hQ.hyp
      (TC.mem_RSet_of_isPGroup hL (hQ.two L hL))
    have hc : 2 ^ (k + 2) = 2 ^ 3 := by
      rw [← hQ.card L hL, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
        QuaternionGroup.card]
      ring
    obtain rfl : k = 1 := by
      have := Nat.pow_right_injective (le_refl 2) hc
      omega
    exact ⟨e⟩
  · rintro _ ⟨M, hM, rfl⟩ _ ⟨M', hM', rfl⟩
    obtain ⟨g, hg⟩ := trans_restrict htrans M hM M' hM'
    exact ⟨QuotientGroup.mk' R g, by rw [← TwistQ.conjSub_map, hg]⟩

namespace StarHyp

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

theorem centMembers_dichotomy {a : G} (ha : a ≠ 1) {K : Subgroup G}
    (hK : K ∈ Generic.centMembers Ω a) :
    (∀ L ∈ Generic.centMembers Ω a, L ∈ dstarComp Ω K) ∨
      Nonempty (AEIdent (Generic.centMembers Ω a) 5) := by
  set P := Generic.centMembers Ω a
  have hD := h.thmD
  have hPΩ : P ⊆ Ω := fun L hL => hL.1
  have hXC : pSpan P ≤ Subgroup.centralizer ({a} : Set G) := pSpan_le fun L hL => hL.2
  have hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := by
    intro L hL x hx
    refine ⟨hD.hyp.conjInvariant x L hL.1, fun y hy => ?_⟩
    rw [mem_conjSub_iff] at hy
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXC hx) (hL.2 hy))
      (Subgroup.inv_mem _ (hXC hx))
  have hlt : Nat.card ↥(pSpan P) < Nat.card G := by
    have hCt : Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
      intro htop
      apply ha
      have hzc : a ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
      rw [h.center, Subgroup.mem_bot] at hzc
      exact hzc
    have := Subgroup.card_lt_of_lt (lt_of_le_of_lt hXC (lt_top_iff_ne_top.mpr hCt))
    rwa [Subgroup.card_top] at this
  by_cases htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L'
  ·
    have F := q8Fam_spanQuot hD hPΩ htrans hinv
    have hconn := fun hc L (hL : L ∈ P) => mem_dstarComp_of_spanQuot hD hPΩ hinv hc hK hL
    rcases thmDConcl_spanQuot hD h.below hPΩ hlt htrans hinv with
      hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | hI64 | ⟨m, hm, ⟨I⟩⟩ | hI29
    · refine Or.inl (hconn fun K' hK' J' hJ' => ?_)
      rw [hsing K' hK' J' hJ']
      exact Relation.ReflTransGen.refl
    · exact Or.inl (hconn (PhilipHall.Frame.TwinDisc.ExitO2.fam_dstarConnected_of_wSet F hW))
    · exact Or.inl (hconn (PhilipHall.Frame.TwinDisc.ExitO2.fam_dstarConnected_of_e8 F hE))
    · obtain ⟨I⟩ := hI64
      exact Or.inl (hconn (PhilipHall.Frame.TwinDisc.ExitO2.fam_dstarConnected_of_e64 F I))
    · rcases Nat.lt_or_ge m 6 with h6 | h6
      · obtain rfl : m = 5 := by omega
        exact Or.inr ⟨AEIdent.ofSpanQuot hD hPΩ hinv I⟩
      · exact Or.inl
          (hconn (PhilipHall.Frame.TwinDisc.ExitO2.fam_dstarConnected_of_aeIdent F h6 I))
    · obtain ⟨I⟩ := hI29
      exact Or.inl (hconn (PhilipHall.Frame.TwinDisc.ExitO2.fam_dstarConnected_of_e29 F I))
  ·
    left
    obtain ⟨M₁, hM₁, M₂, hM₂, hnc⟩ :
        ∃ M₁ ∈ P, ∃ M₂ ∈ P, ¬ ∃ x ∈ pSpan P, conjSub x M₁ = M₂ := by
      by_contra hne
      exact htrans fun L hL L' hL' => by_contra fun h' => hne ⟨L, hL, L', hL', h'⟩
    have hd1 := d1GenLeaf_holds 3 _ (thmDGenBelow_of_absBelow h.below)
    have hcomm : ∀ {L L' : Subgroup G}, L ∈ P → L' ∈ P →
        (¬ ∃ x ∈ pSpan P, conjSub x L = L') → Commutes L L' :=
      fun hL hL' hn => comm_of_not_conj_span hD hd1 hPΩ hlt hinv hL hL' hn
    have hsymm : ∀ {L L' : Subgroup G}, (∃ x ∈ pSpan P, conjSub x L = L') →
        ∃ x ∈ pSpan P, conjSub x L' = L := by
      rintro L L' ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, (pSpan P).inv_mem hx, conjSub_inv_conjSub x L⟩
    have htr : ∀ {L L' L'' : Subgroup G}, (∃ x ∈ pSpan P, conjSub x L = L') →
        (∃ x ∈ pSpan P, conjSub x L' = L'') → ∃ x ∈ pSpan P, conjSub x L = L'' := by
      rintro L L' L'' ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨y * x, (pSpan P).mul_mem hy hx, conjSub_mul y x L⟩
    obtain ⟨M, hM, hKM⟩ : ∃ M ∈ P, ¬ ∃ x ∈ pSpan P, conjSub x K = M := by
      by_cases h1 : ∃ x ∈ pSpan P, conjSub x K = M₁
      · exact ⟨M₂, hM₂, fun h2 => hnc (htr (hsymm h1) h2)⟩
      · exact ⟨M₁, hM₁, h1⟩
    intro L hL
    by_cases hKL : ∃ x ∈ pSpan P, conjSub x K = L
    ·
      have hLM : ¬ ∃ x ∈ pSpan P, conjSub x L = M := fun h2 => hKM (htr hKL h2)
      exact Relation.ReflTransGen.trans
        (h.mem_dstarComp_of_commutes (hPΩ hM) (hPΩ hK) (hcomm hK hM hKM).symm)
        (h.mem_dstarComp_of_commutes (hPΩ hL) (hPΩ hM) (hcomm hL hM hLM))
    · exact h.mem_dstarComp_of_commutes (hPΩ hL) (hPΩ hK) (hcomm hK hL hKL).symm

end StarHyp

end CFSG.ClassicalInvolution.Q3.Sec13
