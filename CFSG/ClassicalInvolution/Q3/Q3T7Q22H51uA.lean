module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Rows
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3CHSec
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77


section Witness

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_witness_alpha3 (hBelow : CIT3Below (Nat.card G)) {Φ : Set (Subgroup G)}
    {c b : G} {M B : Subgroup G} (hΦ : SecData3 c Φ)
    (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) (hM : M ∈ Φ)
    (hMb : IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M b)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) (hbB : b ∈ B) (hbc : b ≠ c)
    (hα : ∀ (ι : Type) (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
        (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
          (centralizingLayer Φ {c})))) (j : ι),
      modOdd c M ≤ secComp hΦ D j → MovedByAll B c (secComp hΦ D j) →
        CFSG.IsComponent (secComp hΦ D j) →
          alphaOf (inducedImage (secComp hΦ D j) (modOdd c B)) = ⊥) :
    Asc77.Hyp51At B c := by
  classical
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hnc
  have hb1 : b ≠ 1 := fun h => by
    have := hMb.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := hMb.le hMb.mem
  obtain ⟨j₁, hj₁⟩ := exists_modOdd_le_secComp hΦ D hM
  have hb₁ : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c M := oddQuotMk_mem_modOdd hMb.mem hbC
  have hm₁ : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      L = secComp hΦ D j₁ := fun L hL hm =>
    eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC (hj₁ hb₁) hL hm
  refine ⟨fun L L' hL hL' hm hm' => (hm₁ L hL hm).trans (hm₁ L' hL' hm').symm, fun L hL hm => ?_⟩
  have hLj₁ := hm₁ L hL hm
  subst hLj₁
  exact hα ι D j₁ hj₁ hm hL

end Witness

section Component

theorem alphaOf_eq_bot_of_twinSq_comp3 (hrows : TwinSqAlphaAll3) {c : CompData}
    (hc : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n)
    {H : Type} [Group H] [Finite H] (ψ : c.G →* H) (R R' : Subgroup c.G) (x x' : c.G)
    (hker : ψ.ker ≤ Subgroup.center c.G) (hR : R ∈ c.fund) (hR' : R' ∈ c.fund) (hne : R ≠ R')
    (hcomm : Commutes R R') (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hsame : ψ x = ψ x') {k : c.G} (hk : k ∈ R)
    (hkk : ψ k * ψ k = ψ x) (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) :
    alphaOf (Subgroup.closure ({FrameVertex.innerHom ψ k * v, FrameVertex.innerHom ψ x} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  obtain ⟨t, n, ht, hadm, rfl⟩ := hc
  exact hrows t n ht hadm H ψ R R' x x'
    ⟨hker, hR, hR', hne, hcomm, hx, hx2, hx1, hx', hx'2, hx'1, hsame⟩ k hk hkk v hvR hvR' hvv

end Component

end CFSG.ClassicalInvolution.Q3.Q3T7
