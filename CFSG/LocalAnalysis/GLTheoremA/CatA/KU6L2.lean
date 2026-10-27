module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.Adapters.LinearCatalog
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.I142N (GLALayer_eq_sSup le_GLALayer GLALayer_le_of)

private theorem kuL2_carrier {q' : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q').Valid) (hq4 : 4 ≤ q'.card) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group ∧
      Nat.card (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group =
        q'.card * (q'.card ^ 2 - 1) / Nat.gcd 2 (q'.card - 1) := by
  haveI : Fact q'.p.Prime := ⟨q'.prime_p⟩
  have hK : Nat.card (GaloisField q'.p q'.exponent) = q'.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q'.p q'.exponent q'.exponent_pos.ne'
  let ePSL := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q' hv
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
      (GaloisField q'.p q'.exponent)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; exact hq4)
  refine ⟨ePSL.isSimpleGroup, ?_⟩
  have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (K := GaloisField q'.p q'.exponent) (n := 2) (by norm_num)
  rw [hK] at h1
  rw [Nat.card_congr (ePSL.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField q'.p q'.exponent))).toEquiv, h1]
  simp [Finset.Icc_self]

theorem catL2eight_simple_card {S : Type} [Group S] [Finite S]
    (h : catalogIs S S10.isL2eight) : IsSimpleGroup S ∧ Nat.card S = 504 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isL2eight, onLie] at hi
  | alternating n hn => simp [S10.isL2eight, onLie] at hi
  | sporadic s => simp [S10.isL2eight, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A n q =>
      rcases n with _ | _ | n
      · simp [S10.isL2eight, onLie] at hi
      · have hq : q.card = 8 := hi
        obtain ⟨hs, hc⟩ := kuL2_carrier hv (by rw [hq]; norm_num)
        haveI := hs
        refine ⟨e.isSimpleGroup, ?_⟩
        rw [Nat.card_congr e.toEquiv, hc, hq]
        norm_num
      · simp [S10.isL2eight, onLie] at hi
    | _ => simp [S10.isL2eight, onLie] at hi


theorem glaLayer_perfect {G : Type} [Group G] (H : Subgroup G) : Group.IsPerfect ↥(GLALayer H) := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact (GLALayer H).mul_mem ((GLALayer H).mul_mem ((GLALayer H).mul_mem hx hy)
      ((GLALayer H).inv_mem hx)) ((GLALayer H).inv_mem hy)
  · rw [GLALayer_eq_sSup]
    refine sSup_le fun L hL => ?_
    have hLE : L ≤ GLALayer H := le_GLALayer hL
    have hLp : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
    calc L = ⁅L, L⁆ := (Subgroup.isPerfect_iff.1 hLp).symm
      _ ≤ ⁅GLALayer H, GLALayer H⁆ := Subgroup.commutator_mono hLE hLE

theorem glaLayer_conj_le {G : Type} [Group G] (H : Subgroup G) {h : G} (hh : h ∈ H) :
    (GLALayer H).map (MulAut.conj h).toMonoidHom ≤ GLALayer H := by
  set c := (MulAut.conj h).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj h).injective
  have hHc : H.map c = H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show h * x * h⁻¹ ∈ H
      exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    · intro x hx
      refine ⟨h⁻¹ * x * h, H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh, ?_⟩
      show h * (h⁻¹ * x * h) * h⁻¹ = x
      group
  have hcomp : ∀ L : Subgroup G, IsComponentOf L H → IsComponentOf (L.map c) H := by
    intro L hL
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (H.mul_mem (H.mul_mem hh (hL.1 hx)) (H.inv_mem hh) : h * x * h⁻¹ ∈ H)
    · have := hL.2.1.map c
      rw [hHc] at this
      exact this
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective L c hcinj).symm hL.2.2
  have key : GLALayer H ≤ (GLALayer H).comap c :=
    GLALayer_le_of fun L hL => Subgroup.map_le_iff_le_comap.1 (le_GLALayer (hcomp L hL))
  exact Subgroup.map_le_iff_le_comap.2 key

end CFSG.LocalAnalysis.GLTheoremA
