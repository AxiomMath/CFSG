module

public import CFSG.Certificates.Kernel.Th.Spec.DceCover
public import CFSG.Certificates.Kernel.DceTwCore
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw

set_option exponentiation.threshold 700

theorem sorted_inj {get : ℕ → ℕ} {qb m : ℕ} {Cs : List ℕ} {Y1 : ℕ}
    (h : DceS.runSorted get qb m Cs 1 = Y1) (hc : sortedCount Y1 = m) :
    ∀ k < m, ∀ k' < m, get k = get k' → k = k' :=
  (sortRun_spec (runSorted_eq _ _ _ _ _ ▸ h) hc).2

theorem tab_stab {HB TB OB RR FA : ℕ → ℕ} {Ct : List ℕ}
    {LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA : ℕ}
    (hT : runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA Ct 1 =
      nT + 1) : ∀ e < nT, ∃ tau, actOK NB sel (pt OB osh owd om I0) (tSig HB TB e)
        (pt OB osh owd om I0) tau = true := by
  rw [runT_eq] at hT
  have hi := cntRun_spec (a := 0) hT
  intro e he
  obtain ⟨J, ht⟩ := hi e (Nat.zero_le _) he
  obtain ⟨-, -, -, hact, -⟩ := tOK_spec ht
  exact ⟨_, hact⟩

instance instFiniteMat24Units : Finite Mat24ˣ :=
  Finite.of_injective (Units.val : Mat24ˣ → Mat24) Units.val_injective

theorem orb_of {M : Subgroup Mat24ˣ} {HB GB TB OB : ℕ → ℕ} {NO nT NORD I0 osh owd om NB sel : ℕ}
    (hsel : DceS.selOK NB sel = true) (hom : om = Nat.sub (Nat.shiftLeft 1 (Nat.mul 24 NB)) 1)
    (hgj : ∀ j < NO, InM M (gm HB GB j) ∧ (NB = 1 ∨ rowsOK NB (pt OB osh owd om j) = true) ∧
      ∃ tau, actOK NB sel (pt OB osh owd om I0) (gm HB GB j) (pt OB osh owd om j) tau = true)
    (hts : ∀ e < nT, InM M (tSig HB TB e) ∧ ∃ tau, actOK NB sel (pt OB osh owd om I0)
      (tSig HB TB e) (pt OB osh owd om I0) tau = true)
    (hinjO : ∀ k < NO, ∀ k' < NO, pt OB osh owd om k = pt OB osh owd om k' → k = k')
    (hinjT : ∀ e < nT, ∀ e' < nT, tSig HB TB e = tSig HB TB e' → e = e')
    (hI0 : I0 < NO) (hnord : nT * NO = NORD) (hcard : Nat.card M ≤ NORD) :
    Orb M NORD (Finset (Fin 24 → ZMod 2)) actP (ptS NB (pt OB osh owd om I0))
      (fun j => ptS NB (pt OB osh owd om j)) (fun j => mEl M (gm HB GB j)) NO I0
      (fun e => mEl M (tSig HB TB e)) nT := by
  have hP : ∀ w, pt OB osh owd om w < 2 ^ (24 * NB) := fun w => pt_lt hom w
  refine
    { finM := inferInstance
      cardM := hcard
      act_one := actP_one
      act_mul := actP_mul
      orbit := fun j hj => ?_
      ω_inj := fun j hj j' hj' h => hinjO j hj j' hj'
        (ptS_inj (hP j) (hP j') (hgj j hj).2.1 (hgj j' hj').2.1 h)
      I0_lt := hI0
      ωI0 := rfl
      stab := fun e he => ?_
      σ_inj := fun e he e' he' h => hinjT e he e' he' ?_
      nord := hnord }
  · obtain ⟨hm, hq, tau, hact⟩ := hgj j hj
    exact actOK_sound hsel hq (hP I0) hact _ (mEl_val hm)
  · obtain ⟨hm, tau, hact⟩ := hts e he
    exact actOK_sound hsel (hgj I0 hI0).2.1 (hP I0) hact _ (mEl_val hm)
  · have e2 : ((((mEl M (tSig HB TB e) : M) : Mat24ˣ) : Mat24)) =
        (((mEl M (tSig HB TB e') : M) : Mat24ˣ) : Mat24) := by
      have h' : mEl M (tSig HB TB e) = mEl M (tSig HB TB e') := h
      rw [h']
    rw [mEl_val (hts e he).1, mEl_val (hts e' he').1] at e2
    exact eq_of_toMat_eq (mat_lt _ _) (mat_lt _ _) e2

section Ctx

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {LT LC LI TL VL NL : ℕ} {x : ℕ → G}
  {φ : M →* G}

theorem sctx_of_chk (hC : MCtx M LT LC LI TL VL NL x φ)
    {RR : ℕ → ℕ} {NR : ℕ} (hrels : ∀ r < NR, rval x (RR r) = 1)
    (hnorm : CFSG.KC.relsNorm RR NR = true)
    (hxi : ∀ c < NL, isN TL VL NL c = true → x (byte LI c) = (x c)⁻¹)
    {HB GB TB OB FA : ℕ → ℕ} {Ch Cg Ct : List ℕ}
    {nH nT NO osh owd om NB sel I0 shA wdA NFA W Wi USQ h : ℕ}
    (himp : ImpSem φ x TL FA shA wdA NFA)
    (hhdr : runHdr HB FA LT TL VL NL shA wdA NFA Ch 1 = nH + 1)
    (hgom : runGom HB GB OB osh owd om NB sel I0 nH Cg 1 = NO + 1)
    (hT : runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA Ct 1 =
      nT + 1)
    (hu : usqOK RR LT LI TL VL NL NR USQ W Wi h = true) :
    SCtx M φ x HB GB TB LT LC LI TL VL NL NO nT W Wi := by
  have hg := gom_mem hC hrels hnorm himp hhdr hgom
  have hs := psi_sem hC hrels hnorm himp hhdr hT
  have hq := usq_sem hC hrels hnorm hxi hu
  exact ⟨hC, fun j hj => ⟨(hg j hj).1, (hg j hj).2.1, (hg j hj).2.2.1⟩, hs,
    ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩⟩

theorem psi_hyp {HB TB OB RR FA : ℕ → ℕ} {Ct : List ℕ}
    {LT' TL' VL' NL' NR nH nT osh owd om NB sel I0 shA wdA NFA : ℕ}
    (hts : ∀ e < nT, (x TL')⁻¹ * rc φ (tSig HB TB e) * x TL' = rc φ (tPsi HB TB e))
    (hT : runT HB TB OB RR FA LT' TL' VL' NL' NR nH nT osh owd om NB sel I0 shA wdA NFA Ct 1 =
      nT + 1) :
    ∀ e < nT, ∃ e' < nT, (x TL')⁻¹ * φ (mEl M (tSig HB TB e)) * x TL' =
      φ (mEl M (tSig HB TB e')) := by
  intro e he
  obtain ⟨ep, hep, hψ⟩ := tab_ep hT e he
  refine ⟨ep, hep, ?_⟩
  have h := hts e he
  rw [hψ] at h
  exact h

end Ctx

section Cover

variable {M : Subgroup Mat24ˣ} {G : Type*} [Group G] {φ : M →* G} {HB GB FB OB : ℕ → ℕ}
  {ND NO NF sh wd osh owd om NB sel AL : ℕ} {el : Bool} {N : Subgroup G} {u : G} {w : ℕ → G}

theorem cover_of (hsel : DceS.selOK NB sel = true)
    (hom : om = Nat.sub (Nat.shiftLeft 1 (Nat.mul 24 NB)) 1)
    (hrow : ∀ j < NO, NB = 1 ∨ rowsOK NB (pt OB osh owd om j) = true)
    (hfacts : ∀ i < NF, FOK N el φ HB GB u w ND NO (rec FB sh wd i))
    (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO) {Cs : List ℕ}
    (hcov : DceS.runCover FB OB sh wd osh owd om NB sel NF NO AL Cs 1 = 1 + ND * 2 ^ 20) :
    ∀ D ∈ (Finset.range ND).filter (fun D => AL.testBit D = true), ∀ j < NO,
      (∃ D' ∈ (Finset.range ND).filter (fun D => AL.testBit D = true), ∃ π : M,
        w D * ((φ (mEl M (gm HB GB j)))⁻¹ * u * φ (mEl M (gm HB GB j))) * (w D' * φ π)⁻¹ ∈ N) ∨
      (∃ D' ∈ (Finset.range ND).filter (fun D => AL.testBit D = true), ∃ j' < NO, ∃ π : M,
        actP (ptS NB (pt OB osh owd om j)) (π : Mat24ˣ) = ptS NB (pt OB osh owd om j') ∧
        w D' * ((φ (mEl M (gm HB GB j')))⁻¹ * u * φ (mEl M (gm HB GB j'))) *
          (w D * φ π)⁻¹ ∈ N) := by
  intro D hD j hj
  rw [Finset.mem_filter, Finset.mem_range] at hD
  obtain ⟨x, tau, hs⟩ := runCover_spec hNO hNO0 hcov D hD.1 hD.2 j hj
  obtain ⟨hlt, hcase⟩ := slotOK_spec hs
  obtain ⟨hR, hPi, -, ν, hν, -, hFM⟩ := hfacts (x >>> 1) hlt
  unfold FMeq rc at hFM
  rcases hcase with ⟨hD', hJ, hal⟩ | ⟨hD', hJ0, hal, hact⟩
  · refine Or.inl ⟨rDp (rec FB sh wd (x >>> 1)), ?_, mEl M (rPi (rec FB sh wd (x >>> 1))), ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hR.dp, hal⟩
    · rw [hD', hJ] at hFM
      have e : uv φ HB GB u (j + 1) =
          (φ (mEl M (gm HB GB j)))⁻¹ * u * φ (mEl M (gm HB GB j)) := by
        simp [uv, rc]
      rw [e] at hFM
      have : w D * ((φ (mEl M (gm HB GB j)))⁻¹ * u * φ (mEl M (gm HB GB j))) *
          (w (rDp (rec FB sh wd (x >>> 1))) *
            φ (mEl M (rPi (rec FB sh wd (x >>> 1)))))⁻¹ = ν := by
        rw [hFM]
        group
      rw [this]
      exact hν
  · have hJle := hR.j
    refine Or.inr ⟨rD (rec FB sh wd (x >>> 1)), ?_, rJ (rec FB sh wd (x >>> 1)) - 1, by omega,
      mEl M (rPi (rec FB sh wd (x >>> 1))), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hR.d, hal⟩
    · exact actOK_sound hsel (hrow _ (by omega)) (pt_lt hom j) hact _ (mEl_val hPi)
    · rw [hD'] at hFM
      have e : uv φ HB GB u (rJ (rec FB sh wd (x >>> 1))) =
          (φ (mEl M (gm HB GB (rJ (rec FB sh wd (x >>> 1)) - 1))))⁻¹ * u *
            φ (mEl M (gm HB GB (rJ (rec FB sh wd (x >>> 1)) - 1))) := by
        simp [uv, rc, Nat.pos_iff_ne_zero.1 hJ0]
      rw [e] at hFM
      have : w (rD (rec FB sh wd (x >>> 1))) *
          ((φ (mEl M (gm HB GB (rJ (rec FB sh wd (x >>> 1)) - 1))))⁻¹ * u *
            φ (mEl M (gm HB GB (rJ (rec FB sh wd (x >>> 1)) - 1)))) *
          (w D * φ (mEl M (rPi (rec FB sh wd (x >>> 1)))))⁻¹ = ν := by
        rw [hFM]
        group
      rw [this]
      exact hν

end Cover

end CFSG.KC.Th.Spec.Dce

end
