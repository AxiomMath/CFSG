module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShBar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssembly
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Reduce
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift1
public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop61
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.AFamily
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.LinearCovers
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1115
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTriv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

abbrev T158Q (X : Type) [Group X] (p : ℕ) : Type :=
  ↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X)

noncomputable def t158xbar (p : ℕ) (x : X) : T158Q X p :=
  QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X)) ⟨x, Subgroup.mem_top x⟩

section PreSetup

private structure BarTransport {p : ℕ} (K B L₁ L₂ : Subgroup X) (x₁ x₂ : X) : Prop where
  KbComp : GLAPComponent p ⊤ (barX p ⊤ K)
  KbQs : CFSG.Open.IsQuasisimple ↥(barX p ⊤ K)
  KbCore : GLAPPrimeCore p ↥(barX p ⊤ K) = ⊥
  chev2 : IsChevSimple 2 (PSimple p (barX p ⊤ K))
  BbElem : IsElemAbelian p (barX p ⊤ B)
  Bnorm : barX p ⊤ B ≤ Subgroup.normalizer (barX p ⊤ K : Set (T158Q X p))
  d_mem : t158xbar p x₁ ∈ barX p ⊤ B
  b_mem : t158xbar p x₂ ∈ barX p ⊤ B
  d_pow : t158xbar p x₁ ^ p = 1
  b_pow : t158xbar p x₂ ^ p = 1
  d_ne : t158xbar p x₁ ≠ 1
  L1comp : GLAPComponent p (barX p ⊤ K ⊓
      Subgroup.centralizer ({t158xbar p x₁} : Set (T158Q X p))) (barX p ⊤ L₁)
  L2comp : GLAPComponent p (barX p ⊤ K ⊓
      Subgroup.centralizer ({t158xbar p x₂} : Set (T158Q X p))) (barX p ⊤ L₂)
  fgd : FGOn p (t158xbar p x₁) (barX p ⊤ L₂)
  fgb : FGOn p (t158xbar p x₂) (barX p ⊤ L₁)
  chevJ : IsChevSimple 2 (PSimple p (barX p ⊤ L₁))
  idiag : InnDiagOn p (Subgroup.zpowers (t158xbar p x₁) ⊔
      Subgroup.zpowers (t158xbar p x₂)) (barX p ⊤ K)
  HW : (Subgroup.zpowers (t158xbar p x₁) ⊔ Subgroup.zpowers (t158xbar p x₂)) ⊓
      (barX p ⊤ B ⊓ Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p))) = ⊥

private theorem barTransport_data {p : ℕ} {K B L₁ L₂ : Subgroup X} {x₁ x₂ : X}
    (hh : T158Hyp p K B x₁ x₂ L₁ L₂)
    (hBnorm : B ≤ Subgroup.normalizer (K : Set X))
    (hinn : InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K)
    (hcK : IsChevSimple 2 (PSimple p K)) :
    BarTransport (p := p) K B L₁ L₂ x₁ x₂ := by
  classical
  have hp : p.Prime := hh.prime
  have hp2 : p ≠ 2 := hh.odd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ :=
    t158m_unpack hh
  have hx1p : x₁ ^ p = 1 := hBel.2 x₁ hx1B
  have hx2p : x₂ ^ p = 1 := hBel.2 x₂ hx2B
  have hx1N : x₁ ∈ Subgroup.normalizer (K : Set X) := (t158m_normalizer hh).1
  have hx2N : x₂ ∈ Subgroup.normalizer (K : Set X) := (t158m_normalizer hh).2
  have hx1N2 : x₁ ∈ Subgroup.normalizer (L₂ : Set X) := t158m_fgOn_normalizer hn12
  have hx2N1 : x₂ ∈ Subgroup.normalizer (L₁ : Set X) := t158m_fgOn_normalizer hn21
  let π : ↥(⊤ : Subgroup X) →* T158Q X p := pQuotHom p ⊤
  have hNker : ¬ p ∣ Nat.card ↥π.ker :=
    CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom hp ⊤
  have hx1p' : (⟨x₁, Subgroup.mem_top x₁⟩ : ↥(⊤ : Subgroup X)) ^ p = 1 :=
    Subtype.ext (by simpa using hx1p)
  have hx2p' : (⟨x₂, Subgroup.mem_top x₂⟩ : ↥(⊤ : Subgroup X)) ^ p = 1 :=
    Subtype.ext (by simpa using hx2p)
  have hKbComp : GLAPComponent p ⊤ (barX p ⊤ K) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.glaPComponent_barX_top hp hK
  have hKbQs : CFSG.Open.IsQuasisimple ↥(barX p ⊤ K) := hK.2.2.1.2.2
  have hKbCore : GLAPPrimeCore p ↥(barX p ⊤ K) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.glaPPrimeCore_barX_eq_bot hp hK.2.1
  have hcKb : IsChevSimple 2 (PSimple p (barX p ⊤ K)) := by
    change IsChevSimple 2 (PSimple p ((K.subgroupOf ⊤).map π))
    exact chev_forth hp (le_top : K ≤ ⊤) (π := π) hNker hcK
  have hBbElem : IsElemAbelian p (barX p ⊤ B) := isElemAbelian_barX hBel
  have hBnormQ : barX p ⊤ B ≤ Subgroup.normalizer (barX p ⊤ K : Set (T158Q X p)) :=
    barX_le_normalizer hBnorm
  have hd_mem_Bb : t158xbar p x₁ ∈ barX p ⊤ B := by
    simpa [t158xbar] using
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1115.mk_mem_barX
        (p := p) (X := ⊤) (S := B) (x := x₁) (Subgroup.mem_top x₁) hx1B
  have hb_mem_Bb : t158xbar p x₂ ∈ barX p ⊤ B := by
    simpa [t158xbar] using
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1115.mk_mem_barX
        (p := p) (X := ⊤) (S := B) (x := x₂) (Subgroup.mem_top x₂) hx2B
  have hdp : t158xbar p x₁ ^ p = 1 := by
    have h : π ((⟨x₁, Subgroup.mem_top x₁⟩ : ↥(⊤ : Subgroup X)) ^ p) = 1 := by
      rw [hx1p', map_one]
    rw [map_pow] at h
    change (π ⟨x₁, Subgroup.mem_top x₁⟩) ^ p = 1
    exact h
  have hbp : t158xbar p x₂ ^ p = 1 := by
    have h : π ((⟨x₂, Subgroup.mem_top x₂⟩ : ↥(⊤ : Subgroup X)) ^ p) = 1 := by
      rw [hx2p', map_one]
    rw [map_pow] at h
    change (π ⟨x₂, Subgroup.mem_top x₂⟩) ^ p = 1
    exact h
  have hd1 : t158xbar p x₁ ≠ 1 := by
    intro hd
    have hc : (⟨x₁, Subgroup.mem_top x₁⟩ : ↥(⊤ : Subgroup X)) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      change π ⟨x₁, Subgroup.mem_top x₁⟩ = 1
      exact hd
    have hone : (⟨x₁, Subgroup.mem_top x₁⟩ : ↥(⊤ : Subgroup X)) = 1 :=
      CFSG.LieType.CentralExt.eq_one_of_mem_ker hNker hc (n := 1) (by simpa using hx1p')
    exact hx1 (by simpa using congrArg Subtype.val hone)
  have hL1bComp : GLAPComponent p
      (barX p ⊤ K ⊓ Subgroup.centralizer
        ({t158xbar p x₁} : Set (T158Q X p))) (barX p ⊤ L₁) := by
    have h :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop126b.glaPComponent_barX_inf_centralizer
        hp (M := ⊤) (L := K) (K := L₁) (d := x₁)
        (Subgroup.mem_top x₁) (le_top : K ≤ ⊤) hx1N
        (isPGroup_zpowers_of_pow_eq_one hx1p) hL1
    simpa [barX, t158xbar, pQuotHom] using h
  have hL2bComp : GLAPComponent p
      (barX p ⊤ K ⊓ Subgroup.centralizer
        ({t158xbar p x₂} : Set (T158Q X p))) (barX p ⊤ L₂) := by
    have h :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop126b.glaPComponent_barX_inf_centralizer
        hp (M := ⊤) (L := K) (K := L₂) (d := x₂)
        (Subgroup.mem_top x₂) (le_top : K ≤ ⊤) hx2N
        (isPGroup_zpowers_of_pow_eq_one hx2p) hL2
    simpa [barX, t158xbar, pQuotHom] using h
  have hfgd : FGOn p (t158xbar p x₁) (barX p ⊤ L₂) := by
    change FGOn p (π ⟨x₁, Subgroup.mem_top x₁⟩) ((L₂.subgroupOf ⊤).map π)
    exact fgOn_forth hp (H := ⊤) (L := L₂) le_top (π := π) hNker
      (Subgroup.mem_top x₁) hx1N2 hn12
  have hfb : FGOn p (t158xbar p x₂) (barX p ⊤ L₁) := by
    change FGOn p (π ⟨x₂, Subgroup.mem_top x₂⟩) ((L₁.subgroupOf ⊤).map π)
    exact fgOn_forth hp (H := ⊤) (L := L₁) le_top (π := π) hNker
      (Subgroup.mem_top x₂) hx2N1 hn21
  have hcL1b : IsChevSimple 2 (PSimple p (barX p ⊤ L₁)) := by
    change IsChevSimple 2 (PSimple p ((L₁.subgroupOf ⊤).map π))
    exact chev_forth hp (le_top : L₁ ≤ ⊤) (π := π) hNker hc1
  have hA' : ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂).subgroupOf ⊤).map π =
      Subgroup.zpowers (t158xbar p x₁) ⊔ Subgroup.zpowers (t158xbar p x₂) := by
    rw [Subgroup.subgroupOf_sup (Subgroup.zpowers_le.2 (Subgroup.mem_top x₁))
      (Subgroup.zpowers_le.2 (Subgroup.mem_top x₂)), Subgroup.map_sup]
    have hsup := CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup
      (p := p) (X := ⊤) (A := Subgroup.zpowers x₁) (B := Subgroup.zpowers x₂)
      (Subgroup.zpowers_le.2 (Subgroup.mem_top x₁))
      (Subgroup.zpowers_le.2 (Subgroup.mem_top x₂))
    rw [show ((Subgroup.zpowers x₁).subgroupOf ⊤).map π =
        barX p ⊤ (Subgroup.zpowers x₁) from rfl,
      show ((Subgroup.zpowers x₂).subgroupOf ⊤).map π =
        barX p ⊤ (Subgroup.zpowers x₂) from rfl,
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129b.barX_zpowers
        (p := p) (N := ⊤) (a := x₁) (Subgroup.mem_top x₁),
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129b.barX_zpowers
        (p := p) (N := ⊤) (a := x₂) (Subgroup.mem_top x₂)]
    rfl
  have hidiagQ : InnDiagOn p (Subgroup.zpowers (t158xbar p x₁) ⊔
      Subgroup.zpowers (t158xbar p x₂)) (barX p ⊤ K) := by
    have h := innDiagOn_map_subgroupOf hp (H := ⊤) (L := K)
      (A := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) le_top hNker hinn
    rw [hA', show (K.subgroupOf ⊤).map π = barX p ⊤ K from rfl] at h
    exact h
  have hHW : (Subgroup.zpowers (t158xbar p x₁) ⊔ Subgroup.zpowers (t158xbar p x₂)) ⊓
      (barX p ⊤ B ⊓ Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p))) = ⊥ :=
    zpowers_sup_inf_centralizer_eq_bot hp hp2 hL1bComp hL2bComp hBbElem hd_mem_Bb hb_mem_Bb
      hdp hbp hfgd hfb
  exact
    { KbComp := hKbComp
      KbQs := hKbQs
      KbCore := hKbCore
      chev2 := hcKb
      BbElem := hBbElem
      Bnorm := hBnormQ
      d_mem := hd_mem_Bb
      b_mem := hb_mem_Bb
      d_pow := hdp
      b_pow := hbp
      d_ne := hd1
      L1comp := hL1bComp
      L2comp := hL2bComp
      fgd := hfgd
      fgb := hfb
      chevJ := hcL1b
      idiag := hidiagQ
      HW := hHW }

theorem exists_preSetup {p : ℕ} {K B L₁ L₂ : Subgroup X} {x₁ x₂ : X}
    (hN : T158Norm) (hh : T158Hyp p K B x₁ x₂ L₁ L₂)
    (hinn : InnDiagOn p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K)
    (hcat : catalogIs (PSimple p K) (t158Shape p))
    (hcK : IsChevSimple 2 (PSimple p K)) :
    ∃ A W : Subgroup (T158Q X p),
      PreSetup p (barX p ⊤ K) (barX p ⊤ L₁) A (t158xbar p x₁) (t158xbar p x₂) ∧
        W = barX p ⊤ B ⊓ Subgroup.centralizer
          (barX p ⊤ K : Set (T158Q X p)) ∧
        A ≤ barX p ⊤ B ∧ A ⊓ W = ⊥ ∧ A ⊔ W = barX p ⊤ B ∧
        Nat.card ↥A = (B ⊓ centModSubgroup p K).relIndex B := by
  have hp : p.Prime := hh.prime
  have hp2 : p ≠ 2 := hh.odd
  have hBnorm : B ≤ Subgroup.normalizer (K : Set X) :=
    hN X p K B x₁ x₂ L₁ L₂ hcat hh hinn
  obtain ⟨hK, hBel, -, -, -, -, -, -, -, -, -, -⟩ := t158m_unpack hh
  let W : Subgroup (T158Q X p) :=
    barX p ⊤ B ⊓ Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p))
  have hT := barTransport_data hh hBnorm hinn hcK
  obtain ⟨A, hAB, hHA, hAW, hAsup⟩ :=
    exists_isCompl_of_isElemAbelian hp hT.BbElem inf_le_left
      (sup_le (Subgroup.zpowers_le.2 hT.d_mem) (Subgroup.zpowers_le.2 hT.b_mem)) hT.HW
  have hfaith : A ⊓ Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨hzA, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzW : z ∈ W := ⟨hAB hzA, hzC⟩
    have hmem : z ∈ A ⊓ W := ⟨hzA, hzW⟩
    rw [hAW] at hmem
    simpa using hmem
  have hcardB : Nat.card ↥B =
      Nat.card ↥A * Nat.card ↥(B ⊓ centModSubgroup p K) :=
    card_eq_card_mul_inf_centModSubgroup (C := ⊤) hp hK le_top hBel hBnorm
      (W := W) (A := A) rfl hAB hAW hAsup
  have hrel := Subgroup.relIndex_mul_card
    (H := B ⊓ centModSubgroup p K) (K := B)
  rw [inf_eq_left.mpr inf_le_left] at hrel
  rw [hcardB] at hrel
  have hArel : Nat.card ↥A = (B ⊓ centModSubgroup p K).relIndex B :=
    (Nat.mul_right_cancel (Nat.card_pos (α := ↥(B ⊓ centModSubgroup p K))) hrel).symm
  refine ⟨A, W, ?_, rfl, hAB, hAW, hAsup, hArel⟩
  exact
    { prime := hp
      odd := hp2
      qs := hT.KbQs
      core := hT.KbCore
      chev2 := hT.chev2
      elem := isElemAbelian_mono hT.BbElem hAB
      norm := hAB.trans hT.Bnorm
      idiag₂ := (innDiagOn_iff hT.KbComp hT.KbQs).2 hT.idiag
      faithful := hfaith
      d_mem := hHA (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      d_ne := hT.d_ne
      b_mem := hHA (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      pcomp := hT.L1comp
      chevJ := hT.chevJ
      b_norm := t158m_fgOn_normalizer hT.fgb
      fg := hT.fgb }

end PreSetup

section LowerBound

theorem card_pow_le_card_A_of_lower {Q : Type} [Group Q] [Finite Q] {p N k : ℕ}
    {L B A W E U : Subgroup Q} (hp : p.Prime)
    (hB : IsElemAbelian p B) (hA : A ≤ B) (hW : W ≤ B)
    (hAW : A ⊓ W = ⊥) (hAsup : A ⊔ W = B)
    (hWL : W ≤ Subgroup.centralizer (L : Set Q))
    (hEL : E ≤ L) (hUL : U ≤ L) (hE : IsElemAbelian p E)
    (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set Q))
    (hlow : p ^ (N - k) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Q)) ≤ Nat.card ↥E)
    (hBrank : p ^ GLATwoLocalRank p Q ≤ Nat.card ↥B) :
    p ^ (N - k) ≤ Nat.card ↥A := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hWL hy) x (hEL hx)
  have hEWel : IsElemAbelian p (E ⊔ W) :=
    IsElemAbelian.sup_of_commute hE (isElemAbelian_mono hB hW) hcomm
  have hWCU : W ≤ Subgroup.centralizer (U : Set Q) :=
    hWL.trans (Subgroup.centralizer_le hUL)
  have hEWU : E ⊔ W ≤ Subgroup.normalizer (U : Set Q) :=
    sup_le hEU (hWCU.trans (Subgroup.centralizer_le_normalizer (U : Set Q)))
  have hcard_sup_le : Nat.card ↥(E ⊔ W) ≤ p ^ GLATwoLocalRank p Q :=
    card_le_pow_glaTwoLocalRank hp hEWel hU1 hU2 hEWU
  have hcard_le_B : Nat.card ↥(E ⊔ W) ≤ Nat.card ↥B := hcard_sup_le.trans hBrank
  have hprod : Nat.card ↥(E ⊔ W) * Nat.card ↥(E ⊓ W) =
      Nat.card ↥E * Nat.card ↥W :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E W hcomm).1
  have hinf_le : Nat.card ↥(E ⊓ W) ≤
      Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Q)) :=
    Subgroup.card_le_of_le (inf_le_inf_left E hWL)
  have h1 : p ^ (N - k) * Nat.card ↥(E ⊓ W) ≤ Nat.card ↥E :=
    (Nat.mul_le_mul_left _ hinf_le).trans hlow
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  have h2 : p ^ (N - k) * Nat.card ↥W ≤ Nat.card ↥(E ⊔ W) := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := ↥(E ⊓ W)))
    calc p ^ (N - k) * Nat.card ↥W * Nat.card ↥(E ⊓ W)
        = (p ^ (N - k) * Nat.card ↥(E ⊓ W)) * Nat.card ↥W := by ring
      _ ≤ Nat.card ↥E * Nat.card ↥W := Nat.mul_le_mul_right _ h1
      _ = Nat.card ↥(E ⊔ W) * Nat.card ↥(E ⊓ W) := hprod.symm
  have h4 : p ^ (N - k) * Nat.card ↥W ≤ Nat.card ↥B := h2.trans hcard_le_B
  have hBcard : Nat.card ↥B = Nat.card ↥A * Nat.card ↥W := by
    rw [← hAsup]
    exact CFSG.card_sup_eq_mul_of_commute A W
      (fun a ha w hw => isElemAbelian_commute hB (hA ha) (hW hw)) hAW
  rw [hBcard] at h4
  exact Nat.le_of_mul_le_mul_right h4 hWpos

end LowerBound

theorem not_catalogIs_isL2n_one (S : Type) [Group S] :
    ¬ catalogIs S (S10.isL2n 1) := by
  rintro ⟨i, hi, -⟩
  cases i with
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | A r q =>
      cases r with
      | zero => simp [S10.isL2n] at hi
      | succ r1 =>
        cases r1 with
        | zero =>
          simp only [S10.isL2n] at hi
          have h4 := (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.valid_lie_A_range
            (r := 1) hv).2 rfl
          have hcard : q.card = 2 := by
            rw [TauCeti.PrimePower.card_def, hi.1, hi.2]
            norm_num
          omega
        | succ r2 => simp [S10.isL2n] at hi
    | _ => simp [S10.isL2n] at hi
  | cyclic _ _ => simp [S10.isL2n] at hi
  | alternating m _ => simp [S10.isL2n] at hi
  | sporadic _ => simp [S10.isL2n] at hi

theorem not_catalogIs_isU3n_one (S : Type) [Group S] :
    ¬ catalogIs S (S10.isU3n 1) := by
  rintro ⟨i, hi, -⟩
  cases i with
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | twistedA r q =>
      cases r with
      | zero => simp only [S10.isU3n, onLie] at hi
      | succ r1 =>
        cases r1 with
        | zero => simp only [S10.isU3n, onLie] at hi
        | succ r2 =>
          cases r2 with
          | zero =>
            simp only [S10.isU3n, onLie] at hi
            have h3 := CFSG.LocalAnalysis.GLTheoremA.FullCover.three_le_card_of_valid_twistedA_two
              (q := q) hv
            have hcard : q.card = 2 := by
              rw [TauCeti.PrimePower.card_def, hi.1, hi.2]
              norm_num
            omega
          | succ r3 => simp only [S10.isU3n, onLie] at hi
    | _ => simp only [S10.isU3n, onLie] at hi
  | cyclic _ _ => simp only [S10.isU3n, onLie] at hi
  | alternating m _ => simp only [S10.isU3n, onLie] at hi
  | sporadic _ => simp only [S10.isU3n, onLie] at hi

theorem barX_rank_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup X}
    (hB : IsElemAbelian p B)
    (hrk : p ^ GLATwoLocalRank p (⊤ : Subgroup X) ≤ Nat.card ↥B) :
    p ^ GLATwoLocalRank p (T158Q X p) ≤ Nat.card ↥(barX p ⊤ B) ∧
      Nat.card ↥(barX p ⊤ B) = Nat.card ↥B := by
  have hBp : IsPGroup p B :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isPGroup_of_isElemAbelian' hB
  have hcard : Nat.card ↥(barX p ⊤ B) = Nat.card ↥B :=
    card_barX_of_isPGroup hp hBp le_top
  refine ⟨?_, hcard⟩
  rw [hcard]
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥(⊤ : Subgroup X)) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.ker_pQuotHom]
    exact CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom hp ⊤
  have hle := glaTwoLocalRank_quotient_le hp hp2
    (GLAPPrimeCore p ↥(⊤ : Subgroup X)) hN
  exact (Nat.pow_le_pow_right hp.pos hle).trans hrk

section MainTheorems

theorem t158Hyp_rank {p : ℕ} {K B L₁ L₂ : Subgroup X} {x₁ x₂ : X}
    (hh : T158Hyp p K B x₁ x₂ L₁ L₂) :
    p ^ GLATwoLocalRank p (⊤ : Subgroup X) ≤ Nat.card ↥B := by
  obtain ⟨⟨-, -, -, -, hrk, -, -, -, -, -, -, -, -⟩, -, -⟩ := hh.hyp
  exact hrk

theorem t158ShapeLieOn_A (hN : T158Norm) (hS : T158SetupLU) (hLU : LinUniBound) :
    T158ShapeLieOn t158ShapeA := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hcat hh hinn
  obtain ⟨i, hi, e⟩ := hcat
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ :=
    t158m_unpack hh
  cases i with
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | A n q =>
      simp only [t158ShapeA, onLie] at hi
      have hp : p.Prime := hh.prime
      have hp2 : p ≠ 2 := hh.odd
      have hp3 : 3 ≤ p := by
        have h2 : 2 ≤ p := hp.two_le
        omega
      haveI : Fact p.Prime := ⟨hp⟩
      have hcatFull : catalogIs (PSimple p K) (t158Shape p) :=
        ⟨.lie ⟨.A n q, hv⟩, Or.inl hi, e⟩
      have hBnorm : B ≤ Subgroup.normalizer (K : Set X) :=
        hN X p K B x₁ x₂ L₁ L₂ hcatFull hh hinn
      have hcK : IsChevSimple 2 (PSimple p K) := by
        refine Or.inl ⟨.lie ⟨.A n q, hv⟩, ?_, e⟩
        simp only [onLie]
        rw [TauCeti.LieTypeIndex.characteristic_A]
        exact hi.1
      obtain ⟨A, W, hPre, hWdef, hAB, hAW, hAsup, -⟩ := exists_preSetup hN hh hinn hcatFull hcK
      let N := n + 1
      have hNtop : ¬ p ∣ Nat.card (pQuotHom p (⊤ : Subgroup X)).ker :=
        CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom hp ⊤
      have hcatLU : catalogIs (PSimple p (barX p ⊤ K))
          (onLie fun i => ∃ q, (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧
            I171.I171LieShape p i) := by
        change catalogIs (PSimple p ((K.subgroupOf ⊤).map (pQuotHom p ⊤))) _
        exact catalog_forth hp le_top hNtop
          ⟨.lie ⟨.A n q, hv⟩, ⟨q, Or.inl (by
            show (⟨.A n q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .A (N - 1) q
            rw [show N - 1 = n from by omega]), hi⟩, e⟩
      obtain ⟨hSetup, h2p⟩ := hS (T158Q X p) p (barX p ⊤ K) (barX p ⊤ L₁) A
        (t158xbar p x₁) (t158xbar p x₂) N hPre hcatLU
      have hUpper : Nat.card ↥A ≤ p ^ (1 + N / p) :=
        hLU (T158Q X p) p (barX p ⊤ K) (barX p ⊤ L₁) A (t158xbar p x₁) (t158xbar p x₂) N
          hSetup hcatLU
      have hN3 : 3 ≤ N := by omega
      have hcatLin : catalogIs (PSimple p (barX p ⊤ K))
          (onLie fun i => ∃ q, i = .A (N - 1) q ∧ q.p = 2 ∧ p ∣ q.card - 1) := by
        change catalogIs (PSimple p ((K.subgroupOf ⊤).map (pQuotHom p ⊤))) _
        exact catalog_forth hp le_top hNtop
          ⟨.lie ⟨.A n q, hv⟩, ⟨q, (by
            show (⟨.A n q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .A (N - 1) q
            rw [show N - 1 = n from by omega]), hi.1,
            (Nat.dvd_gcd_iff.mp hi.2).2⟩, e⟩
      obtain ⟨E, U, hEL, hUL, hE, hU2, hU1, hEU, hlow⟩ :=
        lowerLin_holds (T158Q X p) (barX p ⊤ K) p N hp hp2 hN3 hPre.qs hcatLin
      have hBbElem : IsElemAbelian p (barX p ⊤ B) := isElemAbelian_barX hBel
      obtain ⟨hBrank', -⟩ := barX_rank_bound (B := B) hp hp2 hBel (t158Hyp_rank hh)
      have hW : W ≤ Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p)) := by
        rw [hWdef]
        exact inf_le_right
      have hWB : W ≤ barX p ⊤ B := by
        rw [hWdef]
        exact inf_le_left
      have hLower : p ^ (N - 2) ≤ Nat.card ↥A :=
        card_pow_le_card_A_of_lower (Q := T158Q X p) (p := p) (N := N) (k := 2)
          (L := barX p ⊤ K) (B := barX p ⊤ B) (A := A) (W := W) (E := E) (U := U)
          hp hBbElem hAB hWB hAW hAsup hW hEL hUL hE hU2 hU1 hEU hlow hBrank'
      have hle : N - 2 ≤ 1 + N / p := by
        by_contra hcon
        have hlt : 1 + N / p < N - 2 := by omega
        have hpow : p ^ (1 + N / p) < p ^ (N - 2) :=
          (Nat.pow_lt_pow_iff_right hp.one_lt).2 hlt
        omega
      exact False.elim (lin_case_false hp3 h2p hle)
    | _ => simp [t158ShapeA, onLie] at hi
  | cyclic _ _ => simp [t158ShapeA, onLie] at hi
  | alternating _ _ => simp [t158ShapeA, onLie] at hi
  | sporadic _ => simp [t158ShapeA, onLie] at hi

end MainTheorems

section E6Certificates

theorem t158ShapeLieOn_E6 (hN : T158Norm) (hS : T158SetupE6)
    (hE : T171Sh.E6Bound false) : T158ShapeLieOn t158ShapeE6 := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hcat hh hinn
  obtain ⟨i, hi, e⟩ := hcat
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ :=
    t158m_unpack hh
  cases i with
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | E6 q =>
      simp only [t158ShapeE6, onLie] at hi
      obtain rfl : p = 3 := hi.1
      have hp : (3 : ℕ).Prime := Nat.prime_three
      have hNtop : ¬ 3 ∣ Nat.card (pQuotHom 3 (⊤ : Subgroup X)).ker :=
        CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom hp ⊤
      have hcK : IsChevSimple 2 (PSimple 3 K) := by
        refine Or.inl ⟨.lie ⟨.E6 q, hv⟩, ?_, e⟩
        simp only [onLie]
        rw [TauCeti.LieTypeIndex.characteristic_E6]
        exact hi.2.1
      have hcatFull : catalogIs (PSimple 3 K) (t158Shape 3) :=
        ⟨.lie ⟨.E6 q, hv⟩, Or.inr (Or.inr (Or.inl hi)), e⟩
      have hBnorm : B ≤ Subgroup.normalizer (K : Set X) :=
        hN X 3 K B x₁ x₂ L₁ L₂ hcatFull hh hinn
      obtain ⟨A, W, hPre, hWdef, hAB, hAW, hAsup, -⟩ := exists_preSetup hN hh hinn hcatFull hcK
      have hcatLU : catalogIs (PSimple 3 (barX 3 ⊤ K))
          (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧
            (i = .E6 q ∨ i = .twistedE6 q)) := by
        change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
        exact catalog_forth Nat.prime_three le_top hNtop
          ⟨.lie ⟨.E6 q, hv⟩, ⟨q, hi, Or.inl rfl⟩, e⟩
      have hSetup := hS (T158Q X 3) (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
        (t158xbar 3 x₁) (t158xbar 3 x₂) hPre hcatLU
      have hcatLUe6 : catalogIs (PSimple 3 (barX 3 ⊤ K))
          (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧
            (if false = true then i = .twistedE6 q else i = .E6 q)) := by
        change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
        exact catalog_forth Nat.prime_three le_top hNtop
          ⟨.lie ⟨.E6 q, hv⟩, ⟨q, hi, by simp⟩, e⟩
      have hUpper : Nat.card ↥A ≤ 3 ^ 4 :=
        hE (T158Q X 3) (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
          (t158xbar 3 x₁) (t158xbar 3 x₂) hSetup hcatLUe6
      have hcatE6 : catalogIs (PSimple 3 (barX 3 ⊤ K))
          (onLie fun i => ∃ q, i = .E6 q ∧ q.p = 2 ∧ 3 ∣ q.card - 1) := by
        change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
        exact catalog_forth Nat.prime_three le_top hNtop
          ⟨.lie ⟨.E6 q, hv⟩, ⟨q, rfl, hi.2.1, hi.2.2⟩, e⟩
      obtain ⟨E, U, hEL, hUL, hE, hU2, hU1, hEU, hlow⟩ :=
        lowerE6_holds (T158Q X 3) (barX 3 ⊤ K) hPre.qs hcatE6
      have hBbElem : IsElemAbelian 3 (barX 3 ⊤ B) := isElemAbelian_barX hBel
      obtain ⟨hBrank', -⟩ := barX_rank_bound (B := B) hp (by norm_num) hBel (t158Hyp_rank hh)
      have hW : W ≤ Subgroup.centralizer (barX 3 ⊤ K : Set (T158Q X 3)) := by
        rw [hWdef]
        exact inf_le_right
      have hWB : W ≤ barX 3 ⊤ B := by
        rw [hWdef]
        exact inf_le_left
      have hLower : 3 ^ 5 ≤ Nat.card ↥A := by
        have h := card_pow_le_card_A_of_lower (Q := T158Q X 3) (p := 3) (N := 7) (k := 2)
          (L := barX 3 ⊤ K) (B := barX 3 ⊤ B) (A := A) (W := W) (E := E) (U := U)
          hp hBbElem hAB hWB hAW hAsup hW hEL hUL hE hU2 hU1 hEU hlow hBrank'
        simpa using h
      have hcontra : (3 : ℕ) ^ 5 ≤ 3 ^ 4 := hLower.trans hUpper
      norm_num at hcontra
    | _ => simp [t158ShapeE6, onLie] at hi
  | cyclic _ _ => simp [t158ShapeE6, onLie] at hi
  | alternating _ _ => simp [t158ShapeE6, onLie] at hi
  | sporadic _ => simp [t158ShapeE6, onLie] at hi

end E6Certificates

private theorem t158TwA_setup {p n : ℕ} {K B L₁ L₂ : Subgroup X} {x₁ x₂ : X}
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.twistedA n q).Valid}
    {hi : q.p = 2 ∧ p ∣ Nat.gcd (n + 1) (q.card + 1)}
    {e : Nonempty (PSimple p K ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA n q, hv⟩).Group)}
    {A W : Subgroup (T158Q X p)}
    (hS : T158SetupLU) (hLU : LinUniBound) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 ≤ p)
    (hPre : PreSetup p (barX p ⊤ K) (barX p ⊤ L₁) A
      (t158xbar p x₁) (t158xbar p x₂))
    (hWdef : W = barX p ⊤ B ⊓
      Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p)))
    (hAB : A ≤ barX p ⊤ B) (hAW : A ⊓ W = ⊥) (hAsup : A ⊔ W = barX p ⊤ B)
    (hBel : IsElemAbelian p B)
    (hrk : p ^ GLATwoLocalRank p (⊤ : Subgroup X) ≤ Nat.card ↥B) :
    ∃ N : ℕ, T171Sh.Setup p (barX p ⊤ K) (barX p ⊤ L₁) A
        (t158xbar p x₁) (t158xbar p x₂) ∧
      Nat.card ↥A ≤ p ^ (1 + N / p) ∧ p ^ (N - 3) ≤ Nat.card ↥A ∧
        2 * p ≤ N ∧ 3 ≤ N ∧ N = n + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N := n + 1
  have hNtop : ¬ p ∣ Nat.card (pQuotHom p (⊤ : Subgroup X)).ker :=
    CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom hp ⊤
  have hcatLU : catalogIs (PSimple p (barX p ⊤ K))
      (onLie fun i => ∃ q, (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧
        I171.I171LieShape p i) := by
    change catalogIs (PSimple p ((K.subgroupOf ⊤).map (pQuotHom p ⊤))) _
    exact catalog_forth hp le_top hNtop
      ⟨.lie ⟨.twistedA n q, hv⟩, ⟨q, Or.inr (by
        show (⟨.twistedA n q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .twistedA (N - 1) q
        rw [show N - 1 = n from by omega]), hi⟩, e⟩
  obtain ⟨hSetup, h2p⟩ := hS (T158Q X p) p (barX p ⊤ K) (barX p ⊤ L₁) A
    (t158xbar p x₁) (t158xbar p x₂) N hPre hcatLU
  have hUpper : Nat.card ↥A ≤ p ^ (1 + N / p) :=
    hLU (T158Q X p) p (barX p ⊤ K) (barX p ⊤ L₁) A
      (t158xbar p x₁) (t158xbar p x₂) N hSetup hcatLU
  have hN3 : 3 ≤ N := by omega
  have hcatUni : catalogIs (PSimple p (barX p ⊤ K))
      (onLie fun i => ∃ q, i = .twistedA (N - 1) q ∧ q.p = 2 ∧ p ∣ q.card + 1) := by
    change catalogIs (PSimple p ((K.subgroupOf ⊤).map (pQuotHom p ⊤))) _
    exact catalog_forth hp le_top hNtop
      ⟨.lie ⟨.twistedA n q, hv⟩, ⟨q, (by
        show (⟨.twistedA n q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .twistedA (N - 1) q
        rw [show N - 1 = n from by omega]), hi.1,
        (Nat.dvd_gcd_iff.mp hi.2).2⟩, e⟩
  obtain ⟨E, U, hEL, hUL, hE, hU2, hU1, hEU, hlow⟩ :=
    lowerUni_holds (T158Q X p) (barX p ⊤ K) p N hp hp2 hN3 hPre.qs hcatUni
  have hBbElem : IsElemAbelian p (barX p ⊤ B) := isElemAbelian_barX hBel
  obtain ⟨hBrank', -⟩ := barX_rank_bound (B := B) hp hp2 hBel hrk
  have hW : W ≤ Subgroup.centralizer (barX p ⊤ K : Set (T158Q X p)) := by
    rw [hWdef]
    exact inf_le_right
  have hWB : W ≤ barX p ⊤ B := by
    rw [hWdef]
    exact inf_le_left
  have hLower : p ^ (N - 3) ≤ Nat.card ↥A :=
    card_pow_le_card_A_of_lower (Q := T158Q X p) (p := p) (N := N) (k := 3)
      (L := barX p ⊤ K) (B := barX p ⊤ B) (A := A) (W := W) (E := E) (U := U)
      hp hBbElem hAB hWB hAW hAsup hW hEL hUL hE hU2 hU1 hEU hlow hBrank'
  exact ⟨N, hSetup, hUpper, hLower, h2p, hN3, rfl⟩

private theorem t158TwA_shape_data {K B L₁ : Subgroup X} {x₁ x₂ : X}
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid}
    {hi : q.p = 2 ∧ 3 ∣ q.card + 1}
    {e : Nonempty (PSimple 3 K ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 5 q, hv⟩).Group)}
    {A : Subgroup (T158Q X 3)}
    (hPre : PreSetup 3 (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
      (t158xbar 3 x₁) (t158xbar 3 x₂))
    (hBel : IsElemAbelian 3 B) (hx2B : x₂ ∈ B) (hn21 : FGOn 3 x₂ L₁)
    (hlayer : GLAPLayer 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) ≠ ⊥)
    (hI : T158IdentU6) (hF : T158FixL2) :
    ∃ m : ℕ, Odd m ∧ 1 < m ∧
      catalogIs (PSimple 3 K) (S10.isU6n m) ∧
      catalogIs (PSimple 3 L₁) (S10.isL2n (3 * m)) ∧
      ∃ M : Subgroup X,
        GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) M ∧
          catalogIs (PSimple 3 M) (S10.isL2n m) := by
  let m := q.exponent
  have hcard : q.card = 2 ^ m := by
    rw [TauCeti.PrimePower.card_def, hi.1]
  have h3div : 3 ∣ 2 ^ m + 1 := by
    rw [← hcard]
    exact hi.2
  have hOdd : Odd m :=
    CFSG.RankThree.PartTwo.Census.odd_of_three_dvd_two_pow_add_one h3div
  have hcatK : catalogIs (PSimple 3 K) (S10.isU6n m) :=
    ⟨.lie ⟨.twistedA 5 q, hv⟩, ⟨hi.1, rfl⟩, e⟩
  have hNtop3 : ¬ 3 ∣ Nat.card (pQuotHom 3 (⊤ : Subgroup X)).ker :=
    CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom Nat.prime_three ⊤
  have hcatU6Kb : catalogIs (PSimple 3 (barX 3 ⊤ K)) (S10.isU6n m) := by
    change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
    exact catalog_forth Nat.prime_three le_top hNtop3 hcatK
  have hIdentKb : catalogIs (PSimple 3 (barX 3 ⊤ L₁)) (S10.isL2n (3 * m)) :=
    hI (T158Q X 3) (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
      (t158xbar 3 x₁) (t158xbar 3 x₂) m hPre hcatU6Kb hOdd
  have hcomp : PQuot 3 L₁ ≃* PQuot 3 (barX 3 ⊤ L₁) :=
    CFSG.LocalAnalysis.GLTheoremA.T156.compIso Nat.prime_three
      (Subgroup.map_subgroupOf_eq_of_le (le_top : L₁ ≤ ⊤))
      (pQuotHom 3 ⊤) hNtop3
  have hIdent : catalogIs (PSimple 3 L₁) (S10.isL2n (3 * m)) :=
    (catalogIs_congr (CFSG.LocalAnalysis.GLTheoremA.T156.psimpleIso hcomp)).2 hIdentKb
  obtain ⟨M, hM⟩ := exists_glaPComponent_of_layer_ne_bot hlayer
  have hx2p3 : x₂ ^ 3 = 1 := hBel.2 x₂ hx2B
  have hMcat : catalogIs (PSimple 3 M) (S10.isL2n m) :=
    hF X L₁ x₂ m hx2p3 hn21 hIdent M hM
  have hm_ne_one : m ≠ 1 := by
    intro hm
    exact not_catalogIs_isL2n_one (PSimple 3 M) (by simpa [hm] using hMcat)
  have h1m : 1 < m := by
    rcases hOdd with ⟨k, hk⟩
    omega
  exact ⟨m, hOdd, h1m, hcatK, hIdent, M, hM, hMcat⟩

private theorem t158TwE6_setup {K B L₁ L₂ : Subgroup X} {x₁ x₂ : X}
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid}
    {hi : q.p = 2 ∧ 3 ∣ q.card + 1}
    {e : Nonempty (PSimple 3 K ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩).Group)}
    {A W : Subgroup (T158Q X 3)}
    (hS : T158SetupE6) (hE : E6Bound true) (hL : LowerTwE6)
    (hPre : PreSetup 3 (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
      (t158xbar 3 x₁) (t158xbar 3 x₂))
    (hWdef : W = barX 3 ⊤ B ⊓
      Subgroup.centralizer (barX 3 ⊤ K : Set (T158Q X 3)))
    (hAB : A ≤ barX 3 ⊤ B) (hAW : A ⊓ W = ⊥) (hAsup : A ⊔ W = barX 3 ⊤ B)
    (hBel : IsElemAbelian 3 B)
    (hrk : 3 ^ GLATwoLocalRank 3 (⊤ : Subgroup X) ≤ Nat.card ↥B) :
    T171Sh.Setup 3 (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
        (t158xbar 3 x₁) (t158xbar 3 x₂) ∧
      Nat.card ↥A ≤ 3 ^ 4 ∧ 3 ^ 4 ≤ Nat.card ↥A := by
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  have hNtop : ¬ 3 ∣ Nat.card (pQuotHom 3 (⊤ : Subgroup X)).ker :=
    CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom Nat.prime_three ⊤
  have hcatLU : catalogIs (PSimple 3 (barX 3 ⊤ K))
      (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧
        (i = .E6 q ∨ i = .twistedE6 q)) := by
    change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
    exact catalog_forth Nat.prime_three le_top hNtop
      ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨q, ⟨rfl, hi⟩, Or.inr rfl⟩, e⟩
  have hSetup := hS (T158Q X 3) (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
    (t158xbar 3 x₁) (t158xbar 3 x₂) hPre hcatLU
  have hcatLUe6 : catalogIs (PSimple 3 (barX 3 ⊤ K))
      (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧
        (if true = true then i = .twistedE6 q else i = .E6 q)) := by
    change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
    exact catalog_forth Nat.prime_three le_top hNtop
      ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨q, ⟨rfl, hi⟩, by simp⟩, e⟩
  have hUpper : Nat.card ↥A ≤ 3 ^ 4 :=
    hE (T158Q X 3) (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
      (t158xbar 3 x₁) (t158xbar 3 x₂) hSetup hcatLUe6
  have hcatTwE6 : catalogIs (PSimple 3 (barX 3 ⊤ K))
      (onLie fun i => ∃ q, i = .twistedE6 q ∧ q.p = 2 ∧ 3 ∣ q.card + 1) := by
    change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
    exact catalog_forth Nat.prime_three le_top hNtop
      ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨q, rfl, hi⟩, e⟩
  obtain ⟨E, U, hEL, hUL, hE, hU2, hU1, hEU, hlow⟩ :=
    hL (T158Q X 3) (barX 3 ⊤ K) hPre.qs hcatTwE6
  have hBbElem : IsElemAbelian 3 (barX 3 ⊤ B) := isElemAbelian_barX hBel
  obtain ⟨hBrank', -⟩ := barX_rank_bound (B := B) Nat.prime_three (by norm_num) hBel hrk
  have hW : W ≤ Subgroup.centralizer (barX 3 ⊤ K : Set (T158Q X 3)) := by
    rw [hWdef]
    exact inf_le_right
  have hWB : W ≤ barX 3 ⊤ B := by
    rw [hWdef]
    exact inf_le_left
  have hLower : 3 ^ 4 ≤ Nat.card ↥A := by
    have h := card_pow_le_card_A_of_lower (Q := T158Q X 3) (p := 3) (N := 6) (k := 2)
      (L := barX 3 ⊤ K) (B := barX 3 ⊤ B) (A := A) (W := W) (E := E) (U := U)
      Nat.prime_three hBbElem hAB hWB hAW hAsup hW hEL hUL hE hU2 hU1 hEU hlow hBrank'
    simpa using h
  exact ⟨hSetup, hUpper, hLower⟩

private theorem t158TwA_concl {K B L₁ : Subgroup X} {x₂ : X} {m : ℕ} {M : Subgroup X}
    (hOdd : Odd m) (h1m : 1 < m)
    (hcatK : catalogIs (PSimple 3 K) (S10.isU6n m))
    (hIdent : catalogIs (PSimple 3 L₁) (S10.isL2n (3 * m)))
    (hM : GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) M)
    (hMcat : catalogIs (PSimple 3 M) (S10.isL2n m))
    (hcardB : Nat.card ↥B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) :
    T158Concl15 3 K B x₂ L₁ :=
  ⟨rfl, m, hOdd, h1m, Or.inl ⟨hcatK, hIdent, ⟨M, hM, hMcat⟩, hcardB⟩⟩

theorem t158ShapeLieOn_TwA (hN : T158Norm) (hS : T158SetupLU) (hLU : LinUniBound)
    (hI : T158IdentU6) (hF : T158FixL2) : T158ShapeLieOn t158ShapeTwA := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hcat hh hinn
  obtain ⟨i, hi, e⟩ := hcat
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ :=
    t158m_unpack hh
  cases i with
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | twistedA n q =>
      simp only [t158ShapeTwA, onLie] at hi
      have hp : p.Prime := hh.prime
      have hp2 : p ≠ 2 := hh.odd
      have hp3 : 3 ≤ p := by
        have h2 : 2 ≤ p := hp.two_le
        omega
      haveI : Fact p.Prime := ⟨hp⟩
      have hcatFull : catalogIs (PSimple p K) (t158Shape p) :=
        ⟨.lie ⟨.twistedA n q, hv⟩, Or.inr (Or.inl hi), e⟩
      have hBnorm : B ≤ Subgroup.normalizer (K : Set X) :=
        hN X p K B x₁ x₂ L₁ L₂ hcatFull hh hinn
      have hcK : IsChevSimple 2 (PSimple p K) := by
        refine Or.inl ⟨.lie ⟨.twistedA n q, hv⟩, ?_, e⟩
        simp only [onLie]
        rw [TauCeti.LieTypeIndex.characteristic_twistedA]
        exact hi.1
      obtain ⟨A, W, hPre, hWdef, hAB, hAW, hAsup, -⟩ := exists_preSetup hN hh hinn hcatFull hcK
      obtain ⟨N, -, hUpper, hLower, h2p, hN3, hNval⟩ :=
        t158TwA_setup (K := K) (B := B) (L₁ := L₁) (L₂ := L₂) (x₁ := x₁) (x₂ := x₂)
          (n := n) (q := q) (hv := hv) (hi := hi) (e := e) (A := A) (W := W)
          hS hLU hp hp2 hp3 hPre hWdef hAB hAW hAsup hBel (t158Hyp_rank hh)
      have h3le : 3 ≤ 1 + N / p := by
        have h2le : 2 ≤ N / p := by
          rw [Nat.le_div_iff_mul_le hp.pos]
          exact h2p
        omega
      have hle : N - 3 ≤ 1 + N / p := by
        by_contra hcon
        have hlt : 1 + N / p < N - 3 := by omega
        have hpow : p ^ (1 + N / p) < p ^ (N - 3) :=
          (Nat.pow_lt_pow_iff_right hp.one_lt).2 hlt
        omega
      obtain ⟨hp3eq, hN6⟩ := uni_case_eq hp3 hN3 h3le hle
      obtain rfl : p = 3 := hp3eq
      have hn5 : n = 5 := by omega
      obtain rfl : n = 5 := hn5
      have hi2 : q.p = 2 ∧ 3 ∣ q.card + 1 :=
        ⟨hi.1, (Nat.dvd_gcd_iff.mp hi.2).2⟩
      obtain ⟨m, hOdd, h1m, hcatK, hIdent, M, hM, hMcat⟩ :=
        t158TwA_shape_data (q := q) (hv := hv) (hi := hi2) (e := e) (A := A)
          hPre hBel hx2B hn21 hh.layer hI hF
      have hUpper3 : Nat.card ↥A ≤ 3 ^ 3 := by
        have h := hUpper
        rw [hN6] at h
        norm_num at h
        exact h
      have hLower3 : 3 ^ 3 ≤ Nat.card ↥A := by
        have h := hLower
        rw [hN6] at h
        norm_num at h
        exact h
      have hA3 : Nat.card ↥A = 3 ^ 3 := le_antisymm hUpper3 hLower3
      have hcardB : Nat.card ↥B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
        rw [card_eq_card_mul_inf_centModSubgroup (C := ⊤) Nat.prime_three hK le_top hBel
          hBnorm (W := W) (A := A) hWdef hAB hAW hAsup, hA3]
      exact t158TwA_concl hOdd h1m hcatK hIdent hM hMcat hcardB
    | _ => simp [t158ShapeTwA, onLie] at hi
  | cyclic _ _ => simp [t158ShapeTwA, onLie] at hi
  | alternating _ _ => simp [t158ShapeTwA, onLie] at hi
  | sporadic _ => simp [t158ShapeTwA, onLie] at hi

private theorem t158TwE6_concl {K B L₁ : Subgroup X} {x₂ : X} {m : ℕ} {M : Subgroup X}
    (hOdd : Odd m) (h1m : 1 < m)
    (hcatK : catalogIs (PSimple 3 K) (S10.isTE6n m))
    (hIdent : catalogIs (PSimple 3 L₁) (S10.isU3n (3 * m)))
    (hM : GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) M)
    (hMcat : catalogIs (PSimple 3 M) (S10.isU3n m))
    (hcardB : Nat.card ↥B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) :
    T158Concl15 3 K B x₂ L₁ :=
  ⟨rfl, m, hOdd, h1m, Or.inr ⟨hcatK, hIdent, ⟨M, hM, hMcat⟩, hcardB⟩⟩

theorem t158ShapeLieOn_TwE6 (hN : T158Norm) (hS : T158SetupE6)
    (hE : T171Sh.E6Bound true) (hL : LowerTwE6) (hI : T158IdentTwE6) (hF : T158FixU3) :
    T158ShapeLieOn t158ShapeTwE6 := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hcat hh hinn
  obtain ⟨i, hi, e⟩ := hcat
  obtain ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩ :=
    t158m_unpack hh
  cases i with
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | twistedE6 q =>
      simp only [t158ShapeTwE6, onLie] at hi
      obtain rfl : p = 3 := hi.1
      have hp : (3 : ℕ).Prime := Nat.prime_three
      have hNtop : ¬ 3 ∣ Nat.card (pQuotHom 3 (⊤ : Subgroup X)).ker :=
        CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom hp ⊤
      have hcK : IsChevSimple 2 (PSimple 3 K) := by
        refine Or.inl ⟨.lie ⟨.twistedE6 q, hv⟩, ?_, e⟩
        simp only [onLie]
        rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
        exact hi.2.1
      have hcatFull : catalogIs (PSimple 3 K) (t158Shape 3) :=
        ⟨.lie ⟨.twistedE6 q, hv⟩, Or.inr (Or.inr (Or.inr hi)), e⟩
      have hBnorm : B ≤ Subgroup.normalizer (K : Set X) :=
        hN X 3 K B x₁ x₂ L₁ L₂ hcatFull hh hinn
      obtain ⟨A, W, hPre, hWdef, hAB, hAW, hAsup, -⟩ := exists_preSetup hN hh hinn hcatFull hcK
      have hi2 : q.p = 2 ∧ 3 ∣ q.card + 1 := hi.2
      obtain ⟨-, hUpper, hLower⟩ :=
        t158TwE6_setup (K := K) (B := B) (L₁ := L₁) (L₂ := L₂) (x₁ := x₁) (x₂ := x₂)
          (q := q) (hv := hv) (hi := hi2) (e := e) (A := A) (W := W)
          hS hE hL hPre hWdef hAB hAW hAsup hBel (t158Hyp_rank hh)
      have hA4 : Nat.card ↥A = 3 ^ 4 := le_antisymm hUpper hLower
      let m := q.exponent
      have hcard : q.card = 2 ^ m := by
        rw [TauCeti.PrimePower.card_def, hi.2.1]
      have h3div : 3 ∣ 2 ^ m + 1 := by
        rw [← hcard]
        exact hi.2.2
      have hOdd : Odd m :=
        CFSG.RankThree.PartTwo.Census.odd_of_three_dvd_two_pow_add_one h3div
      have hcatK : catalogIs (PSimple 3 K) (S10.isTE6n m) :=
        ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨hi.2.1, rfl⟩, e⟩
      have hNtop3 : ¬ 3 ∣ Nat.card (pQuotHom 3 (⊤ : Subgroup X)).ker :=
        CFSG.LocalAnalysis.GLTheoremA.H301.not_dvd_card_ker_pQuotHom Nat.prime_three ⊤
      have hcatTE6Kb : catalogIs (PSimple 3 (barX 3 ⊤ K)) (S10.isTE6n m) := by
        change catalogIs (PSimple 3 ((K.subgroupOf ⊤).map (pQuotHom 3 ⊤))) _
        exact catalog_forth Nat.prime_three le_top hNtop3 hcatK
      have hIdentKb : catalogIs (PSimple 3 (barX 3 ⊤ L₁)) (S10.isU3n (3 * m)) :=
        hI (T158Q X 3) (barX 3 ⊤ K) (barX 3 ⊤ L₁) A
          (t158xbar 3 x₁) (t158xbar 3 x₂) m hPre hcatTE6Kb hOdd
      have hcomp : PQuot 3 L₁ ≃* PQuot 3 (barX 3 ⊤ L₁) :=
        CFSG.LocalAnalysis.GLTheoremA.T156.compIso Nat.prime_three
          (Subgroup.map_subgroupOf_eq_of_le (le_top : L₁ ≤ ⊤))
          (pQuotHom 3 ⊤) hNtop3
      have hIdent : catalogIs (PSimple 3 L₁) (S10.isU3n (3 * m)) :=
        (catalogIs_congr
          (CFSG.LocalAnalysis.GLTheoremA.T156.psimpleIso hcomp)).2 hIdentKb
      obtain ⟨M, hM⟩ := exists_glaPComponent_of_layer_ne_bot hh.layer
      have hx2p3 : x₂ ^ 3 = 1 := hBel.2 x₂ hx2B
      have hMcat : catalogIs (PSimple 3 M) (S10.isU3n m) :=
        hF X _ L₁ x₂ m hL1 hx2p3 hn21 hIdent M hM
      have hm_ne_one : m ≠ 1 := by
        intro hm
        exact not_catalogIs_isU3n_one (PSimple 3 M) (by simpa [hm] using hMcat)
      have h1m : 1 < m := by
        rcases hOdd with ⟨k, hk⟩
        omega
      have hcardB : Nat.card ↥B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
        rw [card_eq_card_mul_inf_centModSubgroup (C := ⊤) Nat.prime_three hK le_top hBel
          hBnorm (W := W) (A := A) hWdef hAB hAW hAsup, hA4]
      exact t158TwE6_concl hOdd h1m hcatK hIdent hM hMcat hcardB
    | _ => simp [t158ShapeTwE6, onLie] at hi
  | cyclic _ _ => simp [t158ShapeTwE6, onLie] at hi
  | alternating _ _ => simp [t158ShapeTwE6, onLie] at hi
  | sporadic _ => simp [t158ShapeTwE6, onLie] at hi

end CFSG.LocalAnalysis.GLTheoremA.T158

end
