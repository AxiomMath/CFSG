module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ESup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Relouter




variable {n : ℕ}


section Rel

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem act_indep {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {W₁ R' : Subgroup Y}
    (hW₁ : W₁ ∈ WSet Ω) (hR' : R' ∈ DSet Ω W₁) {r r' : Y} (hr : r ∈ R') (hr' : r' ∈ R')
    (hrW : r ∉ W₁) (hr'W : r' ∉ W₁) {w : Y} (hw : w ∈ W₁) : r * w * r⁻¹ = r' * w * r'⁻¹ := by
  have hc := Q3CL.Thompson.D_inv_mul_mem hΩ hW₁ hR' hr hr' hrW hr'W
  have hab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW₁
  have hcomm := hab _ hc _ hw
  calc r * w * r⁻¹ = r * ((r⁻¹ * r') * w * (r⁻¹ * r')⁻¹) * r⁻¹ := by
        rw [show (r⁻¹ * r') * w * (r⁻¹ * r')⁻¹ = w by rw [hcomm]; group]
    _ = r' * w * r'⁻¹ := by group

theorem WFFrame.frame_rel (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {W₁ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW₁ : t ∈ W₁)
    {Sm : Subgroup Y} {zS : Y} (hSΩ : Sm ∈ CoreAssembly.conjClass (tightCore R))
    (hSD : Sm ∈ DSet (CoreAssembly.conjClass (tightCore R)) W₁) (hSz : IsUniqueInvolution Sm zS)
    (hSne : Sm ≠ M 0) (hSnot : M 0 ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) Sm) {w : Y}
    (hw : w ∈ Sm ⊓ W₁) (hw2 : w * w = zS) :
    ∃ k : Fin 4 → Y, (∀ i, k i ∈ M i ⊓ W₁ ∧ k i * k i = t) ∧ k 0 * k 1 * k 2 * k 3 = zS ∧
      ∀ i, ∀ v ∈ M i, v ∉ W₁ → v * w * v⁻¹ = k i * w := by
  have hP := h.partI
  have c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W₁ := Q3CL.T8.ctxOf hP hW₁
  have h2g := h.exit.2.2.2.1
  have hd := h.hStd.datum
  have hMD : ∀ l, M l ∈ DSet (CoreAssembly.conjClass (tightCore R)) W₁ := fun l =>
    twin_mem_DSet hP h2g hW₁ htW₁ (hfr.mem l).1 (h.uniqInv (hfr.mem l))
  have hMsyl : ∀ l, IsSylow2In (M l) (M l) := fun l =>
    ⟨le_rfl, h2g _ (hfr.mem l).1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hSsyl : IsSylow2In Sm Sm := ⟨le_rfl, h2g _ hSΩ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Fin 4 → Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W₁,
      ∀ i, (ρ i).K = M i :=
    ⟨fun i => Q3CL.T8.mkRep hP hW₁ (hfr.mem i).1 (hMD i) (hMsyl i), fun i => rfl⟩
  obtain ⟨ρS, hρSK⟩ : ∃ ρS : Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W₁,
      ρS.K = Sm := ⟨Q3CL.T8.mkRep hP hW₁ hSΩ hSD hSsyl, rfl⟩
  have hperp : ∀ i, KPerp (CoreAssembly.conjClass (tightCore R)) (M i) =
      twinSet (CoreAssembly.conjClass (tightCore R)) (M i) := fun i =>
    kPerp_datum h.hStd.perp (hfr.mem i).1 (h.uniqInv (hfr.mem i))
  have hnbrM : ∀ i j, i ≠ j → M j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (M i) := by
    intro i j hij
    have hmem : M j ∈ KPerp (CoreAssembly.conjClass (tightCore R)) (M i) := by
      rw [hperp i]
      exact ⟨(hfr.mem j).1, t, h.uniqInv (hfr.mem i), h.uniqInv (hfr.mem j)⟩
    exact hmem.resolve_left (fun e => hij (hfr.inj e).symm)
  have hnc : ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W₁ := by
    obtain ⟨j₀, hj₀⟩ := hfr.surj K (mem_twinSet_self hd.mem hd.hz)
    exact not_dbarConnected_of_wyl' hP hd (kPerp_datum h.hStd.perp hd.mem hd.hz) hW₁ (ρ j₀)
      ((hρK j₀).trans hj₀) (h.hStd.wyl W₁ hW₁)
  have hTT := Q3T6.Mu.isTT_muDelta hP hW₁
  have hS := Q3T6.Mu.isStar_muDelta c
  have hmu_ne : ∀ i j, i ≠ j →
      Asc77.MuTab.muTabElt (ρ i) ≠ Asc77.MuTab.muTabElt (ρ j) := fun i j hij e =>
    hij (hfr.inj (by
      rw [← hρK i, ← hρK j]; exact (Q3T6.Mu.muTabElt_eq_iff hP hW₁ _ _).mp e))
  have hmu_comm : ∀ i j, i ≠ j → Asc77.MuTab.muTabElt (ρ i) * Asc77.MuTab.muTabElt (ρ j) =
      Asc77.MuTab.muTabElt (ρ j) * Asc77.MuTab.muTabElt (ρ i) := fun i j hij =>
    (Q3T6.Mu.muTab_commute_iff hP hW₁ (ρ i) (ρ j) (by
      rw [hρK i, hρK j]; exact fun e => hij (hfr.inj e))).mpr
      (by rw [hρK i, hρK j]; exact hnbrM i j hij)
  obtain ⟨a', ha'Δ, hconna'⟩ :=
    Q3T6.Mu.exists_not_conn_at hP hW₁ hnc (Asc77.MuTab.muTabElt (ρ 0))
  have hxa := Asc77.MuTab.muTabElt_mem (ρ 0)
  have hyF : Asc77.MuTab.muTabElt ρS ∉
      Asc77.Star3T.cent (muDelta (CoreAssembly.conjClass (tightCore R)) W₁)
        (Asc77.MuTab.muTabElt (ρ 0)) := by
    rintro ⟨-, hx⟩
    exact c.noncomm ρS (ρ 0) (by rw [hρSK, hρK 0]; exact hSne)
      (by rw [hρSK, hρK 0]; exact hSnot) (congrArg Subtype.val hx)
  have hconn : ¬ Asc77.Star3T.Conn (muDelta (CoreAssembly.conjClass (tightCore R)) W₁)
      (Asc77.MuTab.muTabElt (ρ 0)) (Asc77.MuTab.muTabElt ρS) :=
    TwinMu.not_conn_of_not_mem_cent hTT hS hxa ha'Δ hconna' hyF
  obtain ⟨ρd, zd, hF4, hzd, -, -, ka, kb, kc, kd, hka, hkb, hkc, hkd, hka2, hkb2, hkc2, hkd2, hra, hrb,
    hrc, hrd, hprod⟩ :=
    TwinMu.frame_prod hP hW₁ (hmu_ne 0 1 (by decide)) (hmu_ne 0 2 (by decide))
      (hmu_ne 1 2 (by decide)) (hmu_comm 0 1 (by decide)) (hmu_comm 0 2 (by decide))
      (hmu_comm 1 2 (by decide)) hconn (w := w) (zS := zS) (za := t) (zb := t) (zc := t)
      (by rw [hρSK]; exact hw) (by rw [hρSK]; exact hSz) hw2
      (by rw [hρK 0]; exact h.uniqInv (hfr.mem 0)) (by rw [hρK 1]; exact h.uniqInv (hfr.mem 1))
      (by rw [hρK 2]; exact h.uniqInv (hfr.mem 2))
  have hρdJ : ∃ l, M l = ρd.K := by
    have h1 : ρd.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (M 0) := by
      have := hF4.ad
      rwa [hρK 0] at this
    have h2 : ρd.K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (M 0) := by
      rw [← hperp 0]; exact Set.mem_insert_of_mem _ h1
    have h2' : ρd.K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := by
      rw [← twinSet_eq_of_mem_twinSet hd.hz (hfr.mem 0)]; exact h2
    exact hfr.surj _ h2'
  obtain ⟨l, hl⟩ := hρdJ
  have hl0 : l ≠ 0 := fun e => (hF4.ad.2.1) (by rw [← hl, e, hρK 0])
  have hl1 : l ≠ 1 := fun e => (hF4.bd.2.1) (by rw [← hl, e, hρK 1])
  have hl2 : l ≠ 2 := fun e => (hF4.cd.2.1) (by rw [← hl, e, hρK 2])
  have hl3 : l = 3 := by
    have key : ∀ l : Fin 4, l ≠ 0 → l ≠ 1 → l ≠ 2 → l = 3 := by decide
    exact key l hl0 hl1 hl2
  subst hl3
  have hzdt : zd = t := hzd.eq (by rw [← hl]; exact h.uniqInv (hfr.mem 3))
  rw [hzdt] at hkd2
  rw [hρK 0] at hka
  rw [hρK 1] at hkb
  rw [hρK 2] at hkc
  rw [← hl] at hkd
  have hactM : ∀ (i : Fin 4) (v r : Y), v ∈ M i → r ∈ M i → v ∉ W₁ → r ∉ W₁ →
      v * w * v⁻¹ = r * w * r⁻¹ := fun i v r hv hr hvW hrW =>
    act_indep h.hyp hW₁ (hMD i) hv hr hvW hrW hw.2
  refine ⟨![ka, kb, kc, kd], ?_, hprod, ?_⟩
  · intro i
    fin_cases i
    exacts [⟨hka, hka2⟩, ⟨hkb, hkb2⟩, ⟨hkc, hkc2⟩, ⟨hkd, hkd2⟩]
  · intro i v hv hvW
    fin_cases i
    · show v * w * v⁻¹ = ka * w
      rw [hactM 0 v (ρ 0).r hv (by rw [← hρK 0]; exact (ρ 0).hRK.1 (ρ 0).hr) hvW (ρ 0).hrW]
      exact hra
    · show v * w * v⁻¹ = kb * w
      rw [hactM 1 v (ρ 1).r hv (by rw [← hρK 1]; exact (ρ 1).hRK.1 (ρ 1).hr) hvW (ρ 1).hrW]
      exact hrb
    · show v * w * v⁻¹ = kc * w
      rw [hactM 2 v (ρ 2).r hv (by rw [← hρK 2]; exact (ρ 2).hRK.1 (ρ 2).hr) hvW (ρ 2).hrW]
      exact hrc
    · show v * w * v⁻¹ = kd * w
      rw [hactM 3 v ρd.r hv (by rw [hl]; exact ρd.hRK.1 ρd.hr) hvW ρd.hrW]
      exact hrd

end Rel

end Relouter

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
