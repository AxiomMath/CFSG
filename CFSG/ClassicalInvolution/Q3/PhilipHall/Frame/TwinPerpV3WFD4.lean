module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFWM
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuLayer

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

section D4outer




variable {n : ℕ}


section D4

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.far_mem (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (k : Fin 4) :
    conjSub y (M k) ∈ CoreAssembly.conjClass (tightCore R) ∧
      IsUniqueInvolution (conjSub y (M k)) (y * t * y⁻¹) ∧
      conjSub y (M k) ∈ DSet (CoreAssembly.conjClass (tightCore R)) W := by
  have hΩ : conjSub y (M k) ∈ CoreAssembly.conjClass (tightCore R) :=
    h.hyp.conjInvariant y _ (hfr.mem k).1
  have hu : IsUniqueInvolution (conjSub y (M k)) (y * t * y⁻¹) := (h.uniqInv (hfr.mem k)).conj y
  exact ⟨hΩ, hu, twin_mem_DSet h.partI h.exit.2.2.2.1 h.hW hfr.s_mem_W hΩ hu⟩

theorem WFFrame.far_ne (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (k l : Fin 4) :
    conjSub y (M k) ≠ M l := by
  intro e
  have h1 := (hfr.far_mem h k).2.1
  rw [e] at h1
  exact hfr.fuse_ne ((h1.eq (h.uniqInv (hfr.mem l))))

theorem WFFrame.far_not_nbr (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (k l : Fin 4) :
    conjSub y (M k) ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (M l) := by
  intro hnb
  have hperp := kPerp_datum h.hStd.perp (hfr.mem l).1 (h.uniqInv (hfr.mem l))
  have hmem : conjSub y (M k) ∈ KPerp (CoreAssembly.conjClass (tightCore R)) (M l) :=
    Set.mem_insert_of_mem _ hnb
  rw [hperp] at hmem
  obtain ⟨-, z, hz1, hz2⟩ := hmem
  exact hfr.fuse_ne ((hz2.eq (hfr.far_mem h k).2.1).symm.trans (hz1.eq (h.uniqInv (hfr.mem l))))

theorem wfD4_proved (n : ℕ) : WFD4 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr
  have hP := h.partI
  have hW := h.hW
  have c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W := Q3CL.T8.ctxOf hP hW
  have h2g := h.exit.2.2.2.1
  have hd := h.hStd.datum
  obtain ⟨s, hs⟩ : ∃ s, s = y * t * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : Fin 4 → Subgroup Y, ∀ i, J i = conjSub y (M i) := ⟨_, fun _ => rfl⟩
  have hJΩ : ∀ i, J i ∈ CoreAssembly.conjClass (tightCore R) := fun i => by
    rw [hJ i]; exact (hfr.far_mem h i).1
  have hJu : ∀ i, IsUniqueInvolution (J i) s := fun i => by
    rw [hJ i, hs]; exact (hfr.far_mem h i).2.1
  have hJD : ∀ i, J i ∈ DSet (CoreAssembly.conjClass (tightCore R)) W := fun i => by
    rw [hJ i]; exact (hfr.far_mem h i).2.2
  have hJsyl : ∀ i, IsSylow2In (J i) (J i) := fun i =>
    ⟨le_rfl, h2g _ (hJΩ i), fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hMD : ∀ l, M l ∈ DSet (CoreAssembly.conjClass (tightCore R)) W := fun l =>
    twin_mem_DSet hP h2g hW h.t_mem (hfr.mem l).1 (h.uniqInv (hfr.mem l))
  have hMsyl : ∀ l, IsSylow2In (M l) (M l) := fun l =>
    ⟨le_rfl, h2g _ (hfr.mem l).1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Fin 4 → Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W,
      ∀ i, (ρ i).K = J i :=
    ⟨fun i => Q3CL.T8.mkRep hP hW (hJΩ i) (hJD i) (hJsyl i), fun i => rfl⟩
  obtain ⟨ρS, hρSK⟩ : ∃ ρS : Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W,
      ρS.K = M 0 := ⟨Q3CL.T8.mkRep hP hW (hfr.mem 0).1 (hMD 0) (hMsyl 0), rfl⟩
  have hJne : ∀ i j, i ≠ j → J i ≠ J j := fun i j hij e =>
    hij (hfr.inj (conjSub_injective y (by rw [← hJ i, ← hJ j]; exact e)))
  have hperp : ∀ i, KPerp (CoreAssembly.conjClass (tightCore R)) (M i) =
      twinSet (CoreAssembly.conjClass (tightCore R)) (M i) := fun i =>
    kPerp_datum h.hStd.perp (hfr.mem i).1 (h.uniqInv (hfr.mem i))
  have hnbrM : ∀ i j, i ≠ j → M j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (M i) := by
    intro i j hij
    have hmem : M j ∈ KPerp (CoreAssembly.conjClass (tightCore R)) (M i) := by
      rw [hperp i]
      exact ⟨(hfr.mem j).1, t, h.uniqInv (hfr.mem i), h.uniqInv (hfr.mem j)⟩
    exact hmem.resolve_left (fun e => hij (hfr.inj e).symm)
  have hnbr : ∀ i j, i ≠ j → J j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (J i) := by
    intro i j hij
    rw [hJ i, hJ j]
    exact omegaNbr_conj h.hyp.conjInvariant (hnbrM i j hij) y
  have hnc : ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W := by
    obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W, ρ₀.K = K :=
      ⟨Q3CL.T8.mkRep hP hW hd.mem h.hKD ⟨le_rfl, h2g _ hd.mem, fun V' hV'K _ hKV' =>
        le_antisymm hV'K hKV'⟩, rfl⟩
    exact not_dbarConnected_of_wyl' hP hd (kPerp_datum h.hStd.perp hd.mem hd.hz) hW ρ₀ hρ₀
      (h.hStd.wyl W hW)
  have hTT := Q3T6.Mu.isTT_muDelta hP hW
  have hS := Q3T6.Mu.isStar_muDelta c
  have hmu_ne : ∀ i j, i ≠ j →
      Asc77.MuTab.muTabElt (ρ i) ≠ Asc77.MuTab.muTabElt (ρ j) := fun i j hij e =>
    hJne i j hij (by
      rw [← hρK i, ← hρK j]; exact (Q3T6.Mu.muTabElt_eq_iff hP hW _ _).mp e)
  have hmu_comm : ∀ i j, i ≠ j → Asc77.MuTab.muTabElt (ρ i) * Asc77.MuTab.muTabElt (ρ j) =
      Asc77.MuTab.muTabElt (ρ j) * Asc77.MuTab.muTabElt (ρ i) := fun i j hij =>
    (Q3T6.Mu.muTab_commute_iff hP hW (ρ i) (ρ j) (by rw [hρK i, hρK j]; exact hJne i j hij)).mpr
      (by rw [hρK i, hρK j]; exact hnbr i j hij)
  obtain ⟨a', ha'Δ, hconna'⟩ := Q3T6.Mu.exists_not_conn_at hP hW hnc (Asc77.MuTab.muTabElt (ρ 0))
  have hxa := Asc77.MuTab.muTabElt_mem (ρ 0)
  have hyF : Asc77.MuTab.muTabElt ρS ∉
      Asc77.Star3T.cent (muDelta (CoreAssembly.conjClass (tightCore R)) W) (Asc77.MuTab.muTabElt (ρ 0)) := by
    rintro ⟨-, hx⟩
    exact c.noncomm ρS (ρ 0) (by rw [hρSK, hρK 0, hJ 0]; exact (hfr.far_ne h 0 0).symm)
      (by rw [hρSK, hρK 0, hJ 0]; exact hfr.far_not_nbr h 0 0) (congrArg Subtype.val hx)
  have hconn : ¬ Asc77.Star3T.Conn (muDelta (CoreAssembly.conjClass (tightCore R)) W)
      (Asc77.MuTab.muTabElt (ρ 0)) (Asc77.MuTab.muTabElt ρS) :=
    TwinMu.not_conn_of_not_mem_cent hTT hS hxa ha'Δ hconna' hyF
  obtain ⟨ρd, zd, hF4, hzd, -, -, ka, kb, kc, kd, hka, hkb, hkc, hkd, hka2, hkb2, hkc2, hkd2, -, -,
    -, -, hprod⟩ :=
    TwinMu.frame_prod hP hW (hmu_ne 0 1 (by decide)) (hmu_ne 0 2 (by decide))
      (hmu_ne 1 2 (by decide)) (hmu_comm 0 1 (by decide)) (hmu_comm 0 2 (by decide))
      (hmu_comm 1 2 (by decide)) hconn (w := a 0) (zS := t) (za := s) (zb := s) (zc := s)
      (by rw [hρSK]; exact Subgroup.mem_inf.mpr ⟨hfr.haM 0, hfr.haW 0⟩)
      (by rw [hρSK]; exact h.uniqInv (hfr.mem 0)) (hfr.sq h 0)
      (by rw [hρK 0]; exact hJu 0) (by rw [hρK 1]; exact hJu 1) (by rw [hρK 2]; exact hJu 2)
  have hρdJ : ∃ l, ρd.K = J l := by
    have h1 : conjSub y⁻¹ ρd.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (M 0) := by
      have := omegaNbr_conj h.hyp.conjInvariant (by rw [← hρK 0]; exact hF4.ad :
        ρd.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (J 0)) y⁻¹
      rwa [hJ 0, conjSub_inv_conjSub] at this
    have h2 : conjSub y⁻¹ ρd.K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (M 0) := by
      rw [← hperp 0]; exact Set.mem_insert_of_mem _ h1
    have h2' : conjSub y⁻¹ ρd.K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := by
      rw [← twinSet_eq_of_mem_twinSet hd.hz (hfr.mem 0)]; exact h2
    obtain ⟨l, hl⟩ := hfr.surj _ h2'
    exact ⟨l, by rw [hJ l, hl]; exact (conjSub_conjSub_inv y ρd.K).symm⟩
  obtain ⟨l, hl⟩ := hρdJ
  have hl0 : l ≠ 0 := fun e => (hF4.ad.2.1) (by rw [hl, hρK 0, e])
  have hl1 : l ≠ 1 := fun e => (hF4.bd.2.1) (by rw [hl, hρK 1, e])
  have hl2 : l ≠ 2 := fun e => (hF4.cd.2.1) (by rw [hl, hρK 2, e])
  have hl3 : l = 3 := by
    have key : ∀ l : Fin 4, l ≠ 0 → l ≠ 1 → l ≠ 2 → l = 3 := by decide
    exact key l hl0 hl1 hl2
  subst hl3
  have hzds : zd = s := hzd.eq (by rw [hl]; exact hJu 3)
  rw [hzds] at hkd2
  rw [hρK 0] at hka
  rw [hρK 1] at hkb
  rw [hρK 2] at hkc
  rw [hl] at hkd
  have hconj : ∀ (i : Fin 4) (x : Y), x ∈ J i → x * x = s → y⁻¹ * x * y ∈ M i ∧
      (y⁻¹ * x * y) * (y⁻¹ * x * y) = t := by
    intro i x hx hx2
    refine ⟨?_, ?_⟩
    · rw [hJ i, mem_conjSub_iff] at hx
      exact hx
    · calc (y⁻¹ * x * y) * (y⁻¹ * x * y) = y⁻¹ * (x * x) * y := by group
        _ = y⁻¹ * s * y := by rw [hx2]
        _ = t := by rw [hs]; group
  obtain ⟨hu0M, hu0⟩ := hconj 0 ka (Subgroup.mem_inf.mp hka).1 hka2
  obtain ⟨hu1M, hu1⟩ := hconj 1 kb (Subgroup.mem_inf.mp hkb).1 hkb2
  obtain ⟨hu2M, hu2⟩ := hconj 2 kc (Subgroup.mem_inf.mp hkc).1 hkc2
  obtain ⟨hu3M, hu3⟩ := hconj 3 kd (Subgroup.mem_inf.mp hkd).1 hkd2
  refine ⟨![y⁻¹ * ka * y, y⁻¹ * kb * y, y⁻¹ * kc * y, y⁻¹ * kd * y], ?_, ?_⟩
  · intro i
    fin_cases i
    exacts [⟨hu0M, hu0⟩, ⟨hu1M, hu1⟩, ⟨hu2M, hu2⟩, ⟨hu3M, hu3⟩]
  · show y⁻¹ * t * y = (y⁻¹ * ka * y) * (y⁻¹ * kb * y) * (y⁻¹ * kc * y) * (y⁻¹ * kd * y)
    calc y⁻¹ * t * y = y⁻¹ * (ka * kb * kc * kd) * y := by rw [hprod]
      _ = _ := by group

end D4

end D4outer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
