module

import CFSG.GH74.GLS.Bg.Pu5.BalABasic
import CFSG.GH74.GLS.Bg.Iii2.L41Comp
import CFSG.GH74.GLS.Bg.Pu5.LPTPAbs
import CFSG.GH74.GLS.NT44.DiagonalSupport
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open CFSG.GH74.GLS.Bg.Pu5 CFSG.GH74.GLS.Bg.Iii2.L41
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.TwoThin
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem normalizes_pair_and_centralizes_sections_of_odd_diagonal_commutators
    {G : Type} [Group G] [Finite G] {v u a : G} {L : Subgroup G}
    (hu2 : orderOf u = 2) (hvu : v * u = u * v)
    (hL : IsPCompIn 2 (centralizer ({v} : Set G)) L)
    (huN : u ∉ normalizer (L : Set G))
    (haV : a ∈ centralizer ({v} : Set G))
    (haU : a ∈ centralizer ({u} : Set G))
    (hraw : ∀ d ∈ IDiag u L,
      ⁅d, a⁆ ∈ pPrimeCoreOf 2 (centralizer ({u} : Set G))) :
    a ∈ normalizer (IDiag u L : Set G) ∧
      (((L.map (MulAut.conj a).toMonoidHom = L) ∧
          ((L.map (MulAut.conj u).toMonoidHom).map (MulAut.conj a).toMonoidHom =
            L.map (MulAut.conj u).toMonoidHom)) ∨
        ((L.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj u).toMonoidHom) ∧
          ((L.map (MulAut.conj u).toMonoidHom).map (MulAut.conj a).toMonoidHom = L))) ∧
      (a ∈ normalizer (L : Set G) →
        a ∈ centralizerSection L (pPrimeCoreOf 2 L) ∧
          a ∈ centralizerSection (L.map (MulAut.conj u).toMonoidHom)
            (pPrimeCoreOf 2 (L.map (MulAut.conj u).toMonoidHom))) := by
  classical
  let Cv : Subgroup G := centralizer ({v} : Set G)
  let Cu : Subgroup G := centralizer ({u} : Set G)
  let H : Subgroup G := Cv ⊓ Cu
  let D : Subgroup G := IDiag u L
  let P : Subgroup G := L.map (MulAut.conj u).toMonoidHom
  have huCv : u ∈ Cv := Subgroup.mem_centralizer_singleton_iff.mpr hvu.symm
  have haH : a ∈ H := ⟨haV, haU⟩
  have hD : IsPCompIn 2 H D := by
    show IsPCompIn 2 (Cv ⊓ Cu) (IDiag u L)
    exact Bg.Pu5.BalA.IG_i_gen hu2 hvu hL huN
  have hH_le_Cu : H ≤ Cu := inf_le_right
  let Da : Subgroup G := D.map (MulAut.conj a).toMonoidHom
  have hDa : IsPCompIn 2 H Da := by
    have hHmap : H.map (MulAut.conj a).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haH)
    have h := isPCompIn_map_conj hD a
    rwa [hHmap] at h
  have hfix_bar : ∀ w ∈ bar u D, MulAut.conj (sbar a haU) w = w := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := hw
    have hcD : (c : G) ∈ D := Subgroup.mem_subgroupOf.mp hc
    have hrawc : ⁅(c : G), a⁆ ∈ pPrimeCoreOf 2 Cu := hraw _ hcD
    change ⁅(c : G), a⁆ ∈ (pPrimeCore 2 ↥Cu).map Cu.subtype at hrawc
    obtain ⟨o, ho, hoz⟩ := Subgroup.mem_map.mp hrawc
    have hmemCu : ⁅(c : G), a⁆ ∈ Cu :=
      Cu.mul_mem (Cu.mul_mem (Cu.mul_mem c.2 haU) (Cu.inv_mem c.2)) (Cu.inv_mem haU)
    have hcommE : ⁅c, (⟨a, haU⟩ : ↥Cu)⁆ ∈ pPrimeCore 2 ↥Cu := by
      have hval2 : (⁅c, (⟨a, haU⟩ : ↥Cu)⁆ : ↥Cu) =
          ⟨⁅(c : G), a⁆, hmemCu⟩ := Subtype.ext rfl
      rw [hval2]
      have hval : (⟨⁅(c : G), a⁆, hmemCu⟩ : ↥Cu) = o :=
        Subtype.ext (by simpa using hoz.symm)
      rwa [hval]
    have hq1 : ⁅barMk Cu c, sbar a haU⁆ = 1 := by
      rw [show sbar a haU = barMk Cu ⟨a, haU⟩ from rfl]
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hcommE
    have hq : barMk Cu c * sbar a haU =
        sbar a haU * barMk Cu c :=
      commutatorElement_eq_one_iff_mul_comm.mp hq1
    show MulAut.conj (sbar a haU) (barMk Cu c) = barMk Cu c
    rw [MulAut.conj_apply]
    calc sbar a haU * barMk Cu c * (sbar a haU)⁻¹
        = (barMk Cu c * sbar a haU) * (sbar a haU)⁻¹ := by
          rw [← hq]
      _ = barMk Cu c := by group
  have hfixMap : (bar u D).map (MulAut.conj (sbar a haU)).toMonoidHom =
      bar u D := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      change (MulAut.conj (sbar a haU)) w ∈ bar u D
      rw [hfix_bar w hw]
      exact hw
    · intro w hw
      exact ⟨w, hw, hfix_bar w hw⟩
  have hbarDa : bar u Da = bar u D := by
    have h := bar_cmap (u := u) (s := a) haU D
    simpa [Da, CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap] using h.trans hfixMap
  have hDa_eq : Da = D :=
    eq_of_bar_eq (t := u) (X := H) hH_le_Cu hDa hD hbarDa
  have haND : a ∈ normalizer (D : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hDa_eq
  obtain ⟨hAB, hDelta_eq⟩ :=
    Bg.Pu5.BalA.IG_bar_gen (x := v) (y := u) hu2 hvu hL huN huCv
  let Abar : Subgroup (barQ Cv) := (L.subgroupOf Cv).map (barMk Cv)
  let Bbar : Subgroup (barQ Cv) := conjSub (barMk Cv ⟨u, huCv⟩)⁻¹ Abar
  let Δ : Subgroup (barQ Cv) := (D.subgroupOf Cv).map (barMk Cv)
  let g : barQ Cv := sbar a haV
  let M : Subgroup (barQ Cv) := ((pPrimeCoreOf 2 Cu).subgroupOf Cv).map (barMk Cv)
  have hDelta_eq' : Δ = (swapDiag hAB).range := hDelta_eq
  have hAb : CFSG.IsComponent Abar :=
    isComponent_map_barMk ((TwoThin.isPCompIn_two_iff.mp hL).2)
  have hBb : CFSG.IsComponent Bbar := isComponent_conjSub hAb _
  have hAq : CFSG.Assembly.IsQuasisimple Abar :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Abar).2 hAb.1
  have hΔq : CFSG.IsQuasisimple ↥((swapDiag hAB).range) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      (swapDiag hAB).range).1 (isQuasisimple_range_swapDiag hAB hAq)
  have hdvd_sub : Nat.card ↥((pPrimeCoreOf 2 Cu).subgroupOf Cv) ∣
      Nat.card ↥(pPrimeCoreOf 2 Cu) :=
    Subgroup.card_comap_dvd_of_injective _ _ Cv.subtype_injective
  have hdvd : Nat.card ↥M ∣ Nat.card ↥((pPrimeCoreOf 2 Cu).subgroupOf Cv) :=
    Subgroup.card_map_dvd _ _
  have hModd : Odd (Nat.card ↥M) :=
    (TwoThin.card_pPrimeCoreOf_odd Cu).of_dvd_nat (hdvd.trans hdvd_sub)
  have hcomm : ∀ q ∈ (swapDiag hAB).range, ⁅q, g⁆ ∈ M := by
    intro q hq
    have hqΔ : q ∈ Δ := by
      rw [hDelta_eq']
      exact hq
    obtain ⟨c, hc, rfl⟩ := hqΔ
    have hcD : (c : G) ∈ D := Subgroup.mem_subgroupOf.mp hc
    have hmemCv : ⁅(c : G), a⁆ ∈ Cv :=
      Cv.mul_mem (Cv.mul_mem (Cv.mul_mem c.2 haV) (Cv.inv_mem c.2)) (Cv.inv_mem haV)
    have hmap_comm : barMk Cv ⟨⁅(c : G), a⁆, hmemCv⟩ = ⁅barMk Cv c, g⁆ := by
      have hval : (⟨⁅(c : G), a⁆, hmemCv⟩ : ↥Cv) =
          ⁅c, (⟨a, haV⟩ : ↥Cv)⁆ := Subtype.ext rfl
      calc barMk Cv ⟨⁅(c : G), a⁆, hmemCv⟩
          = barMk Cv ⁅c, (⟨a, haV⟩ : ↥Cv)⁆ := by rw [hval]
        _ = ⁅barMk Cv c, barMk Cv ⟨a, haV⟩⁆ := map_commutatorElement ..
        _ = ⁅barMk Cv c, g⁆ := by
            rw [show g = sbar a haV from rfl]
            rfl
    rw [← hmap_comm]
    exact Subgroup.mem_map_of_mem (barMk Cv)
      (Subgroup.mem_subgroupOf.mpr (hraw (c : G) hcD))
  have halphaD : Δ.map (MulAut.conj g).toMonoidHom = Δ :=
    map_conj_bar_of_normalizes haV haND
  have hgaN : g ∈ normalizer ((swapDiag hAB).range : Set (barQ Cv)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hDelta_eq']
    exact halphaD
  have hcent := commute_of_odd_commutators hΔq hgaN hModd hcomm
  have hfixD : ∀ d ∈ Δ, MulAut.conj g d = d := by
    intro d hd
    have hd' : d ∈ (swapDiag hAB).range := by rwa [hDelta_eq'] at hd
    have hc := hcent d hd'
    rw [MulAut.conj_apply]
    calc g * d * g⁻¹ = (d * g) * g⁻¹ := by rw [← hc]
      _ = d := by group
  have ht2 : orderOf (barMk Cv ⟨u, huCv⟩) = 2 :=
    orderOf_barMk (TwoThin.orderOf_mk_centralizer huCv hu2)
  have htinv : (barMk Cv ⟨u, huCv⟩)⁻¹ = barMk Cv ⟨u, huCv⟩ :=
    inv_eq_self_of_orderOf_eq_two ht2
  have hbarP : bar v P = Bbar := by
    have h := bar_cmap (u := v) (s := u) huCv L
    calc bar v P
        = (bar v L).map
            (MulAut.conj (sbar u huCv)).toMonoidHom := by
          simpa [P, CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap] using h
      _ = (bar v L).map
            (MulAut.conj (barMk Cv ⟨u, huCv⟩)⁻¹).toMonoidHom := by
          rw [show sbar u huCv = barMk Cv ⟨u, huCv⟩ from rfl, htinv]
      _ = Bbar := by
          show (bar v L).map
              (MulAut.conj (barMk Cv ⟨u, huCv⟩)⁻¹).toMonoidHom =
            conjSub (barMk Cv ⟨u, huCv⟩)⁻¹ Abar
          rfl
  have hLa : IsPCompIn 2 Cv (L.map (MulAut.conj a).toMonoidHom) := by
    have hCvma : Cv.map (MulAut.conj a).toMonoidHom = Cv :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haV)
    have h := isPCompIn_map_conj hL a
    rwa [hCvma] at h
  have hP : IsPCompIn 2 Cv P := by
    have hCvmu : Cv.map (MulAut.conj u).toMonoidHom = Cv :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer huCv)
    have h := isPCompIn_map_conj hL u
    rwa [hCvmu] at h
  have hPa : IsPCompIn 2 Cv (P.map (MulAut.conj a).toMonoidHom) := by
    have hCvma : Cv.map (MulAut.conj a).toMonoidHom = Cv :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haV)
    have h := isPCompIn_map_conj hP a
    rwa [hCvma] at h
  have hbarLa : bar v (L.map (MulAut.conj a).toMonoidHom) =
      Abar.map (MulAut.conj g).toMonoidHom := by
    have h := bar_cmap (u := v) (s := a) haV L
    calc bar v (L.map (MulAut.conj a).toMonoidHom)
        = (bar v L).map (MulAut.conj (sbar a haV)).toMonoidHom := by
          simpa [CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap] using h
      _ = Abar.map (MulAut.conj g).toMonoidHom := by
          rw [show bar v L = Abar from rfl]
  have hbarPa : bar v (P.map (MulAut.conj a).toMonoidHom) =
      Bbar.map (MulAut.conj g).toMonoidHom := by
    have h := bar_cmap (u := v) (s := a) haV P
    calc bar v (P.map (MulAut.conj a).toMonoidHom)
        = (bar v P).map (MulAut.conj (sbar a haV)).toMonoidHom := by
          simpa [CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap] using h
      _ = Bbar.map (MulAut.conj g).toMonoidHom := by
          rw [hbarP]
  have hne : Abar ≠ Bbar := by
    intro heq
    have hbarLP : bar v L = bar v P := by
      rw [show bar v L = Abar from rfl, heq, ← hbarP]
    have hLP : L = P := eq_of_bar_eq (t := v) (X := Cv) le_rfl hL hP hbarLP
    have hPL : P = L := hLP.symm
    exact huN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [P] using hPL))
  have hsurjA : ∀ x ∈ Abar, ∃ b ∈ Bbar, x * b ∈ Δ := by
    intro x hx
    refine ⟨(barMk Cv ⟨u, huCv⟩)⁻¹ * x * barMk Cv ⟨u, huCv⟩, ?_, ?_⟩
    · exact conj_mem_conjSub (t := barMk Cv ⟨u, huCv⟩) hx
    · rw [hDelta_eq']
      exact ⟨⟨x, hx⟩, by rw [swapDiag_apply]⟩
  have hsurjB : ∀ b ∈ Bbar, ∃ x ∈ Abar, b * x ∈ Δ := by
    intro b hb
    change b ∈ conjSub (barMk Cv ⟨u, huCv⟩)⁻¹ Abar at hb
    obtain ⟨x, hx, rfl⟩ := hb
    refine ⟨x, hx, ?_⟩
    rw [hDelta_eq']
    have hcomm' := commute_of_commutator_conj_eq_bot hAB hx
      (conj_mem_conjSub (t := barMk Cv ⟨u, huCv⟩) hx)
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [swapDiag_apply]
    simpa [MulAut.conj_apply] using hcomm'
  have hDle : Δ ≤ Abar ⊔ Bbar := by
    rw [hDelta_eq']
    rintro _ ⟨x, rfl⟩
    exact swapDiag_mem_sup hAB x
  obtain ⟨hpair, hfixDonor⟩ :=
    component_pair_action_of_subdirect hAb hBb hne hDle hsurjA hsurjB
      (MulAut.conj g) halphaD
  have hkey : ∀ X Y : Subgroup G, IsPCompIn 2 Cv X → IsPCompIn 2 Cv Y →
      bar v X = bar v Y → X = Y :=
    fun X Y hX hY h => eq_of_bar_eq (t := v) (X := Cv) le_rfl hX hY h
  have hpairLit : (((L.map (MulAut.conj a).toMonoidHom = L) ∧
      (P.map (MulAut.conj a).toMonoidHom = P)) ∨
      ((L.map (MulAut.conj a).toMonoidHom = P) ∧
        (P.map (MulAut.conj a).toMonoidHom = L))) := by
    rcases hpair with ⟨hAfix, hBfix⟩ | ⟨hAswap, hBswap⟩
    · refine Or.inl ⟨?_, ?_⟩
      · exact hkey _ _ hLa hL (by rw [hbarLa, hAfix])
      · exact hkey _ _ hPa hP (by rw [hbarPa, hBfix, ← hbarP])
    · refine Or.inr ⟨?_, ?_⟩
      · exact hkey _ _ hLa hP (by rw [hbarLa, hAswap, ← hbarP])
      · exact hkey _ _ hPa hL (by rw [hbarPa, hBswap])
  refine ⟨haND, ?_, ?_⟩
  · simpa [P] using hpairLit
  · intro haNL
    have hLa_eq : L.map (MulAut.conj a).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haNL
    have hAeq : Abar.map (MulAut.conj g).toMonoidHom = Abar := by
      have h := hbarLa
      rw [hLa_eq] at h
      exact h.symm
    have hPa_eq : P.map (MulAut.conj a).toMonoidHom = P := by
      rcases hpairLit with ⟨-, h⟩ | ⟨hLP, -⟩
      · exact h
      · exfalso
        have hPL : P = L := hLP.symm.trans hLa_eq
        exact huN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [P] using hPL))
    obtain ⟨hfixA, hfixB⟩ := hfixDonor hfixD hAeq
    constructor
    · refine mem_cSec_of_bar (t := v) (s := a) (Λ := L) hL.1 haV haNL ?_
      intro w hw
      have h := hfixA w hw
      simpa [g, MulAut.conj_apply] using h
    · have haNP : a ∈ normalizer (P : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPa_eq
      refine mem_cSec_of_bar (t := v) (s := a) (Λ := P) hP.1 haV haNP ?_
      intro w hw
      have hwB : w ∈ Bbar := by rw [← hbarP]; exact hw
      have h := hfixB w hwB
      simpa [g, MulAut.conj_apply] using h

end CFSG.GH74.GLS.NT44

end
