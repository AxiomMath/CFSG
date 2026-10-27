module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubGrp
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2E
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2K
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLeaves
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2W

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

namespace AlphaFr.E2W

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem mul_comm_of_comm {x a b : Y} (ha : x * a = a * x) (hb : x * b = b * x) :
    x * (a * b) = a * b * x := by
  rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

omit [Finite Y] in
theorem mul_comm_of_conj_eq {x z a b : Y} (ha : x * a * x⁻¹ = z * a) (hb : x * b * x⁻¹ = z * b)
    (hza : a * z = z * a) (hz : z * z = 1) : x * (a * b) = a * b * x := by
  have h : x * (a * b) * x⁻¹ = a * b :=
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = z * (a * z) * b := by rw [ha, hb]; group
      _ = z * z * a * b := by rw [hza]; group
      _ = a * b := by rw [hz, one_mul]
  calc x * (a * b) = x * (a * b) * x⁻¹ * x := by group
    _ = a * b * x := by rw [h]

theorem conj_eq_of_not_mem_omegaNbr (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {W : Subgroup Y}
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W}) {J L : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    (hne : J ≠ L) (hnot : L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {x : Y}
    (hx : x ∈ J) (hxW : x ∉ W) {z u : Y} (hz : IsUniqueInvolution J z)
    (hu : IsUniqueInvolution L u) : x * u * x⁻¹ = z * u := by
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  obtain ⟨hJD, hJsyl⟩ := SecIdE2.mem_DSet_of_wSet hd hc hO2 hW1 J hJ
  obtain ⟨σ, hσ⟩ := SecIdE2.exists_rep_of_wSet hd hc hO2 hW1 L hL
  subst hσ
  exact (Q3CL.T8.ctxOf hd.partIHypG hW).conj_involution ⟨J, J, x, hJ, hJD, hJsyl, hx, hxW⟩ σ
    hne hnot hz hu

theorem mem_omegaNbr_iff_of_not_dConnected (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {W : Subgroup Y}
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W})
    (hnc : ¬ DConnected (CoreAssembly.conjClass (tightCore R))) {B : Subgroup Y}
    (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {J : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) (hJK : J ≠ tightCore R) (hJB : J ≠ B) :
    tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J ↔
      B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  have c := Q3CL.T8.ctxOf hd.partIHypG hW
  obtain ⟨ρ, hρ⟩ :=
    SecIdE2.exists_rep_of_wSet hd hc hO2 hW1 _ (CoreAssembly.mem_conjClass_self _)
  obtain ⟨σ, hσ⟩ := SecIdE2.exists_rep_of_wSet hd hc hO2 hW1 B hB.1
  obtain ⟨τ, hτ⟩ := SecIdE2.exists_rep_of_wSet hd hc hO2 hW1 J hJ
  have hTT := Q3T6.Mu.isTT_muDelta hd.partIHypG hW
  have hS := Q3T6.Mu.isStar_muDelta c
  obtain ⟨d, hdΔ, a, haΔ, hda⟩ := Q3T6.Mu.exists_not_conn_of_not_connected hd.hypOmegaGen hW
    (SecIdE2.not_dbarConnected_of_wSet hd hc hO2 hW1 hnc)
  obtain ⟨q, hq, hkq⟩ : ∃ q ∈ muDelta (CoreAssembly.conjClass (tightCore R)) W,
      ¬ Star3T.Conn (muDelta (CoreAssembly.conjClass (tightCore R)) W) (T8.repElt ρ) q := by
    by_cases hka : Star3T.Conn (muDelta (CoreAssembly.conjClass (tightCore R)) W)
        (T8.repElt ρ) a
    · exact ⟨d, hdΔ, fun hkd => hda (hkd.symm.trans hka)⟩
    · exact ⟨a, haΔ, hka⟩
  have hne : ρ.K ≠ σ.K := by
    rw [hρ, hσ]
    exact hB.2.1.symm
  have hkb : T8.repElt σ ∈
      Star3T.cent (muDelta (CoreAssembly.conjClass (tightCore R)) W) (T8.repElt ρ) :=
    ⟨T8.repElt_mem σ, ((repElt_commute_iff_gen c ρ σ hne).mpr (by rw [hρ, hσ]; exact hB)).symm⟩
  have hcent := Star3T.cent_eq_of_mem_cent hTT hS (T8.repElt_mem ρ) hq hkq hkb
  have e1 := repElt_commute_iff_gen c τ ρ (by rw [hτ, hρ]; exact hJK)
  have e2 := repElt_commute_iff_gen c τ σ (by rw [hτ, hσ]; exact hJB)
  rw [hτ, hρ] at e1
  rw [hτ, hσ] at e2
  rw [← e1, ← e2]
  have hj := T8.repElt_mem τ
  constructor
  · intro h
    have h' : T8.repElt τ ∈
        Star3T.cent (muDelta (CoreAssembly.conjClass (tightCore R)) W) (T8.repElt σ) := by
      rw [hcent]
      exact ⟨hj, h⟩
    exact h'.2
  · intro h
    have h' : T8.repElt τ ∈
        Star3T.cent (muDelta (CoreAssembly.conjClass (tightCore R)) W) (T8.repElt ρ) := by
      rw [← hcent]
      exact ⟨hj, h⟩
    exact h'.2

theorem mul_mem_center_of_not_dConnected (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {W : Subgroup Y}
    (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W})
    (hnc : ¬ DConnected (CoreAssembly.conjClass (tightCore R))) {B : Subgroup Y}
    (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {v : Y}
    (hv : IsUniqueInvolution B v) : t * v ∈ Subgroup.center Y := by
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  have c := Q3CL.T8.ctxOf hd.partIHypG hW
  have hut := hd.isUniqueInvolution_core
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  have htW := SecIdE2.uniqueInvolution_mem_wSet hd hc hO2 hW1 _ hK t hut
  have hvW := SecIdE2.uniqueInvolution_mem_wSet hd hc hO2 hW1 B hB.1 v hv
  have hKB := E2A.commutes_of_mem_omegaNbr hd hc hO2 hK hB
  have key : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∀ x ∈ J, x * (t * v) = t * v * x := by
    intro J hJ x hx
    by_cases hxW : x ∈ W
    · exact c.comm_W x hxW _ (W.mul_mem htW hvW)
    by_cases hJK : J = tightCore R
    · subst hJK
      exact mul_comm_of_comm (TC.Thin.isUniqueInvolution_comm hut hx) (hKB x hx v hv.mem)
    by_cases hJB : J = B
    · subst hJB
      exact mul_comm_of_comm (hKB t hut.mem x hx).symm (TC.Thin.isUniqueInvolution_comm hv hx)
    have hiff := mem_omegaNbr_iff_of_not_dConnected hd hc hO2 hW1 hnc hB hJ hJK hJB
    by_cases hadj : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J
    · have h1 := E2A.commutes_of_mem_omegaNbr hd hc hO2 hJ hadj
      have h2 := E2A.commutes_of_mem_omegaNbr hd hc hO2 hJ (hiff.mp hadj)
      exact mul_comm_of_comm (h1 x hx t hut.mem) (h2 x hx v hv.mem)
    · obtain ⟨z, hz⟩ := E2A.exists_isUniqueInvolution hd hJ
      have hzW := SecIdE2.uniqueInvolution_mem_wSet hd hc hO2 hW1 J hJ z hz
      exact mul_comm_of_conj_eq
        (conj_eq_of_not_mem_omegaNbr hd hc hO2 hW1 hJ hK hJK hadj hx hxW hz hut)
        (conj_eq_of_not_mem_omegaNbr hd hc hO2 hW1 hJ hB.1 hJB (fun h => hadj (hiff.mpr h)) hx
          hxW hz hv)
        (c.comm_W t htW z hzW) hz.sq
  have hle : TC.Thin.pSpan (CoreAssembly.conjClass (tightCore R)) ≤
      Subgroup.centralizer ({t * v} : Set Y) := TC.Thin.pSpan_le fun J hJ x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact key J hJ x hx
  rw [E2D.pSpan_eq_top hc] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := hle (Subgroup.mem_top g)
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  exact hg

end AlphaFr.E2W

section Cit3


theorem secIdE2LinkGen_proved : SecIdE2LinkGen := by
  intro n _ hP Y _ _ hn R S t hd hc hO2 hnc B hB v hv
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  rcases SecIdE2.thmDConcl_of hP hn hd hc hO2 with
    h1 | ⟨W, hW1⟩ | ⟨E, hE⟩ | h64 | ⟨m, hm, ⟨I⟩⟩ | h29
  · exact absurd (h1 B hB.1 _ hK) hB.2.1
  · exact AlphaFr.E2.linkGen_of_mul_mem_center
      (AlphaFr.E2W.mul_mem_center_of_not_dConnected hd hc hO2 hW1 hnc hB hv)
  · exact AlphaFr.E2E.linkGen_of_e8 hd hO2 hE hB.1 hv
  · obtain ⟨I⟩ := h64
    exact AlphaFr.E2.linkGen_of_mul_mem_center
      (AlphaFr.E2A.mul_mem_center_of_aeIdentOn hd hc hO2 (by norm_num) (by norm_num) I hB hv)
  · by_cases hm8 : m ≤ 8
    · exact AlphaFr.E2.linkGen_of_mul_mem_center
        (AlphaFr.E2A.mul_mem_center_of_aeIdent hd hc hO2 hm hm8 I hB hv)
    · exact absurd (AlphaFr.E2A.dConnected_of_aeIdent hd hc hO2 (by omega) I) hnc
  · obtain ⟨I⟩ := h29
    exact AlphaFr.E2.linkGen_of_mul_mem_center
      (AlphaFr.E2A.mul_mem_center_of_aeIdentOn hd hc hO2 (by norm_num) le_rfl I hB hv)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
