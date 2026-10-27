module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Hx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Wt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Hx

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform

theorem ae6P_conj {Y : Type} [Group Y] {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω) (g c : Y) :
    conjSub g (ae6P Ω c) = ae6P Ω (g * c * g⁻¹) := by
  have hle : ∀ (g c : Y), conjSub g (ae6P Ω c) ≤ ae6P Ω (g * c * g⁻¹) := by
    intro g c
    unfold ae6P
    rw [conjSub_iSup₂]
    refine iSup₂_le fun J hJ => ?_
    have hJ' : conjSub g J ∈ ae6Vc Ω (g * c * g⁻¹) := ⟨hinv g J hJ.1, hJ.2.conj g⟩
    exact le_iSup₂_of_le (f := fun J (_ : J ∈ ae6Vc Ω (g * c * g⁻¹)) => J) (conjSub g J) hJ' le_rfl
  refine le_antisymm (hle g c) ?_
  have h := hle g⁻¹ (g * c * g⁻¹)
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rw [e] at h
  calc ae6P Ω (g * c * g⁻¹) = conjSub g (conjSub g⁻¹ (ae6P Ω (g * c * g⁻¹))) :=
        (conjSub_conjSub_inv g _).symm
    _ ≤ conjSub g (ae6P Ω c) := conjSub_mono h

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem exists_M_moves_t (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    ∃ m ∈ MGrp Ω[R] W, m * t * m⁻¹ ≠ t := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hK : K ∈ Ω[R] := hd.mem
  have c0 : Q3CL.Thompson.Ctx Ω[R] W := Q3CL.T8.ctxOf hP H.hW
  have hKsyl : IsSylow2In K K := ⟨le_rfl, h2g K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρK, hρK⟩ : ∃ ρ : Asc77.Thompson.Rep Ω[R] W, ρ.K = K :=
    ⟨Q3CL.T8.mkRep hP H.hW hK H.hK hKsyl, rfl⟩
  have hnc : ¬ DbarConnected Ω[R] W :=
    not_dbarConnected_of_wyl' hP hd (kPerp_datum hStd.perp hd.mem hd.hz) H.hW ρK hρK (hStd.wyl W H.hW)
  have hnab : ¬ ∀ x y : ↥(muGroup Ω[R] W), x * y = y * x := fun hc =>
    TL4.not_comm_of_muIsoWylD4_gen (hStd.wyl W H.hW) fun x hx y hy =>
      congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ, σ, hρσ⟩ := TwinPerpV3.exists_noncomm_rep hP H.hW hnab
  have htw : ∀ τ : Asc77.Thompson.Rep Ω[R] W, IsUniqueInvolution τ.K t := by
    intro τ
    obtain ⟨m, hm, hmK⟩ := c0.exists_conj_of_rep hP.cls hnc ρK τ
    have h1 := hd.hz.conj m
    rw [hcon m hm] at h1
    rw [← hmK, hρK]
    exact h1
  apply hρσ
  by_cases he : ρ.K = σ.K
  · have h1 := (Q3T6.Mu.muTabElt_eq_iff hP H.hW ρ σ).mpr he
    have h2 : ρ.img = σ.img := congrArg Subtype.val h1
    rw [h2]
  · have hnb : σ.K ∈ omegaNbr Ω[R] ρ.K := by
      have hmem : σ.K ∈ KPerp Ω[R] ρ.K := by
        rw [kPerp_datum hStd.perp ρ.hK (htw ρ)]
        exact ⟨σ.hK, t, htw ρ, htw σ⟩
      exact hmem.resolve_left (fun e => he e.symm)
    exact congrArg Subtype.val ((Q3T6.Mu.muTab_commute_iff hP H.hW ρ σ he).mpr hnb)

theorem exists_M_conj_t_tau (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    ∃ m ∈ MGrp Ω[R] W, m * t * m⁻¹ = y * t * y⁻¹ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  obtain ⟨m, hm, hmt⟩ := exists_M_moves_t H
  have hmN : m ∈ Subgroup.normalizer (W : Set Y) :=
    (iSup₂_le fun R' hR' => hR'.2 : MGrp Ω[R] W ≤ Subgroup.normalizer (W : Set Y)) hm
  have hmW : m * t * m⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hmN t).mp htW
  rcases A6Wt.mem_tG_W H fr hmW rfl with h | h | h
  · exact absurd h hmt
  · exact ⟨m, hm, h⟩
  ·
    obtain ⟨-, h3, -, c2, c3, c4⟩ := twins_facts H
    obtain ⟨e₃⟩ := members_q8_of_isPGroup hStd.perp h2g K₃ hd.hK₃.1
    have hq3 := WF.q8Facts_of_iso h3 e₃
    have ha3t : a₃ ≠ 1 ∧ a₃ ≠ t := by
      constructor
      · intro e; have := fr.o₃; rw [e, orderOf_one] at this; exact absurd this (by decide)
      · intro e
        have h2 : orderOf a₃ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [e, pow_two]; exact hq3.z_sq)
        rw [fr.o₃] at h2; exact absurd h2 (by decide)
    obtain ⟨r, hr, hrne⟩ := hq3.exists_noncomm a₃ fr.h₃.1 ha3t.1 ha3t.2
    have hcomm := hq3.comm_eq a₃ fr.h₃.1 r hr hrne
    have hra : r * a₃ * r⁻¹ = a₃ * t := by
      have hz : a₃ * r * a₃⁻¹ * r⁻¹ = t := hcomm
      have htc : t * r = r * t := hq3.z_central r hr
      have hta : a₃ * t = t * a₃ := (hq3.z_central a₃ fr.h₃.1).symm
      have hsq : a₃ * a₃ = t := Asc77.sq_eq_of_orderOf_four h3 fr.h₃.1 fr.o₃
      have ha3i : a₃⁻¹ = a₃ * t := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_assoc, hsq, hq3.z_sq]
      have h1 : r * a₃⁻¹ * r⁻¹ = a₃⁻¹ * t := by
        calc r * a₃⁻¹ * r⁻¹ = a₃⁻¹ * (a₃ * r * a₃⁻¹ * r⁻¹) := by group
          _ = a₃⁻¹ * t := by rw [hz]
      have h2 := congrArg (·⁻¹) h1
      simp only [mul_inv_rev, inv_inv] at h2
      calc r * a₃ * r⁻¹ = (r * a₃⁻¹ * r⁻¹)⁻¹ := by group
        _ = t⁻¹ * a₃ := by rw [h1]; group
        _ = t * a₃ := by rw [inv_eq_of_mul_eq_one_right hq3.z_sq]
        _ = a₃ * t := hta.symm
    have hrt : r * t * r⁻¹ = t := by rw [hq3.z_central r hr |>.symm, mul_inv_cancel_right]
    have hr1 : r * a₁ * r⁻¹ = a₁ := by
      rw [← c3 a₁ fr.h₁.1 r hr, mul_inv_cancel_right]
    have hr2 : r * a₂ * r⁻¹ = a₂ := by
      have : a₂ * r = r * a₂ := by
        have hK'K₃ := TC.Thin.twin_comm (CoreData.of_S hStd.perp.core).hyp h2g hd.hK'.1 hd.hK₃.1
          hd.hK₃K'.symm hd.hzK' h3
        exact hK'K₃ a₂ fr.h₂.1 r hr
      rw [← this, mul_inv_cancel_right]
    have hr4 : r * a₄ * r⁻¹ = a₄ := by
      have hz4 : IsUniqueInvolution K₄ t := Asc77.isUniqueInvolution_of_mem_twinSet hd.hz H.ex.2.1.1
      have : a₄ * r = r * a₄ := by
        have hK₄K₃ := TC.Thin.twin_comm (CoreData.of_S hStd.perp.core).hyp h2g H.ex.2.1.1.1 hd.hK₃.1
          H.ex.2.1.2.2.2.1 hz4 h3
        exact hK₄K₃ a₄ fr.h₄.1 r hr
      rw [← this, mul_inv_cancel_right]
    have hrM : r ∈ MGrp Ω[R] W := by
      unfold MGrp
      exact (le_iSup₂_of_le (f := fun R' (_ : R' ∈ DSet Ω[R] W) => R') K₃ H.hK₃ le_rfl) hr
    refine ⟨r * m, (MGrp Ω[R] W).mul_mem hrM hm, ?_⟩
    have hτ : y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄ := fr.hy
    calc r * m * t * (r * m)⁻¹ = r * (m * t * m⁻¹) * r⁻¹ := by group
      _ = r * (t * (y * t * y⁻¹)) * r⁻¹ := by rw [h]
      _ = (r * t * r⁻¹) * ((r * a₁ * r⁻¹) * (r * a₂ * r⁻¹) * (r * a₃ * r⁻¹) * (r * a₄ * r⁻¹)) := by
          rw [hτ]; group
      _ = t * (a₁ * a₂ * (a₃ * t) * a₄) := by rw [hrt, hr1, hr2, hra, hr4]
      _ = a₁ * a₂ * a₃ * a₄ * (t * t) := by
          have e1 : a₃ * t = t * a₃ := (hq3.z_central a₃ fr.h₃.1).symm
          have e2 : a₄ * t = t * a₄ := by
            obtain ⟨-, -, hz4', -, -, -⟩ := twins_facts H
            obtain ⟨e₄⟩ := members_q8_of_isPGroup hStd.perp h2g K₄ H.ex.2.1.1.1
            exact ((WF.q8Facts_of_iso hz4' e₄).z_central a₄ fr.h₄.1).symm
          have e3 : a₂ * t = t * a₂ := by
            obtain ⟨hz2', -, -, -, -, -⟩ := twins_facts H
            obtain ⟨e₂⟩ := members_q8_of_isPGroup hStd.perp h2g K' hd.hK'.1
            exact ((WF.q8Facts_of_iso hz2' e₂).z_central a₂ fr.h₂.1).symm
          have e4 : a₁ * t = t * a₁ := by
            obtain ⟨e₁⟩ := members_q8_of_isPGroup hStd.perp h2g K hd.mem
            exact ((WF.q8Facts_of_iso hd.hz e₁).z_central a₁ fr.h₁.1).symm
          have c1 : Commute t a₁ := e4.symm
          have c2 : Commute t a₂ := e3.symm
          have c3 : Commute t a₃ := e1.symm
          have c4 : Commute t a₄ := e2.symm
          have cP : Commute t (a₁ * a₂ * a₃ * a₄) := ((c1.mul_right c2).mul_right c3).mul_right c4
          calc t * (a₁ * a₂ * (a₃ * t) * a₄) = t * (a₁ * a₂ * a₃ * (t * a₄)) := by group
            _ = t * (a₁ * a₂ * a₃ * (a₄ * t)) := by rw [← e2]
            _ = (t * (a₁ * a₂ * a₃ * a₄)) * t := by group
            _ = ((a₁ * a₂ * a₃ * a₄) * t) * t := by rw [cP.eq]
            _ = a₁ * a₂ * a₃ * a₄ * (t * t) := by group
      _ = y * t * y⁻¹ := by rw [hd.hz.sq, mul_one, hτ]

theorem tau_edge (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    t ∈ ae6P Ω[R] (y * t * y⁻¹) ∧ y * t * y⁻¹ ∈ ae6P Ω[R] (y * t * y⁻¹) := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have hinv := conjInvariant_conjClass (tightCore R)
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  obtain ⟨m, hm, hmt⟩ := exists_M_conj_t_tau H fr
  obtain ⟨htP, hτP⟩ := t_tau_mem_ae6P H fr
  have hconj : conjSub m (ae6P Ω[R] t) = ae6P Ω[R] (y * t * y⁻¹) := by
    rw [ae6P_conj hinv, hmt]
  have hmN : m ∈ Subgroup.normalizer (W : Set Y) :=
    (iSup₂_le fun R' hR' => hR'.2 : MGrp Ω[R] W ≤ Subgroup.normalizer (W : Set Y)) hm
  have hτW : y * t * y⁻¹ ∈ W := by
    rw [fr.hy]
    exact W.mul_mem (W.mul_mem (W.mul_mem fr.h₁.2 fr.h₂.2) fr.h₃.2) fr.h₄.2
  have hmN' : m⁻¹ ∈ Subgroup.normalizer (W : Set Y) := Subgroup.inv_mem _ hmN
  have hw : m⁻¹ * t * m⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hmN' t).mp htW
  have hcls : m⁻¹ * t * m⁻¹⁻¹ ∈ ae6P Ω[R] t := by
    rcases A6Wt.mem_tG_W H fr hw rfl with h | h | h
    · rw [h]; exact htP
    · rw [h]; exact hτP
    · rw [h]; exact (ae6P Ω[R] t).mul_mem htP hτP
  refine ⟨?_, ?_⟩
  · rw [← hconj]
    have h0 : m * (m⁻¹ * t * m⁻¹⁻¹) * m⁻¹ ∈ conjSub m (ae6P Ω[R] t) := conj_mem_conjSub hcls
    have e : m * (m⁻¹ * t * m⁻¹⁻¹) * m⁻¹ = t := by group
    rwa [e] at h0
  · rw [← hconj, ← hmt]
    exact conj_mem_conjSub htP

theorem x_edge (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {h : Y}
    (hh : h ∈ Subgroup.centralizer ({t} : Set Y)) :
    t ∈ ae6P Ω[R] (h * (y * t * y⁻¹) * h⁻¹) ∧
      h * (y * t * y⁻¹) * h⁻¹ ∈ ae6P Ω[R] (h * (y * t * y⁻¹) * h⁻¹) := by
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨h1, h2⟩ := tau_edge H fr
  have hconj : conjSub h (ae6P Ω[R] (y * t * y⁻¹)) = ae6P Ω[R] (h * (y * t * y⁻¹) * h⁻¹) :=
    ae6P_conj hinv h _
  have hht : h * t * h⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    rw [hh, mul_inv_cancel_right]
  refine ⟨?_, ?_⟩
  · rw [← hconj]
    have h0 : h * t * h⁻¹ ∈ conjSub h (ae6P Ω[R] (y * t * y⁻¹)) := conj_mem_conjSub h1
    rwa [hht] at h0
  · rw [← hconj]
    exact conj_mem_conjSub h2

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Hx
