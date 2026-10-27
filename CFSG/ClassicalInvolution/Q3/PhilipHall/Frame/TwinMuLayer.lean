module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuClique
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuTab
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section Alg

variable {G : Type} [Group G]

theorem conj_ne {g x x' : G} (h : x ≠ x') : g * x * g⁻¹ ≠ g * x' * g⁻¹ := fun e =>
  h (mul_left_cancel (mul_right_cancel e))

theorem conj_commute {g x x' : G} (h : x * x' = x' * x) :
    (g * x * g⁻¹) * (g * x' * g⁻¹) = (g * x' * g⁻¹) * (g * x * g⁻¹) := by
  calc (g * x * g⁻¹) * (g * x' * g⁻¹) = g * (x * x') * g⁻¹ := by group
    _ = g * (x' * x) * g⁻¹ := by rw [h]
    _ = (g * x' * g⁻¹) * (g * x * g⁻¹) := by group

theorem plusplus {t w v s : G} (hfix : t * (w * v) * t⁻¹ = w * v) (e1 : t * w * t⁻¹ = s * w)
    (e2 : t * v * t⁻¹ = s * v) (hsw : s * w = w * s) : s * s = 1 := by
  have h1 : (t * w * t⁻¹) * (t * v * t⁻¹) = w * v := by
    rw [← hfix]; group
  rw [e1, e2] at h1
  have h2 : (s * w) * (s * v) = (s * s) * (w * v) := by
    calc (s * w) * (s * v) = s * (w * s) * v := by simp only [mul_assoc]
      _ = s * (s * w) * v := by rw [← hsw]
      _ = (s * s) * (w * v) := by simp only [mul_assoc]
  rw [h2] at h1
  have h3 : (s * s) * (w * v) = 1 * (w * v) := by rw [one_mul]; exact h1
  exact mul_right_cancel h3

theorem conj_inv_of {t k s : G} (h : t * k * t⁻¹ = s * k) (hks : k * s = s * k) :
    t * k⁻¹ * t⁻¹ = s⁻¹ * k⁻¹ := by
  calc t * k⁻¹ * t⁻¹ = (t * k * t⁻¹)⁻¹ := by group
    _ = (s * k)⁻¹ := by rw [h]
    _ = k⁻¹ * s⁻¹ := by rw [mul_inv_rev]
    _ = s⁻¹ * k⁻¹ := (Commute.inv_inv (show Commute k s from hks)).eq

end Alg

section Elt

variable {Q : Type*} [Group Q] {Δ : Set Q}

theorem not_conn_of_not_mem_cent (h : IsTT Δ) (hS : IsStar Δ) {d a s : Q} (hd : d ∈ Δ) (ha : a ∈ Δ)
    (hc : ¬ Conn Δ d a) (hsF : s ∉ cent Δ d) : ¬ Conn Δ d s := by
  intro hds
  apply hsF
  have key : ∀ y, Conn Δ d y → y ∈ cent Δ d := by
    intro y hy
    induction hy with
    | refl => exact self_mem_cent hd
    | @tail b c hdb hbc ih =>
      have hcb : c ∈ cent Δ b := ⟨hbc.2.1, hbc.2.2.symm⟩
      rwa [cent_eq_of_mem_cent h hS hd ha hc ih] at hcb
  exact key s hds

end Elt

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem frame_prod (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {ρa ρb ρc ρS : Rep Ω W}
    (hab : muTabElt ρa ≠ muTabElt ρb) (hac : muTabElt ρa ≠ muTabElt ρc)
    (hbc : muTabElt ρb ≠ muTabElt ρc)
    (cab : muTabElt ρa * muTabElt ρb = muTabElt ρb * muTabElt ρa)
    (cac : muTabElt ρa * muTabElt ρc = muTabElt ρc * muTabElt ρa)
    (cbc : muTabElt ρb * muTabElt ρc = muTabElt ρc * muTabElt ρb)
    (hconn : ¬ Conn (muDelta Ω W) (muTabElt ρa) (muTabElt ρS))
    {w zS za zb zc : G} (hw : w ∈ ρS.K ⊓ W) (hzS : IsUniqueInvolution ρS.K zS) (hw2 : w * w = zS)
    (hza : IsUniqueInvolution ρa.K za) (hzb : IsUniqueInvolution ρb.K zb)
    (hzc : IsUniqueInvolution ρc.K zc) :
    ∃ (ρd : Rep Ω W) (zd : G), Frame4 Ω W ρa ρb ρc ρd ∧ IsUniqueInvolution ρd.K zd ∧
      ρS.K ≠ ρd.K ∧ ρS.K ∉ omegaNbr Ω ρd.K ∧
      ∃ ka kb kc kd : G, ka ∈ ρa.K ⊓ W ∧ kb ∈ ρb.K ⊓ W ∧ kc ∈ ρc.K ⊓ W ∧ kd ∈ ρd.K ⊓ W ∧
        ka * ka = za ∧ kb * kb = zb ∧ kc * kc = zc ∧ kd * kd = zd ∧
        ρa.r * w * ρa.r⁻¹ = ka * w ∧ ρb.r * w * ρb.r⁻¹ = kb * w ∧ ρc.r * w * ρc.r⁻¹ = kc * w ∧
        ρd.r * w * ρd.r⁻¹ = kd * w ∧ ka * kb * kc * kd = zS := by
  classical
  have ctx := Q3CL.T8.ctxOf hP hW
  have hΩ := ctx.hΩ
  have hTT := Q3T6.Mu.isTT_muDelta hP hW
  have hS := Q3T6.Mu.isStar_muDelta ctx
  have hxa := muTabElt_mem ρa
  have hxb := muTabElt_mem ρb
  have hxc := muTabElt_mem ρc
  have hs := muTabElt_mem ρS
  have ha_c : muTabElt ρa ∈ cent (muDelta Ω W) (muTabElt ρa) := self_mem_cent hxa
  have hb_c : muTabElt ρb ∈ cent (muDelta Ω W) (muTabElt ρa) := ⟨hxb, cab.symm⟩
  have hc_c : muTabElt ρc ∈ cent (muDelta Ω W) (muTabElt ρa) := ⟨hxc, cac.symm⟩
  obtain ⟨xd, hd_c, nda, ndb, ndc, hxd⟩ :=
    exists_fourth hTT hS hxa hs hconn ha_c hb_c hc_c hab hac hbc
  have hxdΔ : xd ∈ muDelta Ω W := hd_c.1
  have hcl : ∀ u ∈ cent (muDelta Ω W) (muTabElt ρa), ∀ v ∈ cent (muDelta Ω W) (muTabElt ρa),
      u * v = v * u := fun u hu v hv => hTT.isClique_cent hS hxa hs hconn hu hv
  have cad : muTabElt ρa * xd = xd * muTabElt ρa := hcl _ ha_c _ hd_c
  have cbd : muTabElt ρb * xd = xd * muTabElt ρb := hcl _ hb_c _ hd_c
  have ccd : muTabElt ρc * xd = xd * muTabElt ρc := hcl _ hc_c _ hd_c
  have hcs : (xd * muTabElt ρc * muTabElt ρb * muTabElt ρa) * muTabElt ρS =
      muTabElt ρS * (xd * muTabElt ρc * muTabElt ρb * muTabElt ρa) := by
    rw [rev4 cab cac cad cbc cbd ccd]
    exact prod_comm (hTT.mul_self _ hs) (hTT.mul_self _ hxa) (hTT.mul_self _ hxb)
      (hTT.mul_self _ hxc) (hTT.mul_self _ hxdΔ) cab cac cbc cad cbd ccd hxd
  have hca : (xd * muTabElt ρc * muTabElt ρb * muTabElt ρa) * muTabElt ρa =
      muTabElt ρa * (xd * muTabElt ρc * muTabElt ρb * muTabElt ρa) := by
    have : Commute (xd * muTabElt ρc * muTabElt ρb * muTabElt ρa) (muTabElt ρa) :=
      (((show Commute xd (muTabElt ρa) from cad.symm).mul_left
        (show Commute (muTabElt ρc) (muTabElt ρa) from cac.symm)).mul_left
        (show Commute (muTabElt ρb) (muTabElt ρa) from cab.symm)).mul_left (Commute.refl _)
    exact this.eq
  have hg0 : (muTabElt ρa * muTabElt ρS) * muTabElt ρa * (muTabElt ρa * muTabElt ρS)⁻¹ =
      muTabElt ρS := conj_swap hTT hxa hs hconn
  have hgc : (muTabElt ρa * muTabElt ρS) * (xd * muTabElt ρc * muTabElt ρb * muTabElt ρa) *
      (muTabElt ρa * muTabElt ρS)⁻¹ = xd * muTabElt ρc * muTabElt ρb * muTabElt ρa :=
    conj_cent hca hcs
  generalize muTabElt ρa * muTabElt ρS = g at hg0 hgc
  obtain ⟨ρd, hρd⟩ := MuTab.exists_rep_of_mem_muDelta hxdΔ
  subst hρd
  obtain ⟨σb, hσb⟩ := MuTab.exists_rep_of_mem_muDelta
    (hTT.conj_mem' hxb g)
  obtain ⟨σc, hσc⟩ := MuTab.exists_rep_of_mem_muDelta
    (hTT.conj_mem' hxc g)
  obtain ⟨σd, hσd⟩ := MuTab.exists_rep_of_mem_muDelta
    (hTT.conj_mem' hxdΔ g)
  have hFρ : Frame4 Ω W ρa ρb ρc ρd :=
    Frame4.of_comm ctx hab hac nda.symm hbc ndb.symm ndc.symm cab cac cad cbc cbd ccd
  have e_a : muTabElt ρS = g * muTabElt ρa * g⁻¹ := hg0.symm
  have hFσ : Frame4 Ω W ρS σb σc σd := by
    refine Frame4.of_comm ctx ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [e_a, ← hσb]; exact conj_ne hab
    · rw [e_a, ← hσc]; exact conj_ne hac
    · rw [e_a, ← hσd]; exact conj_ne nda.symm
    · rw [← hσb, ← hσc]; exact conj_ne hbc
    · rw [← hσb, ← hσd]; exact conj_ne ndb.symm
    · rw [← hσc, ← hσd]; exact conj_ne ndc.symm
    · rw [e_a, ← hσb]; exact conj_commute cab
    · rw [e_a, ← hσc]; exact conj_commute cac
    · rw [e_a, ← hσd]; exact conj_commute cad
    · rw [← hσb, ← hσc]; exact conj_commute cbc
    · rw [← hσb, ← hσd]; exact conj_commute cbd
    · rw [← hσc, ← hσd]; exact conj_commute ccd
  have hL : piG W (ρd.r * ρc.r * ρb.r * ρa.r) =
      ((muTabElt ρd * muTabElt ρc * muTabElt ρb * muTabElt ρa : ↥(muGroup Ω W)) :
        NQuot (W ⊔ OCW W)) := by
    rw [piG_mul4 ρd.r_mem_normalizer ρc.r_mem_normalizer ρb.r_mem_normalizer
      ρa.r_mem_normalizer]
    rfl
  have hR : piG W (σd.r * σc.r * σb.r * ρS.r) =
      ((muTabElt σd * muTabElt σc * muTabElt σb * muTabElt ρS : ↥(muGroup Ω W)) :
        NQuot (W ⊔ OCW W)) := by
    rw [piG_mul4 σd.r_mem_normalizer σc.r_mem_normalizer σb.r_mem_normalizer
      ρS.r_mem_normalizer]
    rfl
  have hcen : piG W (ρd.r * ρc.r * ρb.r * ρa.r) = piG W (σd.r * σc.r * σb.r * ρS.r) := by
    rw [hL, hR, ← hσd, ← hσc, ← hσb, e_a]
    congr 1
    calc muTabElt ρd * muTabElt ρc * muTabElt ρb * muTabElt ρa
        = g * (muTabElt ρd * muTabElt ρc * muTabElt ρb * muTabElt ρa) * g⁻¹ := hgc.symm
      _ = _ := by group
  have hnc : ∀ {α : Rep Ω W}, muTabElt α ∈ cent (muDelta Ω W) (muTabElt ρa) →
      muTabElt α * muTabElt ρS ≠ muTabElt ρS * muTabElt α := by
    intro α hα h
    exact hconn ((conn_of_mem_cent hxa hα).trans (conn_of_commute hα.1 hs h))
  have nta := not_adj_of_noncomm ctx (hnc ha_c)
  have ntb := not_adj_of_noncomm ctx (hnc hb_c)
  have ntc := not_adj_of_noncomm ctx (hnc hc_c)
  have ntd := not_adj_of_noncomm ctx (hnc hd_c)
  obtain ⟨zd, hzd⟩ := Sec6Gen.exists_uniqueInvolution hΩ ρd.hK
  obtain ⟨ka, kb, kc, kd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    frame_prod_gen ctx hFρ hFσ hcen nta.1 ntb.1 ntc.1 ntd.1 nta.2 ntb.2 ntc.2 ntd.2 hw hzS hw2
      hza hzb hzc hzd
  exact ⟨ρd, zd, hFρ, hzd, ntd.1, ntd.2, ka, kb, kc, kd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13⟩

theorem piG_mul3 {a b c : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (hb : b ∈ Subgroup.normalizer (W : Set G)) (hc : c ∈ Subgroup.normalizer (W : Set G)) :
    piG W (a * b * c) = piG W a * piG W b * piG W c := by
  rw [piG_mul (Subgroup.mul_mem _ ha hb) hc, piG_mul ha hb]

theorem cyc_inf (ctx : Q3CL.Thompson.Ctx Ω W) (α : Rep Ω W) : IsCyclic ↥(α.K ⊓ W) := by
  have hinf := Q3CL.Thompson.inf_W_of_mem_D ctx.hΩ ctx.hW α.hR α.hK α.hRK
  have h := hinf.2.2.1
  rwa [hinf.1] at h

theorem comm_comm (ctx : Q3CL.Thompson.Ctx Ω W) {α β : Rep Ω W} (hne : β.K ≠ α.K)
    (hnot' : α.K ∉ omegaNbr Ω β.K)
    (hbraid : piG W (β.r * α.r * β.r) = piG W (α.r * β.r * α.r))
    {w k zα zβ : G} (hw : w ∈ β.K ⊓ W) (hzβ : IsUniqueInvolution β.K zβ) (hw2 : w * w = zβ)
    (hzα : IsUniqueInvolution α.K zα) (hk : k ∈ α.K ⊓ W) (hk2 : k * k = zα)
    (hrel : α.r * w * α.r⁻¹ = k * w) : β.r * k * β.r⁻¹ = w * k := by
  have hΩ := ctx.hΩ
  have hcW := ctx.comm_W
  have he : β.r * k * β.r⁻¹ * k⁻¹ ∈ β.K ⊓ W := ctx.comm_mem β α hne hk
  have he2 : (β.r * k * β.r⁻¹ * k⁻¹) * (β.r * k * β.r⁻¹ * k⁻¹) = zβ :=
    ctx.comm_sq β α hne hnot' hk hzβ hzα hk2
  have hzz : (w * w) * (w * w) = 1 := by rw [hw2]; exact hzβ.sq
  have hw1 : w * w ≠ 1 := by rw [hw2]; exact hzβ.ne_one
  have hew : (β.r * k * β.r⁻¹ * k⁻¹) * w = w * (β.r * k * β.r⁻¹ * k⁻¹) :=
    hcW _ he.2 _ hw.2
  rcases eq_or_inv (cyc_inf ctx β) he hw hew (he2.trans hw2.symm) hzz hw1 with h | h
  · calc β.r * k * β.r⁻¹ = (β.r * k * β.r⁻¹ * k⁻¹) * k := by group
      _ = w * k := by rw [h]
  · exfalso
    have hBc : β.r * k * β.r⁻¹ = w⁻¹ * k := by
      calc β.r * k * β.r⁻¹ = (β.r * k * β.r⁻¹ * k⁻¹) * k := by group
        _ = w⁻¹ * k := by rw [h]
    have hBAB : β.r * α.r * β.r ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ β.r_mem_normalizer α.r_mem_normalizer)
        β.r_mem_normalizer
    have hABA : α.r * β.r * α.r ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ α.r_mem_normalizer β.r_mem_normalizer)
        α.r_mem_normalizer
    have hPconj := Q3CL.Thompson.conj_eq_of_piG_eq hΩ ctx.hW hBAB hABA hbraid hk.2
    have := braid_contra (A := α.r) (B := β.r) (c := k) (w := w) (z := zα) hrel
      (ctx.conj_inv α hk) (ctx.conj_inv β hw) hBc (hcW _ hk.2 _ hw.2) hk2 hzα.sq hPconj
    exact hw1 this

@[expose] def cdSub (Ω : Set (Subgroup G)) (W : Subgroup G) (x : G) : Subgroup G :=
  ⨆ T ∈ {T : Subgroup G | T ∈ DSet Ω W ∧ T ≤ Subgroup.centralizer ({x} : Set G)}, T

theorem le_cdSub {T : Subgroup G} {x : G} (hT : T ∈ DSet Ω W)
    (h : T ≤ Subgroup.centralizer ({x} : Set G)) : T ≤ cdSub Ω W x :=
  le_iSup₂_of_le T ⟨hT, h⟩ le_rfl

theorem layer_mem (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {ρa ρb ρc ρS : Rep Ω W}
    (hab : muTabElt ρa ≠ muTabElt ρb) (hac : muTabElt ρa ≠ muTabElt ρc)
    (hbc : muTabElt ρb ≠ muTabElt ρc)
    (cab : muTabElt ρa * muTabElt ρb = muTabElt ρb * muTabElt ρa)
    (cac : muTabElt ρa * muTabElt ρc = muTabElt ρc * muTabElt ρa)
    (cbc : muTabElt ρb * muTabElt ρc = muTabElt ρc * muTabElt ρb)
    (hconn : ¬ Conn (muDelta Ω W) (muTabElt ρa) (muTabElt ρS))
    {w v za zb zc : G} (hwa : w ∈ ρa.K ⊓ W) (hvb : v ∈ ρb.K ⊓ W)
    (hza : IsUniqueInvolution ρa.K za) (hzb : IsUniqueInvolution ρb.K zb)
    (hzc : IsUniqueInvolution ρc.K zc) (hw2 : w * w = za) (hv2 : v * v = zb)
    (hS : ρS.R ≤ Subgroup.centralizer ({w * v} : Set G)) :
    w * v⁻¹ ∈ cdSub Ω W (w * v) ∨ w⁻¹ * v ∈ cdSub Ω W (w * v) := by
  classical
  have ctx := Q3CL.T8.ctxOf hP hW
  have hΩ := ctx.hΩ
  have hcW := ctx.comm_W
  have hTT := Q3T6.Mu.isTT_muDelta hP hW
  have hxa := muTabElt_mem ρa
  have hxb := muTabElt_mem ρb
  have hs := muTabElt_mem ρS
  obtain ⟨ws, hws, hws4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hW ρS.hR
  have hwsK : ws ∈ ρS.K ⊓ W := ⟨ρS.hRK.1 hws.1, hws.2⟩
  obtain ⟨zS, hzS⟩ := Sec6Gen.exists_uniqueInvolution hΩ ρS.hK
  have hws2 : ws * ws = zS := sq_eq_involution_of_orderOf_four hzS hwsK.1 hws4
  obtain ⟨ρd, zd, hF, hzd, -, -, ka, kb, kc, kd, mka, mkb, mkc, mkd, sa, sb, sc, sd, ra, rb, rc, rd,
    hprod⟩ := frame_prod hP hW hab hac hbc cab cac cbc hconn hwsK hzS hws2 hza hzb hzc
  have hnca : muTabElt ρa * muTabElt ρS ≠ muTabElt ρS * muTabElt ρa := fun h =>
    hconn (conn_of_commute hxa hs h)
  have hncb : muTabElt ρb * muTabElt ρS ≠ muTabElt ρS * muTabElt ρb := fun h =>
    hconn ((conn_of_mem_cent hxa (show muTabElt ρb ∈ cent (muDelta Ω W) (muTabElt ρa) from
      ⟨hxb, cab.symm⟩)).trans (conn_of_commute hxb hs h))
  have nta := not_adj_of_noncomm ctx hnca
  have ntb := not_adj_of_noncomm ctx hncb
  have nta' := not_adj_of_noncomm ctx (α := ρS) (β := ρa) (fun h => hnca h.symm)
  have ntb' := not_adj_of_noncomm ctx (α := ρS) (β := ρb) (fun h => hncb h.symm)
  have hNa := ρa.r_mem_normalizer
  have hNb := ρb.r_mem_normalizer
  have hNS := ρS.r_mem_normalizer
  have hbraid_a : piG W (ρS.r * ρa.r * ρS.r) = piG W (ρa.r * ρS.r * ρa.r) := by
    rw [piG_mul3 hNS hNa hNS, piG_mul3 hNa hNS hNa]
    exact congrArg Subtype.val (hTT.braid hs hxa (fun h => hnca h.symm))
  have hbraid_b : piG W (ρS.r * ρb.r * ρS.r) = piG W (ρb.r * ρS.r * ρb.r) := by
    rw [piG_mul3 hNS hNb hNS, piG_mul3 hNb hNS hNb]
    exact congrArg Subtype.val (hTT.braid hs hxb (fun h => hncb h.symm))
  have eA : ρS.r * ka * ρS.r⁻¹ = ws * ka :=
    comm_comm ctx nta.1 nta'.2 hbraid_a hwsK hzS hws2 hza mka sa ra
  have eB : ρS.r * kb * ρS.r⁻¹ = ws * kb :=
    comm_comm ctx ntb.1 ntb'.2 hbraid_b hwsK hzS hws2 hzb mkb sb rb
  have hwc : w = ka ∨ w = ka⁻¹ := by
    refine eq_or_inv (cyc_inf ctx ρa) hwa mka (hcW _ hwa.2 _ mka.2) (hw2.trans sa.symm) ?_ ?_
    · rw [sa]; exact hza.sq
    · rw [sa]; exact hza.ne_one
  have hvc : v = kb ∨ v = kb⁻¹ := by
    refine eq_or_inv (cyc_inf ctx ρb) hvb mkb (hcW _ hvb.2 _ mkb.2) (hv2.trans sb.symm) ?_ ?_
    · rw [sb]; exact hzb.sq
    · rw [sb]; exact hzb.ne_one
  have hfix : ρS.r * (w * v) * ρS.r⁻¹ = w * v := by
    have h1 : ρS.r * (w * v) = (w * v) * ρS.r :=
      Subgroup.mem_centralizer_singleton_iff.mp (hS ρS.hr)
    rw [h1]; group
  have hsw : ws * w = w * ws := (hcW _ hwsK.2 _ hwa.2)
  have hskw : ka * ws = ws * ka := hcW _ mka.2 _ hws.2
  have hskb : kb * ws = ws * kb := hcW _ mkb.2 _ hws.2
  have hzSne : ws * ws ≠ 1 := by rw [hws2]; exact hzS.ne_one
  have hjW : w * v ∈ W := W.mul_mem hwa.2 hvb.2
  have hcentD : ∀ ρ : Rep Ω W, ρa.K ∈ omegaNbr Ω ρ.K → ρb.K ∈ omegaNbr Ω ρ.K →
      ρ.R ≤ Subgroup.centralizer ({w * v} : Set G) := by
    intro ρ h1 h2
    refine Q3CL.Thompson.le_centralizer_of_mem hΩ hW ρ.hR ρ.hr ρ.hrW hjW ?_
    have e1 : ρ.r * w = w * ρ.r := ctx.centralizes ρ ρa h1 hwa
    have e2 : ρ.r * v = v * ρ.r := ctx.centralizes ρ ρb h2 hvb
    calc ρ.r * (w * v) = (ρ.r * w) * v := by simp only [mul_assoc]
      _ = (w * ρ.r) * v := by rw [e1]
      _ = w * (ρ.r * v) := by simp only [mul_assoc]
      _ = w * (v * ρ.r) := by rw [e2]
      _ = (w * v) * ρ.r := by simp only [mul_assoc]
  have hRc := le_cdSub ρc.hR (hcentD ρc hF.ca hF.cb)
  have hRd := le_cdSub ρd.hR (hcentD ρd hF.da hF.db)
  have hRS := le_cdSub ρS.hR hS
  have hkcR : kc ∈ ρc.R := by
    have h1 := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW ρc.hR ρc.hK ρc.hRK).1
    have : kc ∈ ρc.R ⊓ W := by rw [h1]; exact mkc
    exact this.1
  have hkdR : kd ∈ ρd.R := by
    have h1 := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW ρd.hR ρd.hK ρd.hRK).1
    have : kd ∈ ρd.R ⊓ W := by rw [h1]; exact mkd
    exact this.1
  have hzSR : zS ∈ ρS.R := by rw [← hws2]; exact ρS.R.mul_mem hws.1 hws.1
  have hX : ka * kb ∈ cdSub Ω W (w * v) := by
    have e : ka * kb = zS * kd⁻¹ * kc⁻¹ := by
      calc ka * kb = (ka * kb * kc * kd) * kd⁻¹ * kc⁻¹ := by group
        _ = zS * kd⁻¹ * kc⁻¹ := by rw [hprod]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hRS hzSR) (Subgroup.inv_mem _ (hRd hkdR)))
      (Subgroup.inv_mem _ (hRc hkcR))
  rcases hwc with hw1 | hw1 <;> rcases hvc with hv1 | hv1
  ·
    exfalso
    have e1 : ρS.r * w * ρS.r⁻¹ = ws * w := by rw [hw1]; exact eA
    have e2 : ρS.r * v * ρS.r⁻¹ = ws * v := by rw [hv1]; exact eB
    exact hzSne (plusplus hfix e1 e2 hsw)
  ·
    left
    have e : w * v⁻¹ = ka * kb := by rw [hw1, hv1, inv_inv]
    rw [e]
    exact hX
  ·
    right
    have e : w⁻¹ * v = ka * kb := by rw [hw1, hv1, inv_inv]
    rw [e]
    exact hX
  ·
    exfalso
    have e1 : ρS.r * w * ρS.r⁻¹ = ws⁻¹ * w := by rw [hw1]; exact conj_inv_of eA hskw
    have e2 : ρS.r * v * ρS.r⁻¹ = ws⁻¹ * v := by rw [hv1]; exact conj_inv_of eB hskb
    have hsw' : ws⁻¹ * w = w * ws⁻¹ := (Commute.inv_left (show Commute ws w from hsw)).eq
    have h := plusplus hfix e1 e2 hsw'
    apply hzSne
    have : (ws * ws)⁻¹ = 1 := by rw [mul_inv_rev]; exact h
    exact inv_eq_one.mp this

theorem perm_four_twin (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) (hnc : ¬ DbarConnected Ω W)
    {ρa ρb ρc : Rep Ω W} (hab : muTabElt ρa ≠ muTabElt ρb) (hac : muTabElt ρa ≠ muTabElt ρc)
    (hbc : muTabElt ρb ≠ muTabElt ρc)
    (cab : muTabElt ρa * muTabElt ρb = muTabElt ρb * muTabElt ρa)
    (cac : muTabElt ρa * muTabElt ρc = muTabElt ρc * muTabElt ρa)
    {w v : G} (hw : w ∈ ρa.R ⊓ W) (hv : v ∈ ρb.R ⊓ W) (hw4 : orderOf w = 4) (hv4 : orderOf v = 4) :
    ∃ ψ : ↥(Subgroup.closure (muDeltaCent Ω W (w * v))) ≃* Equiv.Perm (Fin 4),
      ∀ (x : ↥(muGroup Ω W)) (hx : x ∈ Subgroup.closure (muDeltaCent Ω W (w * v))),
        x ∈ muDeltaCent Ω W (w * v) ↔ (ψ ⟨x, hx⟩).IsSwap := by
  classical
  have ctx := Q3CL.T8.ctxOf hP hW
  have hΩ := ctx.hΩ
  have hTT := Q3T6.Mu.isTT_muDelta hP hW
  have hS := Q3T6.Mu.isStar_muDelta ctx
  have hxa := muTabElt_mem ρa
  have hxb := muTabElt_mem ρb
  have hxc := muTabElt_mem ρc
  obtain ⟨a, haΔ, hconna⟩ := Q3T6.Mu.exists_not_conn_at hP hW hnc (muTabElt ρa)
  have hk : (cent (muDelta Ω W) (muTabElt ρa)).ncard = 4 := by
    have hsub : ({muTabElt ρa, muTabElt ρb, muTabElt ρc} : Set ↥(muGroup Ω W)) ⊆
        cent (muDelta Ω W) (muTabElt ρa) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact self_mem_cent hxa
      · exact ⟨hxb, cab.symm⟩
      · exact ⟨hxc, cac.symm⟩
    have h3 : ({muTabElt ρa, muTabElt ρb, muTabElt ρc} : Set ↥(muGroup Ω W)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rcases Q3T8.Asc77.thompsonClique G Ω hP W hW hnc (muTabElt ρa) hxa with h | h | ⟨h, -⟩
    · omega
    · omega
    · exact h
  have hDC : DComm W ρa.R ρb.R :=
    Q3T8.Asc77.Thompson.dComm_of_commute hΩ hW ρa.hR ρb.hR ρa.hr ρb.hr ρa.hrW ρb.hrW
      (congrArg Subtype.val cab) (fun h => hab (Subtype.ext h))
  exact Q3T8.Asc77.Thompson.exists_perm_four_of_wv ctx hTT hS ρa.hR ρb.hR hDC ρa.hr
    ρa.hrW (d := muTabElt ρa) (a := a) rfl hxa haΔ hconna hk hw hv hw4 hv4

theorem exists_S (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) (hnc : ¬ DbarConnected Ω W)
    {ρa ρb ρc : Rep Ω W} (hab : muTabElt ρa ≠ muTabElt ρb) (hac : muTabElt ρa ≠ muTabElt ρc)
    (hbc : muTabElt ρb ≠ muTabElt ρc)
    (cab : muTabElt ρa * muTabElt ρb = muTabElt ρb * muTabElt ρa)
    (cac : muTabElt ρa * muTabElt ρc = muTabElt ρc * muTabElt ρa)
    {w v : G} (hw : w ∈ ρa.R ⊓ W) (hv : v ∈ ρb.R ⊓ W) (hw4 : orderOf w = 4) (hv4 : orderOf v = 4) :
    ∃ ρS : Rep Ω W, ρS.R ≤ Subgroup.centralizer ({w * v} : Set G) ∧
      ¬ Conn (muDelta Ω W) (muTabElt ρa) (muTabElt ρS) := by
  classical
  have ctx := Q3CL.T8.ctxOf hP hW
  have hTT := Q3T6.Mu.isTT_muDelta hP hW
  have hS := Q3T6.Mu.isStar_muDelta ctx
  have hxa := muTabElt_mem ρa
  obtain ⟨a, haΔ, hconna⟩ := Q3T6.Mu.exists_not_conn_at hP hW hnc (muTabElt ρa)
  obtain ⟨ψ, hψ⟩ := perm_four_twin hP hW hnc hab hac hbc cab cac hw hv hw4 hv4
  have hex : ∃ y ∈ muDeltaCent Ω W (w * v), y ∉ cent (muDelta Ω W) (muTabElt ρa) := by
    by_contra hcon
    push Not at hcon
    have hsw : ∀ i j : Fin 4, i ≠ j →
        (↑(ψ.symm (Equiv.swap i j)) : ↥(muGroup Ω W)) ∈ muDeltaCent Ω W (w * v) := by
      intro i j hij
      rw [hψ _ (ψ.symm (Equiv.swap i j)).2]
      simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
      exact ⟨i, j, hij, rfl⟩
    have hc1 := hcon _ (hsw 0 1 (by decide))
    have hc2 := hcon _ (hsw 0 2 (by decide))
    have hcomm : ψ.symm (Equiv.swap 0 1) * ψ.symm (Equiv.swap 0 2) =
        ψ.symm (Equiv.swap 0 2) * ψ.symm (Equiv.swap 0 1) :=
      Subtype.ext (hTT.isClique_cent hS hxa haΔ hconna hc1 hc2)
    have h := congrArg ψ hcomm
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    exact absurd h (by decide)
  obtain ⟨y, hyC, hyF⟩ := hex
  obtain ⟨R, hR, r, hr, hrW, hyr⟩ := hyC
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1.1
  let ρS : Rep Ω W := ⟨K, R, r, hK, hR.1, hRK, hr, hrW⟩
  have hy' : muTabElt ρS = y := Subtype.ext hyr.symm
  refine ⟨ρS, hR.2, ?_⟩
  rw [hy']
  exact not_conn_of_not_mem_cent hTT hS hxa haΔ hconna hyF

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
