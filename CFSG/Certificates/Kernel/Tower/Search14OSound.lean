module

public import Certificates.Data.Kernel.Tower.Search14O
public import CFSG.Certificates.Kernel.Tower.Search14Sound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower

variable {X : Type*} [Group X] {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}

theorem s14_tg {HL nq t u1 u2 v o : Nat} {TG : Nat → Nat}
    (h : e14Tg mul HL TG nq t u1 u2 v o = true) :
    Nat.land o 1023 < nq ∧ Nat.shiftRight o 10 < 256 ∧
      TG (Nat.land o 1023) = e14Im t u1 u2 (l16 (TG (Nat.land o 1023)) 3) ∧
      mul (l16 HL (Nat.shiftRight o 10)) u1 = mul u1 (l16 HL (Nat.shiftRight o 10)) ∧
      mul (l16 HL (Nat.shiftRight o 10)) u2 = mul u2 (l16 HL (Nat.shiftRight o 10)) ∧
      mul (l16 HL (Nat.shiftRight o 10)) v =
        mul (l16 (TG (Nat.land o 1023)) 3) (l16 HL (Nat.shiftRight o 10)) := by
  simp only [e14Tg, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1.1.1.1, Nat.le_of_ble_eq_true h.1.1.1.1.2,
    Nat.eq_of_beq_eq_true h.1.1.1.2, Nat.eq_of_beq_eq_true h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

theorem e14_complete {n : Nat} (hn : n = 16384) (M : IsModel (⊤ : Subgroup X) n mul dec)
    {GS PT t : Nat} (hT : treeB n 4 mul GS PT = true)
    {OT LB RP CZ HL GI KY PV CL1 CL2 CL3 RK1 RK2 RK3 R1 W1 R2 : Nat} {W2 SP TG : Nat → Nat}
    {nl c1 c2 c3 n1 n2 f nq : Nat}
    (hord : ordOK n mul OT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hcz : czOK16 n LB CZ = true) (hH : hOK16 n mul t HL = true)
    (hky : kyOK mul OT LB CZ GS KY PV = true)
    (hc1 : cmOK16 n mul t OT LB CZ (kyL KY 0) CL1 RK1 c1 = true)
    (hc2 : cmOK16 n mul t OT LB CZ (kyL KY 1) CL2 RK2 c2 = true)
    (hc3 : cmOK16 n mul t OT LB CZ (kyL KY 2) CL3 RK3 c3 = true)
    (h1 : e14Lvl1 n mul HL CL1 c1 R1 W1 n1 = true)
    (h2 : allB n1 (fun r1 => e14Lvl2 n mul OT LB CZ t HL CL2 c2 R1 R2 (pvL PV 0) n2 (W2 r1) r1) = true)
    (h3 : allB n2 (fun r2 => e14Lvl3O mul OT LB CZ t HL GS PT f R1 R2 (pvL PV 1) (pvL PV 2) TG nq
      CL3 c3 (SP r2) r2) = true)
    (htg : allB nq (fun q => Nat.blt (l16 (TG q) 3) n) = true)
    (β : MulAut X) (hβ : β (dec (l16 GS 0)) = dec t) :
    ∃ h : X, h * dec t = dec t * h ∧ ∃ q < nq, ∀ i < 4,
      h * β (dec (l16 GS i)) * h⁻¹ = dec (l16 (TG q) i) := by
  have hn' : n < 32768 := by omega
  obtain ⟨ht, hHL⟩ := s14_hParts hH
  obtain ⟨-, -, k2, -, p1, p2⟩ := s14_kyParts hky
  have hg : ∀ i < 4, l16 GS i < n := fun i hi => treeB_gen hT hi
  obtain ⟨h, hht, r2, hr2, hu1, hu2, e1, e2⟩ :=
    s14_lvl12 M hn' hT hord hlab hcz hH hky hc1 hc2 h1 h2 β hβ
  obtain ⟨γ, hγ⟩ : ∃ γ : MulAut X, ∀ x, γ x = h * β x * h⁻¹ :=
    ⟨MulAut.conj h * β, fun x => by rw [MulAut.mul_apply, MulAut.conj_apply]⟩
  have g0 : γ (dec (l16 GS 0)) = dec t := by rw [hγ, hβ, hht, mul_inv_cancel_right]
  have g1 : γ (dec (l16 GS 1)) = dec (l16 R1 (e14P1 R2 r2)) := by rw [hγ, e1]
  have g2 : γ (dec (l16 GS 2)) = dec (e14P2 R2 r2) := by rw [hγ, e2]
  obtain ⟨v, hv, hdv⟩ : ∃ v < n, dec v = γ (dec (l16 GS 3)) :=
    ⟨_, M.code_lt (Subgroup.mem_top _), M.dec_code (Subgroup.mem_top _)⟩
  have hK : ivOf mul OT LB CZ t v = kyL KY 2 := by
    rw [k2]
    exact s14_ivOf_aut M hn' hT hlab hord hcz γ (hg 0 (by norm_num)) (hg 3 (by norm_num)) ht hv
      g0.symm hdv
  have hP13 : pvOf16 mul OT LB CZ t (l16 R1 (e14P1 R2 r2)) v = pvL PV 1 := by
    rw [p1]
    exact s14_pvOf_aut M hn' hT hlab hord hcz γ (hg 0 (by norm_num)) (hg 1 (by norm_num))
      (hg 3 (by norm_num)) ht hu1 hv g0.symm g1.symm hdv
  have hP23 : pvOf16 mul OT LB CZ t (e14P2 R2 r2) v = pvL PV 2 := by
    rw [p2]
    exact s14_pvOf_aut M hn' hT hlab hord hcz γ (hg 0 (by norm_num)) (hg 2 (by norm_num))
      (hg 3 (by norm_num)) ht hu2 hv g0.symm g2.symm hdv
  obtain ⟨hk3, hcl3⟩ := s14_cand hc3 hv hK
  have hl3 : e14Lvl3O mul OT LB CZ t HL GS PT f R1 R2 (pvL PV 1) (pvL PV 2) TG nq CL3 c3 (SP r2)
      r2 = true := allB_eq_true.1 h3 r2 hr2
  have hv3 : (!Nat.beq (pvOf16 mul OT LB CZ t (l16 R1 (e14P1 R2 r2)) (l16 CL3 (rkL RK3 v)))
        (pvL PV 1) ||
      !Nat.beq (pvOf16 mul OT LB CZ t (e14P2 R2 r2) (l16 CL3 (rkL RK3 v))) (pvL PV 2) ||
      e14Oc mul HL GS PT f TG nq t (l16 R1 (e14P1 R2 r2)) (e14P2 R2 r2) (l16 CL3 (rkL RK3 v))
        (lane (SP r2) 32 4294967295 (rkL RK3 v))) = true := allB_eq_true.1 hl3 _ hk3
  rw [hcl3, hP13, hP23] at hv3
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at hv3
  generalize lane (SP r2) 32 4294967295 (rkL RK3 v) = o at hv3
  generalize hU1 : l16 R1 (e14P1 R2 r2) = u1 at hu1 g1 hv3 e1
  generalize hU2 : e14P2 R2 r2 = u2 at hu2 g2 hv3 e2
  unfold e14Oc at hv3
  cases hb : Nat.beq (Nat.land o 1) 0
  · rw [hb, cond_false, Bool.and_eq_true] at hv3
    have hIM := s14_im M (by omega) ht hu1 hu2 hv γ g0 g1 g2 hdv.symm
    have hx : Nat.land (Nat.shiftRight o 1) 16383 < n :=
      lt_of_le_of_lt Nat.and_le_right (by omega)
    rw [s14_sp_false M hT γ hIM hx (Nat.le_of_ble_eq_true hv3.1)] at hv3
    exact absurd hv3.2 Bool.false_ne_true
  · rw [hb, cond_true] at hv3
    obtain ⟨hq, hi, hTG, hc1', hc2', hc3'⟩ := s14_tg hv3
    generalize Nat.land (Nat.shiftRight o 1) 1023 = q at hq hTG hc3'
    generalize Nat.shiftRight (Nat.shiftRight o 1) 10 = i at hi hc1' hc2' hc3'
    have hw : l16 (TG q) 3 < n := Nat.le_of_ble_eq_true (allB_eq_true.1 htg q hq)
    generalize l16 (TG q) 3 = w at hw hTG hc3'
    obtain ⟨hH3, hH3t⟩ := hHL i hi
    have c3 := s14_conj_eq M hH3 hv hw hc3'
    have cu1 := s14_conj_eq M hH3 hu1 hu1 hc1'
    have cu2 := s14_conj_eq M hH3 hu2 hu2 hc2'
    have ct3 := s14_conj_eq M hH3 ht ht hH3t
    obtain ⟨a0, a1, a2, a3⟩ := s14_e14Im (t := t) (u1 := u1) (u2 := u2) (v := w) (by omega)
      (by omega) (by omega) (by omega)
    refine ⟨dec (l16 HL i) * h, ?_, q, hq, fun k hk => ?_⟩
    · rw [← mul_inv_eq_iff_eq_mul, s14_conj_mul, hht, mul_inv_cancel_right, ct3]
    · rw [hTG, s14_conj_mul, ← hγ]
      interval_cases k
      · rw [a0, g0, ct3]
      · rw [a1, g1, cu1]
      · rw [a2, g2, cu2]
      · rw [a3, ← hdv, c3]

end Certificates.KernelTower

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

theorem l2Facts_of_l3 {X : Type*} [Group X] {t x₀ : X} (Q : Subgroup X) (hN : Q.Normal)
    (hQ : Q.index = 2) (htQ : t ∉ Q) (hxQ : x₀ ∉ Q) (hcls : ∀ x, IsPInv x → Conj x t ∨ Conj x x₀)
    (hL3 : ∀ D : ExtData X, D.α x₀ = t →
      Nat.card (centralizer {CycExt.incl D t} : Subgroup (CycExt D)) = 2 ^ 8 →
        L3Facts (CycExt D) (CycExt.incl D t)) : L2Facts X t := by
  refine ⟨Q, hQ, htQ, fun x hx hP => ?_, x₀, hcls, Or.inr hL3⟩
  rcases hcls x hP with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h := hN.conj_mem _ hx k⁻¹
    have e : k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t := by group
    rw [e] at h
    exact htQ h
  · have h := hN.conj_mem _ hx k⁻¹
    have e : k⁻¹ * (k * x₀ * k⁻¹) * k⁻¹⁻¹ = x₀ := by group
    rw [e] at h
    exact hxQ h

end CFSG.OddStandard.AltStdSmall4.Tower
