module

public import Certificates.Data.Kernel.Misc.RuCov
public import Certificates.Data.Kernel.Misc.RuCovB
public import CFSG.Certificates.Kernel.Misc.RuScanSound

public section

namespace CFSG.KC.Misc.RuCov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan
  CFSG.KC.Misc.RuBase

theorem conjOK_sound {ss cs : List Nat} {gs hs : List (Equiv.Perm (Fin 4060))} (h1 : PL ss gs)
    (h2 : PL cs hs) {R : Nat} {ρ : Equiv.Perm (Fin 4060)} (hR : PRep 4060 12 R ρ)
    (h : conjOK ss cs R = true) :
    ∀ b (hb : b < 4), hs.prod (gs.prod ⟨b, by omega⟩) = ρ (hs.prod ⟨b, by omega⟩) := by
  intro b hb
  unfold conjOK at h
  have e := Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 h b hb)
  have e1 : yAp ss b = (gs.prod ⟨b, by omega⟩ : Nat) := yAp_eq h1 ⟨b, by omega⟩
  have e2 : yAp cs b = (hs.prod ⟨b, by omega⟩ : Nat) := yAp_eq h2 ⟨b, by omega⟩
  rw [e1, e2, yAp_eq h2, apP_eq hR] at e
  exact Fin.ext e

theorem kind0_sound {ys : List Nat} {gs : List (Equiv.Perm (Fin 4060))} (h : PL ys gs) {x : Nat}
    (hx : (if Nat.blt x 4060 = true then
      (if Nat.beq (yAp ys (yAp ys x)) x = true then false else true) else false) = true) :
    ∃ y : Fin 4060, gs.prod (gs.prod y) ≠ y := by
  split_ifs at hx with h1 h2
  have hlt := Nat.blt_eq.mp h1
  refine ⟨⟨x, hlt⟩, fun e => h2 ?_⟩
  have e1 : yAp ys x = (gs.prod ⟨x, hlt⟩ : Nat) := yAp_eq h ⟨x, hlt⟩
  rw [e1, yAp_eq h, e]
  exact Nat.beq_eq.mpr rfl

theorem recK_sound {ys : List Nat} {gs : List (Equiv.Perm (Fin 4060))} (h : PL ys gs) {T : Nat}
    {τ : Equiv.Perm (Fin 4060)} (hT : PRep 4060 12 T τ) {K3 : List Nat → Nat → Bool} {r : Nat}
    (hr : recK ys T K3 r = true) :
    (∃ y : Fin 4060, gs.prod (gs.prod y) ≠ y) ∨
      (∀ b (hb : b < 4), gs.prod ⟨b, by omega⟩ = ⟨b, by omega⟩) ∨
      (∀ b (hb : b < 4), gs.prod ⟨b, by omega⟩ = τ ⟨b, by omega⟩) ∨ K3 ys r = true := by
  unfold recK at hr
  rw [RuScan.strictB_eq] at hr
  simp only [RuBase.bIf_eq] at hr
  split_ifs at hr with h0 h1 h2
  · rw [RuScan.strictB_eq] at hr
    exact Or.inl (kind0_sound h hr)
  · refine Or.inr (Or.inl fun b hb => Fin.ext ?_)
    have e := Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 hr b hb)
    have e1 : yAp ys b = (gs.prod ⟨b, by omega⟩ : Nat) := yAp_eq h ⟨b, by omega⟩
    rw [e1] at e
    exact e
  · refine Or.inr (Or.inr (Or.inl fun b hb => Fin.ext ?_))
    have e := Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 hr b hb)
    have e1 : yAp ys b = (gs.prod ⟨b, by omega⟩ : Nat) := yAp_eq h ⟨b, by omega⟩
    have e2 : apP T b = (τ ⟨b, by omega⟩ : Nat) := apP_eq hT ⟨b, by omega⟩
    rw [e1, e2] at e
    exact e
  · exact Or.inr (Or.inr (Or.inr hr))

theorem k3C_sound {TR HR : Nat → Nat} {o0 o1 o2 n0 n1 n2 nR : Nat} {ss : List Nat} {r : Nat}
    (h : k3C TR o0 o1 o2 n0 n1 n2 HR nR ss r = true) :
    ∃ ρ < nR, ∃ a0 < n0, ∃ a1 < n1, ∃ a2 < n2,
      conjOK ss [TR (o0 + a0), TR (o1 + a1), TR (o2 + a2)] (HR ρ) = true := by
  unfold k3C at h
  simp only [RuScan.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨_, h1, _, h2, _, h3, _, h4, h5⟩

theorem k3L_sound {TR HR : Nat → Nat} {o0 o1 n0 n1 nR : Nat} {ss : List Nat} {r : Nat}
    (h : k3L TR o0 o1 n0 n1 HR nR ss r = true) :
    ∃ ρ < nR, ∃ a0 < n0, ∃ a1 < n1, conjOK ss [TR (o0 + a0), TR (o1 + a1)] (HR ρ) = true := by
  unfold k3L at h
  simp only [RuScan.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨_, h1, _, h2, _, h3, h4⟩

theorem chkCov_spec {LR TR W : Nat → Nat} {T : Nat} {K3 : List Nat → Nat → Bool} {lo cnt : Nat}
    (h : chkCov LR TR W T K3 lo cnt = true) :
    ∀ d < cnt, recK [TR (roff 4060 48720 (LR 0) + (lo + d) / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + (lo + d) % rcnt (LR 1))] T K3 (W (lo + d)) = true := by
  unfold chkCov at h
  simp only [RuScan.strictB_eq] at h
  intro d hd
  exact RuBase.allN_iff.1 h d hd

theorem chkCov_all {LR TR W : Nat → Nat} {T : Nat} {K3 : List Nat → Nat → Bool} {K cnt : Nat}
    (h : ∀ q < K, chkCov LR TR W T K3 (cnt * q) cnt = true) :
    ∀ i < K * cnt, recK [TR (roff 4060 48720 (LR 0) + i / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + i % rcnt (LR 1))] T K3 (W i) = true := by
  intro i hi
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have := chkCov_spec (h _ hq) _ hd
  rwa [e] at this

theorem cjEq_sound {R H T : Nat} {h τ : Equiv.Perm (Fin 4060)} (hH : PRep 4060 12 H h)
    (hT : PRep 4060 12 T τ) (hc : cjEq R H T = true) : PRep 4060 12 R (h * τ * h⁻¹) := by
  intro y
  unfold cjEq eqF at hc
  have e := Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 hc _ (h⁻¹ y).2)
  beta_reduce at e
  have e1 : apP H (h⁻¹ y : Nat) = (h (h⁻¹ y) : Nat) := apP_eq hH _
  have e2 : apP T (h⁻¹ y : Nat) = (τ (h⁻¹ y) : Nat) := apP_eq hT _
  have e4 : h (h⁻¹ y) = y := by simp
  rw [e1, e2, apP_eq hH, e4] at e
  have e3 : pg 12 (mask 12) R y = apP R y := rfl
  rw [e3, e]
  simp [Equiv.Perm.mul_apply]

theorem fixC_eq {P : Nat} {g : Equiv.Perm (Fin 4060)} (hP : PRep 4060 12 P g) :
    fixC P = (CFSG.Certificates.Native.fixedList 4060 (unpack 4060 12 P)).length := by
  unfold fixC CFSG.Certificates.Native.fixedList
  refine congrArg List.length (List.filter_congr fun i hi => ?_)
  have hi' : i < 4060 := List.mem_range.1 hi
  have e0 : pg 12 (mask 12) P i = apP P i := rfl
  rw [unpack_get hi', e0]
  by_cases e : apP P i = i
  · rw [Nat.beq_eq.mpr e, beq_iff_eq.mpr e]
  · rw [Bool.eq_false_iff.mpr (fun h => e (Nat.eq_of_beq_eq_true h)), beq_eq_false_iff_ne.mpr e]

end CFSG.KC.Misc.RuCov

end
