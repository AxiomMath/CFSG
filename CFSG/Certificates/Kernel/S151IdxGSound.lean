module

public import Certificates.Data.Kernel.S151IdxG
public import CFSG.Certificates.Kernel.S151IdxFSound
public import CFSG.Certificates.Kernel.SporLatDcPair

public section

namespace CFSG.KC.IdxG

open CFSG.KC.E64F CFSG.KC.IdxF CFSG.KC.SLOm CFSG.Quasithin.S151S9T CFSG.QuasithinUnique.Ch1.SporLat

variable {n : Nat}

theorem fixCodes_sound {Δ : List Nat} (hΔ : codesBelow n Δ = true) {t : Array Nat}
    {f : Nat → Nat} (ht : Good n t f) (h : fixCodes n Δ f = true) : codeSetAct n t Δ = Δ := by
  rw [CFSG.KC.SLDc.codeSetAct_eq]
  have e : Δ.map (CFSG.KC.SLDc.codeAT n t) = Δ.map (codeF n f) := by
    refine List.map_congr_left fun c hc => ?_
    have hp := List.all_eq_true.1 (List.all_eq_true.1 hΔ c hc)
    unfold CFSG.KC.SLDc.codeAT codeF
    congr 2
    refine List.map_congr_left fun p hpm => ?_
    exact (ht.2 p (of_decide_eq_true (hp p hpm))).1
  unfold CFSG.KC.SLDc.codeSetT
  rw [e]
  exact beq_iff_eq.1 h

variable {D : LatData (List Nat)} {nm ns : Nat} {mlen : Nat → Nat}
  {M : Nat → Nat → Nat → Nat} {Sl : Nat → Nat → Nat}

theorem idx3OkG_sound (H : Hyp n D nm ns mlen M Sl) {act : Array Nat → List Nat → List Nat}
    {Δ : List Nat} {fx : (Nat → Nat) → Bool}
    (hfx : ∀ {t : Array Nat} {f : Nat → Nat}, Good n t f → fx f = true → act t Δ = Δ)
    {zT : Array Nat} {z : Nat → Nat} (hz : Good n zT z) {W : Idx3Wit}
    (h : idx3OkG W n fx nm ns mlen M Sl z = true) : W.Ok n act Δ D zT := by
  unfold idx3OkG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, h1⟩, hxw⟩, hczl⟩, hcz⟩, hx3⟩, hx1⟩, hrl⟩, hril⟩, hr⟩, hdc⟩ := h
  have hp' : W.p < nm := of_decide_eq_true hp
  have h1' : mlen W.p = 1 := beq_iff_eq.1 h1
  have hx : Good n (W.xT n D) (xF W M) := H.good_mword hp' h1' hxw
  have hrT : ∀ i < 5, Good n (W.rT n D i) (wordF Sl (W.rw.getD i [])) := fun i hi => by
    have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    unfold Idx3Wit.rT
    rw [getElem!_list_eq]
    exact H.good_sword e.1.1.1.1
  have hriT : ∀ i < 5, Good n (W.riT n D i) (wordF Sl (W.ri.getD i [])) := fun i hi => by
    have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    unfold Idx3Wit.riT
    rw [getElem!_list_eq]
    exact H.good_sword e.1.1.1.2
  refine ⟨by rw [H.nm_eq]; exact hp', by rw [H.len _ hp', h1'], ?_, ?_, ?_, beq_iff_eq.1 hrl,
    beq_iff_eq.1 hril, fun i hi => ?_, ?_, ?_, fun j hj => ?_⟩
  · intro l hl
    have := lt_of_all hxw l hl
    rw [H.ns_eq]
    exact this
  · exact tab_eq_of_eqOn (good_word (good_three1 (g := id) (h := id) hx) (by simp))
      (good_idTabN n) (eqOn_iff.2 (idOn_iff.1 hx3))
  · refine tab_ne_of_eqOn hx (good_idTabN n) ?_
    rw [Bool.not_eq_true'] at hx1 ⊢
    rw [Bool.eq_false_iff] at hx1 ⊢
    exact fun e => hx1 (idOn_iff.2 (eqOn_iff.1 e))
  · have e := List.all_eq_true.1 hr i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ := e
    refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, ?_, ?_⟩
    · rw [H.ns_eq]
      exact lt_of_all e1 l (by rwa [getElem!_list_eq] at hl)
    · rw [H.ns_eq]
      exact lt_of_all e2 l (by rwa [getElem!_list_eq] at hl)
    · exact tab_eq_of_eqOn (good_word (good_three2 (h := id) (hrT i hi) (hriT i hi)) (by simp))
        (good_idTabN n) (eqOn_iff.2 (idOn_iff.1 e3))
    · exact hfx (good_word (good_three2 (h := id) hx (hrT i hi)) (by simp)) e4
    · exact hfx (good_word (good_three2 (h := id) hx (hrT i hi)) (by simp)) e5
  · exact distinct5_spec (T := fun i => W.dcT n D i) (fun i hi =>
      good_word (good_three3 (hrT i hi) hx (hriT i hi)) (by simp [dcWord])) hdc
  · rw [beq_iff_eq.1 hczl, H.nm_eq]
  · rw [H.nm_eq] at hj
    have e := List.all_eq_true.1 hcz j (List.mem_range.2 hj)
    rw [beq_iff_eq] at e
    rw [getElem!_list_eq, ← czv_spec H hz hj, ← e]
    rfl

end CFSG.KC.IdxG

end
