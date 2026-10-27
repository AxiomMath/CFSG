
module

public import Certificates.Data.Kernel.Fi22Cls.Lab
public import CFSG.Certificates.Kernel.Fi22S0.KillSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs

public section

namespace CFSG.KD.Fi22Cls

open CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KD.Fi22S0 CFSG.Sporadic.Fi22.S0
open CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Foote.E27.Fi22S0
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native (nR)

theorem tabMul_zero_right {G : Type*} [Group G] {g : ℕ → G} {P : Array (ℕ × ℕ)}
    {Lt : Array (Array ℕ)} {n m : ℕ} (hT : TabData g P Lt n m) (hn : 0 < n) {x : ℕ} (hx : x < n) :
    tabMul P Lt x 0 = x := by
  obtain ⟨h1, h2⟩ := hT.mul x hx 0 hn
  rw [tabElt_zero, mul_one] at h2
  exact (hT.inj x hx _ h1 h2).symm

theorem labs_of {pp pj W CI REP KW KC KR : ℕ → ℕ} {lt : ℕ → ℕ → ℕ}
    (hT : TabData gJ par L nS 3)
    (hpar : par () = Array.ofFn (n := 19683) fun i => (pp i.val, pj i.val))
    (hL : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := 19683) fun i => lt j.val i.val)
    (hkill : ∀ a < 19683, killC pp pj lt KW KC KR 19683 126 a = true) (hr0 : KR 0 < 19683)
    (hlab : ∀ a < 19683, labC pp pj lt W CI REP KW KC (KR 0) 19683 126 a = true)
    (hrep : ∀ r < 126, REP r < 19683) {lr lo wo : Array ℕ}
    (hlr : lr = Array.ofFn (n := 126) fun l => REP l.val)
    (hlo : lo = Array.ofFn (n := 19683) fun i => CI i.val)
    (hwo : wo = Array.ofFn (n := 19683) fun i => W i.val) :
    lo.size = nS ∧ wo.size = nS ∧
      (List.range nS).all (fun i => i == 0 ||
        tabMul (par ()) (L ()) i (tabMul (par ()) (L ()) i i) != 0 ||
        (decide (lo[i]! < nR) && decide (wo[i]! < nS) && decide (lr[lo[i]!]! < nS) &&
          tabMul (par ()) (L ()) wo[i]! i == tabMul (par ()) (L ()) lr[lo[i]!]! wo[i]!)) = true := by
  refine ⟨by rw [hlo, Array.size_ofFn]; rfl, by rw [hwo, Array.size_ofFn]; rfl, ?_⟩
  have hj : ∀ i < 19683, pp i < i → pj i < 3 := by
    intro i hi hp
    have h := (hT.par_lt i (by omega) hi).2
    rw [hpar, CFSG.KS.LyS0K.ofFnG (fun i => (pp i, pj i)) hi] at h
    exact h
  have hLt : ∀ j < 3, ∀ i < 19683, lt j i < 19683 := by
    intro j hj i hi
    have h := (hT.left j hj i hi).1
    rw [hL, CFSG.KS.LyS0K.ofFnG (fun j => Array.ofFn (n := 19683) fun i => lt j i.val) hj,
      CFSG.KS.LyS0K.ofFnG (fun i => lt j i) hi] at h
    exact h
  have htm : ∀ a < 19683, ∀ b < 19683, tabMul (par ()) (L ()) a b = tm pp pj lt a b :=
    fun a ha b hb => tm_eq hpar hL hj hLt ha hb
  rw [List.all_eq_true]
  intro a ha
  have ha' : a < 19683 := List.mem_range.1 ha
  by_cases h0 : a = 0
  · subst h0
    rfl
  by_cases hc : tabMul (par ()) (L ()) a (tabMul (par ()) (L ()) a a) = 0
  swap
  · simp [hc]
  have haa := (hT.mul a ha' a ha').1
  have hc' := hc
  rw [htm a ha' _ haa, htm a ha' a ha'] at hc'
  have hl := hlab a ha'
  unfold labC at hl
  rw [sB_eq] at hl
  by_cases hr : CI a < 126
  · rw [bRec_eq, (blt_iff _ _).2 hr] at hl
    simp only [↓reduceIte, sB_eq, bRec_and, Bool.and_eq_true] at hl
    obtain ⟨hw, he⟩ := hl
    have hw' : W a < 19683 := (blt_iff _ _).1 hw
    have hx := hrep _ hr
    have g1 : lo[a]! = CI a := by
      rw [hlo]
      exact CFSG.KS.LyS0K.ofFnG (fun i => CI i) ha'
    have g2 : wo[a]! = W a := by
      rw [hwo]
      exact CFSG.KS.LyS0K.ofFnG (fun i => W i) ha'
    have g3 : lr[CI a]! = REP (CI a) := by
      rw [hlr]
      exact CFSG.KS.LyS0K.ofFnG (fun l => REP l) hr
    rw [g1, g2, g3, htm _ hw' _ ha', htm _ hx _ hw', Nat.eq_of_beq_eq_true he]
    have e1 : nR = 126 := rfl
    have e2 : nS = 19683 := rfl
    simp [e1, e2, hw', hr, hx]
  · exfalso
    have hb : Nat.blt (CI a) 126 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact hr ((blt_iff _ _).1 e)
    rw [bRec_eq, hb] at hl
    simp only [Bool.false_eq_true, ↓reduceIte, bRec_and, Bool.and_eq_true] at hl
    obtain ⟨hw0, hk0, hne⟩ := hl
    have ew := Nat.eq_of_beq_eq_true hw0
    have ek := Nat.eq_of_beq_eq_true hk0
    have hk := hkill a ha'
    have hb0 : Nat.beq a 0 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact h0 (Nat.eq_of_beq_eq_true e)
    unfold killC at hk
    rw [bRec_eq, hb0, sB_eq, hc'] at hk
    simp only [Bool.false_eq_true, ↓reduceIte, sB_eq, bRec_and, Bool.and_eq_true] at hk
    have hk2 : (Nat.blt (KW a) 19683 && (Nat.blt (KC a) 126 &&
        Nat.beq (tm pp pj lt (KW a) a) (tm pp pj lt (KR (KC a)) (KW a)))) = true := hk
    simp only [Bool.and_eq_true] at hk2
    obtain ⟨-, -, he⟩ := hk2
    rw [ew, ek] at he
    have e := Nat.eq_of_beq_eq_true he
    rw [← htm 0 (by omega) a ha', ← htm _ hr0 0 (by omega), tabMul_zero,
      tabMul_zero_right hT (by unfold nS; omega) (by unfold nS; omega)] at e
    have hn : Nat.beq a (KR 0) = true := by
      rw [e]
      exact Nat.beq_refl _
    rw [bRec_eq, hn] at hne
    simp at hne

end CFSG.KD.Fi22Cls

end
