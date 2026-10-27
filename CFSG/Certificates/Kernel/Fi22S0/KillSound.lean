
module

public import Certificates.Data.Kernel.Fi22S0.Kill
public import CFSG.Certificates.Kernel.Fi22S0.Sound
public import CFSG.Certificates.Kernel.LyS0.Sound
import Mathlib
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.KD.Fi22S0

open CFSG.KC.Fi22S0 CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27
open CFSG.HardMathSupport.Foote.E27.Fi22S0 Subgroup
open CFSG.Sporadic.Fi22 (J)

theorem sN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem nRec_eq (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bRec_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem tmF_succ (pp pj : ℕ → ℕ) (lt : ℕ → ℕ → ℕ) (f a b : ℕ) :
    tmF pp pj lt (f + 1) a b = CFSG.KC.Enum.strictN (pp a) fun p =>
      Bool.rec (motive := fun _ => ℕ) b (lt (pj a) (tmF pp pj lt f p b)) (Nat.blt p a) := rfl

theorem tmF_eq {pp pj : ℕ → ℕ} {lt : ℕ → ℕ → ℕ}
    (hpar : par () = Array.ofFn (n := 19683) fun i => (pp i.val, pj i.val))
    (hL : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := 19683) fun i => lt j.val i.val)
    (hj : ∀ i < 19683, pp i < i → pj i < 3) (hLt : ∀ j < 3, ∀ i < 19683, lt j i < 19683)
    {b : ℕ} (hb : b < 19683) :
    ∀ f a, a < 19683 → a < f →
      tabMul (par ()) (L ()) a b = tmF pp pj lt f a b ∧ tmF pp pj lt f a b < 19683
  | 0, a, _, h => absurd h (Nat.not_lt_zero a)
  | f + 1, a, ha, hf => by
    have hpa : (par ())[a]! = (pp a, pj a) := by
      rw [hpar, CFSG.KS.LyS0K.ofFnG (fun i => (pp i, pj i)) ha]
    rw [tabMul, tmF_succ, sN_eq, nRec_eq, hpa]
    by_cases hlt : pp a < a
    · have hb' : Nat.blt (pp a) a = true := CFSG.KS.LyS0K.blt_iff hlt
      rw [dif_pos hlt, hb']
      simp only [↓reduceIte]
      have hja := hj a ha hlt
      obtain ⟨e1, e2⟩ := tmF_eq hpar hL hj hLt hb f (pp a) (by omega) (by omega)
      rw [e1, hL, CFSG.KS.LyS0K.ofFnG (fun j => Array.ofFn (n := 19683) fun i => lt j i.val) hja,
        CFSG.KS.LyS0K.ofFnG (fun i => lt (pj a) i) e2]
      exact ⟨rfl, hLt _ hja _ e2⟩
    · have hb' : Nat.blt (pp a) a = false := by
        rw [Bool.eq_false_iff]
        intro e
        exact hlt (CFSG.KS.LyS0K.blt_of e)
      rw [dif_neg hlt, hb']
      exact ⟨rfl, hb⟩

theorem tm_eq {pp pj : ℕ → ℕ} {lt : ℕ → ℕ → ℕ}
    (hpar : par () = Array.ofFn (n := 19683) fun i => (pp i.val, pj i.val))
    (hL : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := 19683) fun i => lt j.val i.val)
    (hj : ∀ i < 19683, pp i < i → pj i < 3) (hLt : ∀ j < 3, ∀ i < 19683, lt j i < 19683)
    {a b : ℕ} (ha : a < 19683) (hb : b < 19683) :
    tabMul (par ()) (L ()) a b = tm pp pj lt a b :=
  (tmF_eq hpar hL hj hLt hb (a + 1) a ha (by omega)).1

theorem card_inf_centralizer_conj {G : Type*} [Group G] {T : Subgroup G} {u x y : G}
    (hu : u ∈ T) (e : u * x = y * u) :
    Nat.card ↥(T ⊓ centralizer ({x} : Set G)) = Nat.card ↥(T ⊓ centralizer ({y} : Set G)) := by
  have hy : y = u * x * u⁻¹ := by rw [e, mul_inv_cancel_right]
  subst hy
  refine Nat.card_congr
    { toFun := fun z => ⟨u * z * u⁻¹, ?_⟩
      invFun := fun z => ⟨u⁻¹ * z * u, ?_⟩
      left_inv := fun z => by ext; simp [mul_assoc]
      right_inv := fun z => by ext; simp [mul_assoc] }
  · obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.1 z.2
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem hu hzT) (T.inv_mem hu), ?_⟩
    rw [mem_centralizer_singleton_iff] at hzC ⊢
    calc u * z * u⁻¹ * (u * x * u⁻¹) = u * (z * x) * u⁻¹ := by group
      _ = u * (x * z) * u⁻¹ := by rw [hzC]
      _ = u * x * u⁻¹ * (u * z * u⁻¹) := by group
  · obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.1 z.2
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem (T.inv_mem hu) hzT) hu, ?_⟩
    rw [mem_centralizer_singleton_iff] at hzC ⊢
    calc u⁻¹ * z * u * x = u⁻¹ * (z * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * (u * x * u⁻¹ * z) * u := by rw [hzC]
      _ = x * (u⁻¹ * z * u) := by group

theorem tabComm_eq_of_conj (hT : TabData gJ par L nS 3) {w a r : ℕ} (hw : w < nS) (ha : a < nS)
    (hr : r < nS) (e : tabMul (par ()) (L ()) w a = tabMul (par ()) (L ()) r w) :
    tabComm (par ()) (L ()) nS a = tabComm (par ()) (L ()) nS r := by
  have := finite_J
  obtain ⟨T, hTm, -⟩ := hT.exists_subgroup (by unfold nS; norm_num : 0 < nS)
  rw [← hT.card_inf_centralizer hTm ha, ← hT.card_inf_centralizer hTm hr]
  refine card_inf_centralizer_conj ((hTm _).2 ⟨w, hw, rfl⟩) ?_
  rw [(hT.mul w hw a ha).2, (hT.mul r hr w hw).2, e]

theorem killOK_of {pp pj W CI REP : ℕ → ℕ} {lt cw : ℕ → ℕ → ℕ}
    (hT : TabData gJ par L nS 3)
    (hpar : par () = Array.ofFn (n := 19683) fun i => (pp i.val, pj i.val))
    (hL : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := 19683) fun i => lt j.val i.val)
    (hkill : ∀ a < 19683, killC pp pj lt W CI REP 19683 126 a = true)
    (hrep : ∀ r < 126, repC pp pj lt REP cw 19683 81 r = true) : killOK () = true := by
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
  unfold killOK
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
  rw [htm a ha' _ haa, htm a ha' a ha'] at hc
  have hk := hkill a ha'
  have hb0 : Nat.beq a 0 = false := by
    rw [Bool.eq_false_iff]
    intro e
    exact h0 (Nat.eq_of_beq_eq_true e)
  unfold killC at hk
  rw [bRec_eq, hb0, sB_eq, hc] at hk
  simp only [Bool.false_eq_true, ↓reduceIte, sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at hk
  have hk2 : (Nat.blt (W a) 19683 && (Nat.blt (CI a) 126 &&
      Nat.beq (tm pp pj lt (W a) a) (tm pp pj lt (REP (CI a)) (W a)))) = true := hk
  simp only [Bool.and_eq_true, blt_iff] at hk2
  obtain ⟨hw, hr, he⟩ := hk2
  have hrep' := hrep _ hr
  unfold repC at hrep'
  simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at hrep'
  obtain ⟨hx, hall⟩ := hrep'
  have hall' := CFSG.KS.allN_spec hall
  have hw' : ∀ k < 81, cw (CI a) k < 19683 ∧
      (k ≠ 0 → cw (CI a) (k - 1) < cw (CI a) k) ∧
      tm pp pj lt (REP (CI a)) (cw (CI a) k) = tm pp pj lt (cw (CI a) k) (REP (CI a)) := by
    intro k hk
    have h := hall' k hk
    simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff, bRec_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, fun hk0 => ?_, Nat.eq_of_beq_eq_true h3⟩
    have hb : Nat.beq k 0 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact hk0 (Nat.eq_of_beq_eq_true e)
    rw [hb] at h2
    simp only [Bool.false_eq_true, ↓reduceIte, blt_iff] at h2
    exact h2
  have hcomm : tabComm (par ()) (L ()) nS a = tabComm (par ()) (L ()) nS (REP (CI a)) := by
    refine tabComm_eq_of_conj hT hw ha' hx ?_
    rw [htm _ hw _ ha', htm _ hx _ hw]
    exact Nat.eq_of_beq_eq_true he
  have h81 : 81 ≤ tabComm (par ()) (L ()) nS (REP (CI a)) := by
    unfold tabComm
    refine CFSG.KS.LyS0K.le_countP (W := cw (CI a)) (fun k hk => (hw' k hk).1)
      (fun k hk => ?_) (fun k hk => ?_)
    · have := (hw' (k + 1) hk).2.1 (by omega)
      simpa using this
    · obtain ⟨h1, -, h3⟩ := hw' k hk
      rw [htm _ hx _ h1, htm _ h1 _ hx, h3]
      exact beq_self_eq_true _
  simp [hcomm, h81]

end CFSG.KD.Fi22S0

end
