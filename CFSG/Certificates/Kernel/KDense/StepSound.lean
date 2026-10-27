module

public import CFSG.Certificates.Kernel.KStep.Rho
public import CFSG.Certificates.Kernel.KStep.Xi
public import CFSG.Certificates.Kernel.KStep.Tau
public import CFSG.Certificates.Kernel.KStep.Perm15
public import CFSG.Certificates.Kernel.KStep.KeyBind
public import CFSG.Certificates.Kernel.KStep.Defs
import CFSG.Certificates.Kernel.KDense.KeysSound
import CFSG.Certificates.Kernel.KDense.Data.Checks
import CFSG.Certificates.Kernel.KDense.Data.KeySort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.Monster.AxisCount

theorem resPN_four' (S x p : ℕ) : (resPN 4 S x p : ZMod (2 ^ 4 - 1)) = (resP S x p : ZMod 15) := by
  unfold resPN resP
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
  congr 1
  ring

theorem resN_four' (v : Native.DVec) (k : ℕ) : (resN 4 v k : ZMod (2 ^ 4 - 1)) = (res15 v k : ZMod 15) := by
  unfold resN res15
  norm_num

theorem rep_iff_four {v : Native.DVec} {s : St} : Rep v s ↔ RepN 4 v s := by
  unfold Rep RepN
  simp only [resPN_four', resN_four']

theorem andB_eq' (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem listEq_eq' : ∀ {l m : List ℕ}, listEq l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: l, y :: m, h => by
    change andB (Nat.beq x y) (listEq l m) = true at h
    rw [andB_eq', Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, listEq_eq' h.2]

theorem findIdx_spec {l : List ℕ} : ∀ {ls : List (List ℕ)}, (findIdx l ls).1 = true →
    ∃ h : (findIdx l ls).2 < ls.length, ls[(findIdx l ls).2] = l
  | [], h => absurd h Bool.false_ne_true
  | x :: ls, h => by
    change (Bool.rec (motive := fun _ => Bool × Nat)
      (Prod.rec (motive := fun _ => Bool × Nat) (fun f i => (f, Nat.add i (nat_lit 1))) (findIdx l ls))
      (true, nat_lit 0) (listEq x l)).1 = true at h
    change ∃ h : (Bool.rec (motive := fun _ => Bool × Nat)
      (Prod.rec (motive := fun _ => Bool × Nat) (fun f i => (f, Nat.add i (nat_lit 1))) (findIdx l ls))
      (true, nat_lit 0) (listEq x l)).2 < (x :: ls).length, (x :: ls)[(Bool.rec (motive := fun _ => Bool × Nat)
      (Prod.rec (motive := fun _ => Bool × Nat) (fun f i => (f, Nat.add i (nat_lit 1))) (findIdx l ls))
      (true, nat_lit 0) (listEq x l)).2] = l
    rcases hx : listEq x l
    · rw [hx] at h
      rcases hfi : findIdx l ls with ⟨f, i⟩
      rw [hfi] at h
      have := findIdx_spec (ls := ls) (by rw [hfi]; exact h)
      rw [hfi] at this
      obtain ⟨hi, he⟩ := this
      change ∃ h : i + 1 < ls.length + 1, (x :: ls)[i + 1] = l
      exact ⟨by omega, by simpa using he⟩
    · change ∃ h : 0 < ls.length + 1, (x :: ls)[0] = l
      exact ⟨by omega, listEq_eq' hx⟩

theorem tabOK_get {F : Fix} {T : Tab} (h : tabOK F T = true) :
    ∀ k (hk : k < T.arrs.length), entryOK F T T.arrs[k] k = true := by
  have key : ∀ (L : List (List ℕ)) (k0 : ℕ), List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun l _ ih k => andB (entryOK F T l k) (ih (Nat.add k (nat_lit 1)))) L k0 = true →
      ∀ i (hi : i < L.length), entryOK F T L[i] (k0 + i) = true := by
    intro L
    induction L with
    | nil => intro _ _ i hi; exact absurd hi (Nat.not_lt_zero i)
    | cons x L ih =>
      intro k0 h0 i hi
      obtain ⟨h1, h2⟩ := Benes.andB_true h0
      rcases i with _ | i
      · simpa using h1
      · have := ih (k0 + 1) h2 i (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  intro k hk
  have := key T.arrs 0 h k hk
  rwa [Nat.zero_add] at this

theorem dataOK_parts {F : Fix} {T : Tab} {KT TH OCT DU1 : ℕ} (h : dataOK F T KT TH OCT DU1 = true) :
    KeyBind F ∧ xiOK F = true ∧ poutOK F = true ∧ pi6OK F = true ∧ tauMasksOK F = true ∧
      tabOK F T = true := by
  unfold dataOK fixOK at h
  simp only [andB_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, ⟨x1, x2, x3, x4⟩, h7⟩ := h
  exact ⟨keyBind_of h1 h2 h3 h4 h5, x1, x2, x3, x4, h7⟩

end CFSG.KC.KStep

namespace CFSG.KC.KDense

open CFSG.KC.KStep CFSG.Monster.AxisCount

theorem step_sound {F : Fix} {T : Tab} {KT TH OCT DU1 : Nat} (h : dataOK F T KT TH OCT DU1 = true)
    (g : Native.Gen) (hg : letterOK g = true) (v : Native.DVec) (s : St) (hs : Rep v s)
    (hf : (step F T g s).1 = true) :
    g.validB = true ∧ Rep (Native.applyGen (Native.mkCtx ()) g v) (step F T g s) := by
  obtain ⟨hK, hx, hp, h6, hm, ht⟩ := dataOK_parts h
  have hG : KeysGood := CFSG.KC.KDense.keys_sound CFSG.KD.KDF.F CFSG.KD.KDF.KT CFSG.KD.KDF.TH
      CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 CFSG.KD.KDK.NK CFSG.KD.KDF.th_ok CFSG.KD.KDF.oct_ok
      CFSG.KD.KDF.du1_ok CFSG.KD.KDF.keys_ok CFSG.KD.KDF.keyPlanes_ok CFSG.KD.KDK.keys_distinct
  have hs4 := rep_iff_four.1 hs
  obtain ⟨ok, X, A, W⟩ := s
  cases g with
  | rho q =>
    obtain ⟨qs, qa, qd⟩ := q
    have ha : qa < 4096 := by
      have : Nat.blt qa 4096 = true := hg
      rwa [Nat.blt_eq] at this
    refine ⟨rfl, rep_iff_four.2 ?_⟩
    have e : step F T (.rho (qs, qa, qd)) (ok, X, A, W) =
        (andB ok true, (rhoG ops15 F qs.toNat qa qd X A W).2) := by
      cases qs <;> rfl
    rw [e]
    exact rho_sound ops15_law (by decide) hK hG qs ha qd hs4 _
  | perm arr =>
    have hsz : arr.size = 24 := by
      have : Nat.beq arr.size 24 = true := hg
      rwa [Nat.beq_eq] at this
    have e : step F T (.perm arr) (ok, X, A, W) =
        (andB ok (findIdx (arrList arr) T.arrs).1, permStep T (findIdx (arrList arr) T.arrs).2 X A W) :=
      rfl
    rw [e] at hf ⊢
    have hf' : (findIdx (arrList arr) T.arrs).1 = true := by
      have : andB ok (findIdx (arrList arr) T.arrs).1 = true := hf
      rw [andB_eq', Bool.and_eq_true] at this
      exact this.2
    obtain ⟨hk, hkl⟩ := findIdx_spec hf'
    have he := tabOK_get ht _ hk
    rw [hkl] at he
    obtain ⟨hv, hr⟩ := perm15_sound hK hG hsz he hs4 (andB ok (findIdx (arrList arr) T.arrs).1)
    exact ⟨hv, rep_iff_four.2 hr⟩
  | sign a =>
    exact absurd hf (by
      have : (step F T (.sign a) (ok, X, A, W)).1 = false := rfl
      rw [this]
      exact Bool.false_ne_true)
  | xi =>
    refine ⟨rfl, rep_iff_four.2 ?_⟩
    exact xi_sound ops15_law (by decide) hK hG hx hp hs4 ok
  | tau =>
    refine ⟨rfl, rep_iff_four.2 ?_⟩
    exact tau_sound ops15_law (by decide) h6 hm hs4 ok

end CFSG.KC.KDense

end
