
module

public import CFSG.Certificates.Kernel.LocalQTA7KSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoInputs

public section

namespace CFSG.KC.LQT.L

open Equiv Matrix CFSG.KC.LQT.S CFSG.KC.LQT.CM CFSG.QuasithinUnique.Vol2Native.A312L

@[expose] def bitsV (v : Fin 3 → ZMod 2) : ℕ := (v 0).val + 2 * (v 1).val + 4 * (v 2).val

@[expose] def mBits (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ℕ :=
  (A 0 0).val + 2 * (A 0 1).val + 4 * (A 0 2).val + 8 * (A 1 0).val + 16 * (A 1 1).val +
    32 * (A 1 2).val + 64 * (A 2 0).val + 128 * (A 2 1).val + 256 * (A 2 2).val

theorem mBits_lt (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : mBits A < 512 := by
  have h : ∀ r c, (A r c).val < 2 := fun r c => ZMod.val_lt (A r c)
  have := h 0 0
  have := h 0 1
  have := h 0 2
  have := h 1 0
  have := h 1 1
  have := h 1 2
  have := h 2 0
  have := h 2 1
  have := h 2 2
  unfold mBits
  omega

theorem det_bits : ∀ a b c d e f g h i : ZMod 2,
    a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g = 1 →
    detK2 (a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val + 32 * f.val + 64 * g.val +
      128 * h.val + 256 * i.val) = 1 := by
  decide

theorem detK2_mBits {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : A.det = 1) :
    detK2 (mBits A) = 1 := by
  rw [Matrix.det_fin_three] at h
  exact det_bits _ _ _ _ _ _ _ _ _ h

theorem mv_bits : ∀ a b c d e f g h i x y z : ZMod 2,
    mvK (a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val + 32 * f.val + 64 * g.val +
      128 * h.val + 256 * i.val) (x.val + 2 * y.val + 4 * z.val) =
    (a * x + b * y + c * z).val + 2 * (d * x + e * y + f * z).val +
      4 * (g * x + h * y + i * z).val := by
  decide

theorem mvK_mBits (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    mvK (mBits A) (bitsV v) = bitsV (A *ᵥ v) := by
  have e : ∀ r, (A *ᵥ v) r = A r 0 * v 0 + A r 1 * v 1 + A r 2 * v 2 := fun r => by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  unfold bitsV mBits
  rw [e 0, e 1, e 2]
  exact mv_bits _ _ _ _ _ _ _ _ _ _ _ _

theorem bitsV_inj : ∀ u v : Fin 3 → ZMod 2, bitsV u = bitsV v → u = v := by
  decide

theorem brec_beq (x w a b : ℕ) :
    Bool.rec (motive := fun _ => ℕ) a b (Nat.beq x w) = if x = w then b else a := by
  by_cases h : x = w
  · subst h
    simp [Nat.beq_refl]
  · rw [beq_false h]
    simp [h]

theorem idxK_eq (V : List ℕ) (w : ℕ) : idxK V w =
    if getK V 0 = w then 0 else if getK V 1 = w then 1 else if getK V 2 = w then 2 else
    if getK V 3 = w then 3 else if getK V 4 = w then 4 else if getK V 5 = w then 5 else 6 := by
  change Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 6 5
      (Nat.beq (getK V 5) w)) 4 (Nat.beq (getK V 4) w)) 3 (Nat.beq (getK V 3) w)) 2
      (Nat.beq (getK V 2) w)) 1 (Nat.beq (getK V 1) w)) 0 (Nat.beq (getK V 0) w) = _
  simp only [brec_beq]

theorem getK_getD : ∀ (l : List ℕ) (i : ℕ), getK l i = l.getD i 0
  | [], _ => rfl
  | x :: l, i => by
    change Bool.rec (motive := fun _ => ℕ) (getK l (Nat.sub i 1)) x (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      rw [beq_false (Nat.succ_ne_zero i), getK_getD l]
      rfl

theorem getK_bits {vec : Fin 7 → Fin 3 → ZMod 2} {V : List ℕ}
    (hv : (List.finRange 7).map (fun i => bitsV (vec i)) = V) (j : Fin 7) :
    getK V j = bitsV (vec j) := by
  rw [getK_getD, ← hv, List.getD_eq_getElem _ _ (by simp)]
  simp

theorem rhoRaw_get (vec : Fin 7 → Fin 3 → ZMod 2) (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (j : Fin 7) : (Seven.rhoRaw vec A).get j = Seven.idxOf vec (A *ᵥ vec j) := by
  fin_cases j <;> rfl

theorem idxK_bits {vec : Fin 7 → Fin 3 → ZMod 2} {V : List ℕ}
    (hv : (List.finRange 7).map (fun i => bitsV (vec i)) = V) (u : Fin 3 → ZMod 2) :
    idxK V (bitsV u) = Seven.idxOf vec u := by
  have hb : ∀ j : Fin 7, getK V j = bitsV u ↔ u = vec j := fun j => by
    rw [getK_bits hv j]
    exact ⟨fun e => (bitsV_inj _ _ e).symm, fun e => by rw [e]⟩
  rw [idxK_eq]
  have h0 : getK V 0 = bitsV u ↔ u = vec 0 := hb 0
  have h1 : getK V 1 = bitsV u ↔ u = vec 1 := hb 1
  have h2 : getK V 2 = bitsV u ↔ u = vec 2 := hb 2
  have h3 : getK V 3 = bitsV u ↔ u = vec 3 := hb 3
  have h4 : getK V 4 = bitsV u ↔ u = vec 4 := hb 4
  have h5 : getK V 5 = bitsV u ↔ u = vec 5 := hb 5
  simp only [h0, h1, h2, h3, h4, h5]
  unfold Seven.idxOf
  split_ifs <;> rfl

theorem rhoK_mBits {vec : Fin 7 → Fin 3 → ZMod 2} {V : List ℕ}
    (hv : (List.finRange 7).map (fun i => bitsV (vec i)) = V) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    rhoK V (mBits A) = rc7 (Seven.rhoRaw vec A) := by
  refine (ofFn_congr fun i hi => ?_)
  rw [getK_bits hv ⟨i, hi⟩, mvK_mBits, idxK_bits hv]
  simp only [hi, ↓reduceDIte, rhoRaw_get]

theorem rho7_sound (C : List Lvl) (hI : chainInj 7 C = true) (G : List Seven.P7)
    (vec : Fin 7 → Fin 3 → ZMod 2) {V : List ℕ} {d : ℕ}
    (hv : (List.finRange 7).map (fun i => bitsV (vec i)) = V)
    (h : rhoIn7 C d V (G.map code) = true) :
    ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (Seven.bfsSet (G.map Seven.R7.enc) d).contains (Seven.rhoRaw vec g) = true := by
  intro g
  unfold rhoIn7 at h
  rw [P.andB_iff, P.andB_iff, P.allN_iff, map_code7] at h
  obtain ⟨hok, hb, hall⟩ := h
  have hm := hall (mBits g) (mBits_lt g)
  rw [P.impB_iff, P.beq_iff, rhoK_mBits hv] at hm
  have := hm (detK2_mBits (Matrix.SpecialLinearGroup.det_coe g))
  rw [Std.HashSet.contains_iff_mem, bfsSet7_eq]
  exact (repM_mem (idxInj7 hok hI _) (rep7 hok hI _ d hb) _).1 this

end CFSG.KC.LQT.L

end
