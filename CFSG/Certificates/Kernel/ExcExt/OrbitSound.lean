module

public import CFSG.Certificates.Kernel.ExcExt.Sound
public import Certificates.Data.Kernel.ExcExt.Orbit
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcLine

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}

theorem bor_eq_true {a b : Bool} : bor a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem sumN_eq (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ k : Fin n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : sumN (n + 1) f = sumN n f + f n := rfl
    rw [e, ih, Fin.sum_univ_castSucc]
    simp

theorem ofDigK_eq (d : ℕ) (f : ℕ → ℕ) : ofDigK d f = ∑ k : Fin d, (f k % 3) * 3 ^ (k : ℕ) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have e : ofDigK (d + 1) f = ofDigK d f + (f d % 3) * 3 ^ d := rfl
    rw [e, ih, Fin.sum_univ_castSucc]
    simp

theorem digK_eq (c k : ℕ) : digK c k = Chk.dig c k := rfl

private theorem idx_lt (u : Root m) (k : Fin (dim m)) : dim m * u + k < dim m * nroots m :=
  calc dim m * u + k < dim m * u + dim m := by omega
    _ = dim m * (u + 1) := by ring
    _ ≤ dim m * nroots m := Nat.mul_le_mul_left _ u.isLt

private theorem lane_cast (x : ℕ) : (((x + 1) % 3 : ℕ) : ZMod 3) = ((x : ℤ) - 8 : ℤ) := by
  rw [ZMod.natCast_mod]
  push_cast
  have h9 : (9 : ZMod 3) = 0 := by decide
  linear_combination h9

private theorem getD_decI {d r x i k : ℕ} (hi : i < r) (hk : k < d) :
    ((decI d r x).getD i []).getD k 0 = (ln4 x (d * i + k) : ℤ) - 8 := by
  simp [decI, exI, List.getD_eq_getElem?_getD, hi, hk]

theorem fK_cast (hK : TabsOK m K fx hx fx' hx') (u : Root m) (k : Fin (dim m)) :
    ((fK K u k : ℕ) : ZMod 3) = (F m u k : ZMod 3) := by
  have hF : tabF m = decI (dim m) (nroots m) fx := beq_iff_eq.mp hK.hF
  have hres := Nat.eq_of_beq_eq_true (allN_iff.mp hK.hf3 _ (idx_lt u k))
  have e1 : fK K u k = (ln4 fx (dim m * u + k) + 1) % 3 := by
    unfold fK
    rw [hK.hd]
    exact hres
  have e2 : F m u k = (ln4 fx (dim m * u + k) : ℤ) - 8 := by
    rw [F, hF]
    exact getD_decI u.isLt k.isLt
  rw [e1, e2, lane_cast]

theorem hK_cast (hK : TabsOK m K fx hx fx' hx') (u : Root m) (k : Fin (dim m)) :
    ((ExcExtK.hK K u k : ℕ) : ZMod 3) = (H m u k : ZMod 3) := by
  have hH : tabH m = decI (dim m) (nroots m) hx := beq_iff_eq.mp hK.hH
  have hres := Nat.eq_of_beq_eq_true (allN_iff.mp hK.hh3 _ (idx_lt u k))
  have e1 : ExcExtK.hK K u k = (ln4 hx (dim m * u + k) + 1) % 3 := by
    unfold ExcExtK.hK
    rw [hK.hd]
    exact hres
  have e2 : H m u k = (ln4 hx (dim m * u + k) : ℤ) - 8 := by
    rw [H, hH]
    exact getD_decI u.isLt k.isLt
  rw [e1, e2, lane_cast]

theorem reflK_eq (hK : TabsOK m K fx hx fx' hx') (u : Root m) (c : ℕ) :
    reflK K u c = code m (reflection m u (vec m c)) := by
  have e0 : reflK K u c = ofDigK K.d fun k =>
      digK c k + 2 * ((∑ j : Fin K.d, fK K u j * digK c j) % 3 * ExcExtK.hK K u k) := by
    unfold reflK reflA
    rw [sumN_eq]
    rfl
  rw [e0, hK.hd, ofDigK_eq, code]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← ZMod.val_natCast (n := 3)]
  congr 1
  rw [reflection_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, root_apply, coroot, vec, digK_eq]
  push_cast
  rw [ZMod.natCast_mod]
  push_cast
  simp only [fK_cast hK, hK_cast hK]
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination ((∑ j : Fin (dim m), (F m u j : ZMod 3) * (Chk.dig c j : ZMod 3)) *
    (H m u k : ZMod 3)) * h3

theorem memK_sound {c : ℕ} {L : List ℕ} (h : memK c L = true) : c ∈ L := by
  induction L with
  | nil => exact absurd h Bool.false_ne_true
  | cons a l ih =>
    have e : memK c (a :: l) = bor (Nat.beq a c) (memK c l) := rfl
    rw [e, bor_eq_true] at h
    rcases h with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih h)

theorem orbOK_spec {B : ℕ} {reps : List ℕ} {c : ℕ} (h : orbOK K B reps c = true) :
    c ∈ reps ∨ (parE (ln32 B c) < 3 ^ K.d ∧ refE (ln32 B c) < K.r ∧
      depE (ln32 B (parE (ln32 B c))) < depE (ln32 B c) ∧
      reflK K (refE (ln32 B c)) (parE (ln32 B c)) = c) := by
  unfold orbOK orbE at h
  generalize ln32 B c = e at h ⊢
  cases hd : Nat.beq (depE e) 0
  · rw [hd] at h
    simp only [band_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    exact Or.inr h
  · rw [hd] at h
    exact Or.inl (memK_sound h)

theorem extCasesVx_of_line (hT : Chk.tabsOK m (tabsK m K) = true) {L : KLine} (h : ExtLineOK m K L)
    {c : ℕ} (hcv : L.cv = c) (hc : c < 3 ^ dim m) : ExtCasesVx (excRaw m) (vec m c) := by
  subst hcv
  refine extCasesVx_of_scanLineN hT (S := searchOf m L) (X := witOf m L) ?_
  rw [code_vec m hc]
  exact h

theorem extCasesVx_of_orbit (hK : TabsOK m K fx hx fx' hx') {T : Chk.Tabs}
    (hT : Chk.tabsOK m T = true) {B : ℕ} {reps : List ℕ}
    (hB : ∀ c < 3 ^ dim m, orbOK K B reps c = true)
    (hR : ∀ c ∈ reps, ExtCasesVx (excRaw m) (vec m c)) (vx : V m) :
    ExtCasesVx (excRaw m) vx := by
  have key : ∀ n c, c < 3 ^ dim m → depE (ln32 B c) = n → ExtCasesVx (excRaw m) (vec m c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hc hn
      rcases orbOK_spec (hB c hc) with hmem | ⟨hp, hu, hdp, hrefl⟩
      · exact hR c hmem
      · generalize parE (ln32 B c) = p at hp hdp hrefl
        generalize refE (ln32 B c) = u at hu hrefl
        rw [hK.hd] at hp
        rw [hK.hr] at hu
        have hpar := ih _ (lt_of_lt_of_eq hdp hn) p hp rfl
        have h2 : reflK K u p = code m (reflection m ⟨u, hu⟩ (vec m p)) := reflK_eq hK ⟨u, hu⟩ p
        have e : vec m c = reflection m ⟨u, hu⟩ (vec m p) := by
          rw [← hrefl, h2, vec_code]
        rw [e]
        exact extCasesVx_reflection hT _ hpar
  have h := key _ (code m vx) (code_lt m vx) rfl
  rwa [vec_code] at h

theorem orbOK_of_chunks {B : ℕ} {reps : List ℕ} {w q : ℕ}
    (h : ∀ j < q, orbRangeOK K B reps (w * j) w = true) : ∀ c < w * q, orbOK K B reps c = true := by
  intro c hc
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
  have hj : c / w < q := (Nat.div_lt_iff_lt_mul hw).mpr (by rwa [Nat.mul_comm])
  have h' := allN_iff.mp (h (c / w) hj) (c % w) (Nat.mod_lt c hw)
  have e : w * (c / w) + c % w = c := Nat.div_add_mod c w
  rw [← e]
  exact h'

theorem orbOK_all {B : ℕ} {reps : List ℕ} {w q : ℕ} (hwq : 3 ^ dim m = w * q)
    (h : ∀ j < q, orbRangeOK K B reps (w * j) w = true) :
    ∀ c < 3 ^ dim m, orbOK K B reps c = true := by
  rw [hwq]
  exact orbOK_of_chunks h

end CFSG.ExcExtK

end
