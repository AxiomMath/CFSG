module

public import CFSG.Certificates.Kernel.SuzNine.Sound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.SuzNine

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Mathieu

theorem fldK_of_prep {P : ℕ} {g : Equiv.Perm (Fin 1782)} (h : PRep 1782 11 P g)
    (x : Fin 1782) : fldK P x = g x := h x

theorem setK_prep {P : ℕ} {g : Equiv.Perm (Fin 1782)} (h : PRep 1782 11 P g)
    (s : Finset (Fin 1782)) :
    setK s.card (listKey (ptList s)) P = listKey (ptList (s.map g.toEmbedding)) :=
  setK_map (by decide) g (fldK_of_prep h) s

@[expose] def posProd {n : ℕ} (gs : ℕ → Equiv.Perm (Fin n)) (wd : List ℤ) : Equiv.Perm (Fin n) :=
  (wd.map fun z => gs (z.toNat - 1)).prod

theorem prep_wordK_pos {j : ℕ} {PS : ℕ → ℕ} {gs : ℕ → Equiv.Perm (Fin 1782)}
    (hS : ∀ h < j, PRep 1782 11 (PS h) (gs h)) (PSI : ℕ → ℕ) :
    ∀ wd : List ℤ, lettersK j wd = true →
      CFSG.KC.LQT.P.allL (wd.map icode) (fun c => Nat.beq (Nat.land c 1) 0) = true →
      PRep 1782 11 (wordK 1782 11 (mask 11) (pidn 1782 11) PS PSI wd) (posProd gs wd)
  | [], _, _ => by
    rw [wordK_nil]
    simpa [posProd] using prep_pidn (n := 1782) (w := 11) (by decide) (by decide)
  | z :: wd, hl, hp => by
    rw [lettersK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hc0, hcj⟩, hl⟩ := hl
    have hp' := (CFSG.KC.LQT.P.allL_iff _ _).1 hp
    have hz := hp' (icode z) (by simp)
    have hrest : CFSG.KC.LQT.P.allL (wd.map icode) (fun c => Nat.beq (Nat.land c 1) 0) = true :=
      (CFSG.KC.LQT.P.allL_iff _ _).2 fun x hx => hp' x (List.mem_cons_of_mem _ hx)
    have ih := prep_wordK_pos hS PSI wd hl hrest
    rw [wordK_cons]
    cases z with
    | ofNat k =>
      have ec : icode (Int.ofNat k) = k + k := rfl
      rw [ec] at hc0 hcj ⊢
      have e1 : Nat.land (k + k) 1 = 0 := by
        change (k + k) &&& 1 = 0
        rw [Nat.and_one_is_mod]
        omega
      have e2 : Nat.shiftRight (k + k) 1 = k := by
        rw [shr_eq]
        omega
      have hprod : posProd gs (Int.ofNat k :: wd) = gs (k - 1) * posProd gs wd := by
        simp [posProd]
      rw [e1, e2, hprod]
      exact prep_pcomp (by decide) (hS (k - 1) (by omega)) ih
    | negSucc k =>
      have ec : icode (Int.negSucc k) = (k + 1) + (k + 1) + 1 := rfl
      have e1 : Nat.land ((k + 1) + (k + 1) + 1) 1 = 1 := by
        change ((k + 1) + (k + 1) + 1) &&& 1 = 1
        rw [Nat.and_one_is_mod]
        omega
      rw [ec, e1] at hz
      exact absurd hz (by decide)

@[expose] def ap (c : Equiv.Perm (Fin 1782)) (x : ℕ) : ℕ :=
  if h : x < 1782 then (c ⟨x, h⟩ : ℕ) else 0

theorem ap_lt (c : Equiv.Perm (Fin 1782)) (x : ℕ) : ap c x < 2 ^ 11 := by
  unfold ap
  split_ifs
  · exact lt_of_lt_of_le (c _).2 (by decide)
  · decide

theorem ap_mul (g c : Equiv.Perm (Fin 1782)) {x : ℕ} (hx : x < 1782) :
    ap (g * c) x = ap g (ap c x) := by
  simp [ap, hx, (c ⟨x, hx⟩).2]

theorem ap_one {x : ℕ} (hx : x < 1782) : ap 1 x = x := by simp [ap, hx]

@[expose] noncomputable def permKey (c : Equiv.Perm (Fin 1782)) : ℕ :=
  packP 30 (fun t => ap c (fldK idKey t)) id

theorem packP_congr {n : ℕ} {v v' p : ℕ → ℕ} (h : ∀ i < n, v i = v' i) :
    packP n v p = packP n v' p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [packP_succ, packP_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem fldK_permKey (c : Equiv.Perm (Fin 1782)) {t : ℕ} (ht : t < 30) :
    fldK (permKey c) t = ap c (fldK idKey t) :=
  (fldK_packP (n := 30) (p := id) (fun i _ => ap_lt c _) (fun _ _ _ _ e => e)).1 t ht

theorem fldK_permKey_ge (c : Equiv.Perm (Fin 1782)) {t : ℕ} (ht : 30 ≤ t) :
    fldK (permKey c) t = 0 :=
  (fldK_packP (n := 30) (p := id) (fun i _ => ap_lt c _) (fun _ _ _ _ e => e)).2 t
    (fun i hi e => by simp only [id] at e; omega)

theorem actK_permKey {P : ℕ} {g : Equiv.Perm (Fin 1782)} (hP : PRep 1782 11 P g)
    (hid : ∀ t < 30, fldK idKey t < 1782) (c : Equiv.Perm (Fin 1782)) :
    actK (permKey c) P = permKey (g * c) := by
  rw [actK_eq, permKey]
  refine packP_congr fun t ht => ?_
  rw [show fldK (packP 30 (fun t => ap c (fldK idKey t)) id) t = ap c (fldK idKey t) from
    fldK_permKey c ht, ap_mul g c (hid t ht)]
  unfold ap
  rw [dif_pos (hid t ht), dif_pos (c _).2]
  exact fldK_of_prep hP _

theorem fldK_eq_zero_of_shr {k t : ℕ} (hk : Nat.shiftRight k 330 = 0) (ht : 30 ≤ t) :
    fldK k t = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fldK, Nat.zero_testBit]
  have h := congrArg (fun x => Nat.testBit x (11 * t + i - 330)) hk
  simp only [Nat.zero_testBit] at h
  change (k >>> 330).testBit _ = false at h
  rw [Nat.testBit_shiftRight, show 330 + (11 * t + i - 330) = 11 * t + i by omega] at h
  rw [h, Bool.and_false]

theorem idKey_eq (hid : ∀ t < 30, fldK idKey t < 1782) (hk : Nat.shiftRight idKey 330 = 0) :
    idKey = permKey 1 := by
  apply fldK_ext
  intro t
  by_cases ht : t < 30
  · rw [fldK_permKey 1 ht, ap_one (hid t ht)]
  · rw [fldK_permKey_ge 1 (by omega), fldK_eq_zero_of_shr hk (by omega)]

end CFSG.KC.SuzNine

end
