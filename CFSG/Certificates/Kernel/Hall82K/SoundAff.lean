module

public import CFSG.Certificates.Kernel.Hall82K.SoundBase

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.CGT.Hall82

theorem testBit_lor36 {L : ℕ} (hL : L < 2 ^ 36) (u i : ℕ) :
    (L ||| u <<< 36).testBit i = if i < 36 then L.testBit i else u.testBit (i - 36) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 36
  · have h1 : ¬ i ≥ 36 := by omega
    simp [hi, h1]
  · have h1 : L.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : i ≥ 36 := by omega
    simp [hi, h1, h2]

theorem lor36_shr {L : ℕ} (hL : L < 2 ^ 36) (u : ℕ) : Nat.shiftRight (L ||| u <<< 36) 36 = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((L ||| u <<< 36) >>> 36).testBit i = _
  rw [Nat.testBit_shiftRight, testBit_lor36 hL]
  simp

theorem lor36_m36 {L : ℕ} (hL : L < 2 ^ 36) (u : ℕ) : Nat.land (L ||| u <<< 36) m36K = L := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hm : m36K = 2 ^ 36 - 1 := rfl
  change ((L ||| u <<< 36) &&& m36K).testBit i = _
  rw [Nat.testBit_and, testBit_lor36 hL, hm, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 36
  · simp [hi]
  · have h1 : L.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, h1]

theorem fld_lor36 {L : ℕ} (hL : L < 2 ^ 36) (u : ℕ) {s : ℕ} (hs : s ≤ 30) :
    fld (L ||| u <<< 36) s = fld L s := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h63 : (63 : ℕ) = 2 ^ 6 - 1 := rfl
  change (((L ||| u <<< 36) >>> s) &&& 63).testBit i = ((L >>> s) &&& 63).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    testBit_lor36 hL, h63, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 6
  · have h1 : s + i < 36 := by omega
    simp [hi, h1]
  · simp [hi]

theorem apL_lor36 {L : ℕ} (hL : L < 2 ^ 36) (u v : ℕ) : apL (L ||| u <<< 36) v = apL L v := by
  unfold apL
  rw [fld_lor36 hL u (by norm_num : (0 : ℕ) ≤ 30), fld_lor36 hL u (by norm_num : (6 : ℕ) ≤ 30),
    fld_lor36 hL u (by norm_num : (12 : ℕ) ≤ 30), fld_lor36 hL u (by norm_num : (18 : ℕ) ≤ 30),
    fld_lor36 hL u (by norm_num : (24 : ℕ) ≤ 30), fld_lor36 hL u (by norm_num : (30 : ℕ) ≤ 30)]

theorem compL_lor36 {L M : ℕ} (hL : L < 2 ^ 36) (hM : M < 2 ^ 36) (u w : ℕ) :
    compL (L ||| u <<< 36) (M ||| w <<< 36) = compL L M := by
  rw [compL_eq_enc6, compL_eq_enc6]
  simp only [apL_lor36 hL]
  rw [fld_lor36 hM w (by norm_num : (0 : ℕ) ≤ 30), fld_lor36 hM w (by norm_num : (6 : ℕ) ≤ 30),
    fld_lor36 hM w (by norm_num : (12 : ℕ) ≤ 30), fld_lor36 hM w (by norm_num : (18 : ℕ) ≤ 30),
    fld_lor36 hM w (by norm_num : (24 : ℕ) ≤ 30), fld_lor36 hM w (by norm_num : (30 : ℕ) ≤ 30)]

@[expose] def linPart (g : Fin 64 → Fin 64) : Fin 64 → Fin 64 := fun v => xorF (g v) (g 0)

@[expose] def IsAff (g : Fin 64 → Fin 64) : Prop :=
  ∀ v w, linPart g (xorF v w) = xorF (linPart g v) (linPart g w)

@[expose] def codeA (g : Fin 64 → Fin 64) : ℕ := codeL (linPart g) ||| (g 0).val <<< 36

theorem linPart_zero (g : Fin 64 → Fin 64) : linPart g 0 = 0 := xorF_self _

theorem eq_linPart (g : Fin 64 → Fin 64) (v : Fin 64) : g v = xorF (linPart g v) (g 0) := by
  rw [linPart, xorF_assoc, xorF_self, xorF_zero]

theorem codeA_shr (g : Fin 64 → Fin 64) : Nat.shiftRight (codeA g) 36 = (g 0).val :=
  lor36_shr (codeL_lt _) _

theorem codeA_m36 (g : Fin 64 → Fin 64) : Nat.land (codeA g) m36K = codeL (linPart g) :=
  lor36_m36 (codeL_lt _) _

theorem apL_codeA {g : Fin 64 → Fin 64} (hg : IsAff g) (v : Fin 64) :
    apL (codeA g) v.val = (linPart g v).val := by
  rw [codeA, apL_lor36 (codeL_lt _), apL_codeL hg]

theorem apA_codeA {g : Fin 64 → Fin 64} (hg : IsAff g) (v : Fin 64) :
    apA (codeA g) v.val = (g v).val := by
  unfold apA
  rw [apL_codeA hg, codeA_shr, eq_linPart g v, val_xorF]
  rfl

theorem codeA_inj {g h : Fin 64 → Fin 64} (hg : IsAff g) (hh : IsAff h)
    (e : codeA g = codeA h) : g = h :=
  funext fun v => Fin.ext (by rw [← apA_codeA hg, ← apA_codeA hh, e])

theorem xorF_cancel (a b c : Fin 64) : xorF (xorF (xorF a b) c) (xorF b c) = a := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [val_xorF, Nat.testBit_xor]
  cases (a : ℕ).testBit i <;> cases (b : ℕ).testBit i <;> cases (c : ℕ).testBit i <;> rfl

theorem linPart_comp {g h : Fin 64 → Fin 64} (hg : IsAff g) :
    linPart (fun v => g (h v)) = fun v => linPart g (linPart h v) := by
  funext v
  change xorF (g (h v)) (g (h 0)) = _
  rw [eq_linPart g (h v), eq_linPart g (h 0), eq_linPart h v, hg]
  exact xorF_cancel _ _ _

theorem isAff_comp {g h : Fin 64 → Fin 64} (hg : IsAff g) (hh : IsAff h) :
    IsAff (fun v => g (h v)) := by
  intro v w
  rw [linPart_comp hg]
  change linPart g (linPart h (xorF v w)) = _
  rw [hh, hg]

theorem compA_codeA {g h : Fin 64 → Fin 64} (hg : IsAff g) (hh : IsAff h) :
    compA (codeA g) (codeA h) = codeA (fun v => g (h v)) := by
  have e1 : compL (codeA g) (codeA h) = codeL (linPart (fun v => g (h v))) := by
    unfold codeA
    rw [compL_lor36 (codeL_lt _) (codeL_lt _), compL_eq_codeL, fnL_codeL hg, fnL_codeL hh,
      linPart_comp (h := h) hg]
  unfold compA
  rw [codeA_shr, apA_codeA hg, e1]
  rfl

theorem isAff_mul {g h : Equiv.Perm (Fin 64)} (hg : IsAff g) (hh : IsAff h) : IsAff ⇑(g * h) :=
  isAff_comp (g := ⇑g) (h := ⇑h) hg hh

theorem compA_codeA_mul {g h : Equiv.Perm (Fin 64)} (hg : IsAff g) (hh : IsAff h) :
    compA (codeA g) (codeA h) = codeA ⇑(g * h) :=
  compA_codeA (g := ⇑g) (h := ⇑h) hg hh

theorem linPart_transl (u : Fin 64) : linPart (transl u) = id := by
  funext v
  change xorF (xorF v u) (xorF 0 u) = v
  rw [zero_xorF, xorF_assoc, xorF_self, xorF_zero]

theorem isAff_transl (u : Fin 64) : IsAff (transl u) := by
  intro v w
  rw [linPart_transl]
  rfl

theorem codeL_id : codeL id = idK := rfl

theorem codeA_transl (u : Fin 64) : codeA (transl u) = trK u.val := by
  unfold codeA trK
  rw [linPart_transl, codeL_id]
  change idK ||| (xorF 0 u).val <<< 36 = _
  rw [zero_xorF]
  rfl

theorem codeA_one : codeA ⇑(1 : Equiv.Perm (Fin 64)) = idK := by
  have h := codeA_transl 0
  rw [transl_zero] at h
  exact h

theorem isAff_one : IsAff ⇑(1 : Equiv.Perm (Fin 64)) := by
  have h := isAff_transl 0
  rwa [transl_zero] at h

theorem xcodeK_formula : ∀ u : Fin 64, ∀ A B C : Bool,
    Nat.lor
      (Nat.lor (Nat.xor (bitN u.val 0) (bitN u.val 2))
        (Nat.lor (Nat.shiftLeft (bitN u.val 1) 1) (Nat.shiftLeft (bitN u.val 4) 2)))
      (Nat.lor (Nat.shiftLeft (b2n A) 3)
        (Nat.lor (Nat.shiftLeft (b2n B) 4) (Nat.shiftLeft (b2n C) 5))) =
    ((if u.val.testBit 0 = u.val.testBit 2 then 0 else 1) +
      2 * (if u.val.testBit 1 then 1 else 0) + 4 * (if u.val.testBit 4 then 1 else 0) +
      8 * (if A = true then 1 else 0) + 16 * (if B = true then 1 else 0) +
      32 * (if C = true then 1 else 0)) % 64 := by
  decide +kernel

theorem fld_codeL (f : Fin 64 → Fin 64) :
    fld (codeL f) 0 = (f 1).val ∧ fld (codeL f) 6 = (f 2).val ∧ fld (codeL f) 24 = (f 16).val := by
  obtain ⟨e0, e1, -, -, e4, -⟩ := fld_enc6 (f 1).2 (f 2).2 (f 4).2 (f 8).2 (f 16).2 (f 32).2
  exact ⟨e0, e1, e4⟩

theorem xcodeK_codeA (g : Equiv.Perm (Fin 64)) : xcodeK (codeA g) = (xcode g).val := by
  obtain ⟨e0, e1, e4⟩ := fld_codeL (linPart g)
  unfold xcodeK
  rw [codeA_shr]
  unfold codeA
  rw [fld_lor36 (codeL_lt _) _ (by norm_num : (0 : ℕ) ≤ 30),
    fld_lor36 (codeL_lt _) _ (by norm_num : (6 : ℕ) ≤ 30),
    fld_lor36 (codeL_lt _) _ (by norm_num : (24 : ℕ) ≤ 30), e0, e1, e4, xcodeK_formula]
  unfold xcode
  simp only [linPart, val_xorF]
  congr 3 <;> simp [nbeq_iff, bor_eq_true]

open CFSG.Monster.B.Co2 CFSG.RankThree.Native in
theorem permOfArr_eq_fnL {c : ℕ} {a : Array ℕ} (hca : codeArrK c a = true)
    (hinj : Function.Injective (fnL c)) (v : Fin 64) : permOfArr 64 a v = fnL c v := by
  have hrep : Rep 64 a (Equiv.ofBijective (fnL c) (Finite.injective_iff_bijective.1 hinj)) :=
    fun x => by rw [codeArrK_getElem hca x.2]; rfl
  rw [permOfArr_eq_of_rep hrep]
  rfl

theorem forall₂_getD {R : ℕ → Array ℕ → Prop} {L : List ℕ} {A : List (Array ℕ)}
    (h : List.Forall₂ R L A) : ∀ i < L.length, R (L.getD i 0) (A.getD i #[]) := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hr _ ih =>
    intro i hi
    cases i with
    | zero => exact hr
    | succ i => exact ih i (by simpa using hi)

theorem fnL_idK : fnL idK = id := by
  rw [← codeL_id]
  exact fnL_codeL (fun _ _ => rfl)

theorem fnL_inj_of_inv {r : ℕ} (h : compL r r = idK) : Function.Injective (fnL r) := by
  have e : ∀ v, fnL r (fnL r v) = v := fun v => by
    have := congrFun (fnL_compL r r) v
    rw [h, fnL_idK] at this
    exact this.symm
  exact Function.LeftInverse.injective e

theorem fnL_zero (c : ℕ) : fnL c 0 = 0 := by
  have h := fnL_add c 0 0
  rwa [xorF_self, xorF_self] at h

theorem linPart_of_add {g : Fin 64 → Fin 64} (hg : ∀ v w, g (xorF v w) = xorF (g v) (g w))
    (h0 : g 0 = 0) : linPart g = g := by
  funext v
  rw [linPart, h0, xorF_zero]

theorem isAff_of_add {g : Fin 64 → Fin 64} (hg : ∀ v w, g (xorF v w) = xorF (g v) (g w))
    (h0 : g 0 = 0) : IsAff g := by
  intro v w
  rw [linPart_of_add hg h0]
  exact hg v w

theorem rmK_lt : ∀ r ∈ rmK, r < 2 ^ 36 := by decide +kernel

section RM

variable (hrm : zipArrK rmK hallRMArr = true)
  (hinv : allL (fun r => Nat.beq (compL r r) idK) rmK = true)

include hrm hinv in
theorem hallRMPerm_eq (e : Fin 8) : ⇑(hallRMPerm e) = fnL (rmK.getD e.val 0) := by
  have hl : e.val < rmK.length := e.2
  have hmem : rmK.getD e.val 0 ∈ rmK := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hi := nbeq_iff.1 (allL_iff.1 hinv _ hmem)
  funext v
  exact permOfArr_eq_fnL (forall₂_getD (zipArrK_spec hrm) e.val hl) (fnL_inj_of_inv hi) v

include hrm hinv in
theorem hallRMPerm_mul_self (e : Fin 8) : hallRMPerm e * hallRMPerm e = 1 := by
  have hl : e.val < rmK.length := e.2
  have hmem : rmK.getD e.val 0 ∈ rmK := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hi := nbeq_iff.1 (allL_iff.1 hinv _ hmem)
  apply Equiv.ext
  intro v
  rw [Equiv.Perm.mul_apply, hallRMPerm_eq hrm hinv]
  have := congrFun (fnL_compL (rmK.getD e.val 0) (rmK.getD e.val 0)) v
  rw [hi, fnL_idK] at this
  exact this.symm

include hrm hinv in
theorem isAff_hallRMPerm (e : Fin 8) : IsAff (hallRMPerm e) := by
  rw [hallRMPerm_eq hrm hinv]
  exact isAff_of_add (fnL_add _) (fnL_zero _)

include hrm hinv in
theorem codeA_transl_mul (u : Fin 64) (e : Fin 8) :
    codeA ⇑(transl u * hallRMPerm e) = Nat.lor (rmK.getD e.val 0) (Nat.shiftLeft u.val 36) := by
  have hl : e.val < rmK.length := e.2
  have hmem : rmK.getD e.val 0 ∈ rmK := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hlin : linPart ⇑(transl u * hallRMPerm e) = fnL (rmK.getD e.val 0) := by
    funext v
    change xorF (xorF (hallRMPerm e v) u) (xorF (hallRMPerm e 0) u) = _
    rw [hallRMPerm_eq hrm hinv, fnL_zero, zero_xorF, xorF_assoc, xorF_self, xorF_zero]
  unfold codeA
  rw [hlin, codeL_fnL (rmK_lt _ hmem)]
  change _ ||| (xorF (hallRMPerm e 0) u).val <<< 36 = _
  rw [hallRMPerm_eq hrm hinv, fnL_zero, zero_xorF]
  rfl

include hrm hinv in
theorem codeA_mul_transl (u : Fin 64) (e : Fin 8) :
    codeA ⇑(hallRMPerm e * transl u) =
      Nat.lor (rmK.getD e.val 0) (Nat.shiftLeft (apL (rmK.getD e.val 0) u.val) 36) := by
  have hl : e.val < rmK.length := e.2
  have hmem : rmK.getD e.val 0 ∈ rmK := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hlin : linPart ⇑(hallRMPerm e * transl u) = fnL (rmK.getD e.val 0) := by
    funext v
    change xorF (hallRMPerm e (xorF v u)) (hallRMPerm e (xorF 0 u)) = _
    rw [hallRMPerm_eq hrm hinv, zero_xorF, fnL_add, xorF_assoc, xorF_self, xorF_zero]
  unfold codeA
  rw [hlin, codeL_fnL (rmK_lt _ hmem)]
  change _ ||| (hallRMPerm e (xorF 0 u)).val <<< 36 = _
  rw [hallRMPerm_eq hrm hinv, zero_xorF]
  rfl

include hrm hinv in
theorem isAff_transl_mul (u : Fin 64) (e : Fin 8) : IsAff ⇑(transl u * hallRMPerm e) :=
  isAff_mul (isAff_transl u) (isAff_hallRMPerm hrm hinv e)

include hrm hinv in
theorem x1_code {x : Equiv.Perm (Fin 64)} (hx : x ∈ hallX1) :
    IsAff x ∧ ∃ u ∈ u0K, ∃ r ∈ rmK, codeA x = Nat.lor r (Nat.shiftLeft u 36) := by
  obtain ⟨u, hu, e, rfl⟩ := hx
  have hl : e.val < rmK.length := e.2
  refine ⟨isAff_transl_mul hrm hinv u e, u.val, hu, rmK.getD e.val 0, ?_,
    codeA_transl_mul hrm hinv u e⟩
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_mem hl

theorem allX1_spec {p : ℕ → Bool} (h : allX1 p = true) :
    ∀ u ∈ u0K, ∀ r ∈ rmK, p (Nat.lor r (Nat.shiftLeft u 36)) = true := fun u hu r hr =>
  allL_iff.1 (allL_iff.1 h u hu) r hr

include hrm hinv in
theorem allX1_code {p : ℕ → Bool} (h : allX1 p = true) {x : Equiv.Perm (Fin 64)}
    (hx : x ∈ hallX1) : p (codeA x) = true := by
  obtain ⟨-, u, hu, r, hr, e⟩ := x1_code hrm hinv hx
  rw [e]
  exact allX1_spec h u hu r hr

end RM
