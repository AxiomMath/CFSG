module

public import CFSG.Certificates.Kernel.FixBoundK.Complete
public import CFSG.Certificates.Kernel.FixBoundK.PairSound
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.KC.FixBoundK.Pair

open CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.FixBoundK

theorem bit_eq_testBit (X i : ℕ) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem pw2_eq (w : ℕ) : pw2 w = 2 ^ w := by
  change 1 <<< w = _
  rw [Nat.shiftLeft_eq, one_mul]

theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  have h : fget X i w ≤ 2 ^ w - 1 := by
    change (X >>> (i * w)) &&& (pw2 w - 1) ≤ _
    rw [pw2_eq]
    exact Nat.and_le_right
  have := Nat.one_le_two_pow (n := w)
  omega

theorem xorSel_eq (mp s m : ℕ) : xorSel mp s m = xorL (fun j => fget mp j 6) s m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Nat.xor (nIf(bit s m, fget mp m 6, 0)) (xorSel mp s m) = _
    rw [ih, xorL, bit_eq_testBit]
    cases s.testBit m <;> rfl

@[expose] noncomputable def cperm (X : ℕ) : Equiv.Perm (Fin 24) := decode (decP X)

theorem decP_getElem! (X : ℕ) {p : ℕ} (hp : p < 24) : (decP X)[p]! = ap X p := by
  rw [getElem!_pos (decP X) p (by simpa [decP] using hp)]
  simp only [decP, List.getElem_toArray, List.getElem_map, List.getElem_range]
  rfl

theorem cperm_apply {X : ℕ} (hX : PermArr (decP X) = true) (p : Fin 24) :
    (cperm X p : ℕ) = ap X p := by
  rw [cperm, decode_apply hX, decP_getElem! X p.2]

theorem cperm_inj {X Y : ℕ} (hX : PermArr (decP X) = true) (hY : PermArr (decP Y) = true)
    (hkX : keyP (decP X) = X) (hkY : keyP (decP Y) = Y) (h : cperm X = cperm Y) : X = Y := by
  rw [← hkX, ← hkY, decode_inj hX hY h]

theorem idc_eq : idc = keyP idArr := by decide +kernel

theorem pA_apply {IV R μ : ℕ}
    (hv : ∀ j < 6, μ.testBit j = true → PermArr (decP (ivc IV (gI R j))) = true) (p : Fin 24) :
    pA IV R μ p = (prodM (fun j => cperm (ivc IV (gI R j))) μ p : ℕ) := by
  set h : ℕ → Equiv.Perm (Fin 24) := fun j => cperm (ivc IV (gI R j))
  have key : ∀ k ≤ 6, ∀ q : Fin 24,
      Nat.rec (motive := fun _ => ℕ → ℕ) (fun p => p)
        (fun j ih p => ih (nIf(bit μ j, ap (ivc IV (gI R j)) p, p))) k (q : ℕ) =
        (prodL h (List.range k) μ q : ℕ) := by
    intro k
    induction k with
    | zero => intro _ q; rfl
    | succ k ih =>
      intro hk q
      have e : prodL h (List.range (k + 1)) μ =
          prodL h (List.range k) μ * (if μ.testBit k then h k else 1) := by
        simp [prodL, List.range_succ]
      have harg : nIf(bit μ k, ap (ivc IV (gI R k)) q, q) =
          ((if μ.testBit k then h k else 1) q : ℕ) := by
        rw [bit_eq_testBit]
        cases hb : μ.testBit k
        · rfl
        · rw [if_pos rfl]
          exact (cperm_apply (hv k (by omega) hb) q).symm
      rw [e, Equiv.Perm.mul_apply, ← ih (Nat.le_of_succ_le hk)]
      change Nat.rec (motive := fun _ => ℕ → ℕ) (fun p => p)
        (fun j ih p => ih (nIf(bit μ j, ap (ivc IV (gI R j)) p, p))) k
          (nIf(bit μ k, ap (ivc IV (gI R k)) q, q)) = _
      rw [harg]
  exact key 6 le_rfl p

variable {rec : ℕ → ℕ}

theorem mem_sylowSub_iff
    (hmem : ∀ x, x ∈ sylowCert.pts ↔ PermArr x = true ∧ ∃ i < 1024, valF 120 (rec i) = keyP x)
    (hrec : ∀ i < 1024, PermArr (decP (valF 120 (rec i))) = true ∧
      keyP (decP (valF 120 (rec i))) = valF 120 (rec i))
    {x : Equiv.Perm (Fin 24)} : x ∈ sylowSub ↔ ∃ j < 1024, cperm (valF 120 (rec j)) = x := by
  rw [sylowSub_facts.2]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hs : sylowCert.pts[i]! ∈ sylowCert.pts := by
      rw [getElem!_pos sylowCert.pts i hi]
      exact Array.getElem_mem hi
    obtain ⟨hp, j, hj, e⟩ := (hmem _).1 hs
    exact ⟨j, hj, by rw [cperm, e, decP_keyP hp, pt]⟩
  · rintro ⟨j, hj, rfl⟩
    have hs := (hmem _).2 ⟨(hrec j hj).1, j, hj, (hrec j hj).2.symm⟩
    obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hs
    exact ⟨i, hi, by rw [pt, getElem!_pos sylowCert.pts i hi, e, cperm]⟩

theorem fget_IR_lt (IR i : ℕ) : fget IR i 10 < 1024 := fget_lt IR i 10

theorem IR_strictMono {IV IR : ℕ} (hinv : ∀ i < 191, invOK IV IR rec 191 i = true) {i j : ℕ}
    (hij : i < j) (hj : j < 191) : fget IR i 10 < fget IR j 10 := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := (invOK_spec (hinv j (by omega))).2.2.2 hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact lt_trans (ih h (by omega)) hs
    · exact hs

theorem exists_ivc_eq
    (hmem : ∀ x, x ∈ sylowCert.pts ↔ PermArr x = true ∧ ∃ i < 1024, valF 120 (rec i) = keyP x)
    (hrec : ∀ i < 1024, PermArr (decP (valF 120 (rec i))) = true ∧
      keyP (decP (valF 120 (rec i))) = valF 120 (rec i))
    (hlt : ∀ i j, i < j → j < 1024 → valF 120 (rec i) < valF 120 (rec j))
    {IV IR : ℕ} (hinv : ∀ i < 191, invOK IV IR rec 191 i = true)
    {x : Equiv.Perm (Fin 24)} (hx : x ∈ sylowSub) (hxx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ i < 191, cperm (ivc IV i) = x := by
  have hcode : ∀ i < 191, ivc IV i = valF 120 (rec (fget IR i 10)) := fun i hi =>
    (invOK_spec (hinv i hi)).1
  have hperm : ∀ i < 191, PermArr (decP (ivc IV i)) = true := fun i hi => by
    rw [hcode i hi]
    exact (hrec _ (fget_IR_lt IR i)).1
  set S : Set (Equiv.Perm (Fin 24)) := {x | x ∈ sylowSub ∧ x * x = 1 ∧ x ≠ 1} with hS
  set T : Set (Equiv.Perm (Fin 24)) := (fun i => cperm (ivc IV i)) '' {i | i < 191} with hT
  have hTS : T ⊆ S := by
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 191 := hi
    obtain ⟨h1, h2, h3, -⟩ := invOK_spec (hinv i hi')
    refine ⟨(mem_sylowSub_iff hmem hrec).2 ⟨_, fget_IR_lt IR i, by rw [← h1]⟩, ?_, ?_⟩
    · ext p
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, cperm_apply (hperm i hi'),
        cperm_apply (hperm i hi'), h2 p p.2]
    · intro e
      apply h3
      have hd : decP (ivc IV i) = idArr := decode_inj (hperm i hi') PermArr_idArr
        (by rw [decode_idArr]; exact e)
      rw [idc_eq, ← hd, h1, (hrec _ (fget_IR_lt IR i)).2]
  have hinj : Set.InjOn (fun i => cperm (ivc IV i)) {i | i < 191} := by
    intro i hi j hj e
    have hi' : i < 191 := hi
    have hj' : j < 191 := hj
    have hk : ∀ k < 191, keyP (decP (ivc IV k)) = ivc IV k := fun k hk => by
      rw [hcode k hk]
      exact (hrec _ (fget_IR_lt IR k)).2
    have he := cperm_inj (hperm i hi') (hperm j hj') (hk i hi') (hk j hj') e
    rw [hcode i hi', hcode j hj'] at he
    rcases lt_trichotomy i j with h | h | h
    · exact absurd he (ne_of_lt (hlt _ _ (IR_strictMono hinv h hj') (fget_IR_lt IR j)))
    · exact h
    · exact absurd he (ne_of_gt (hlt _ _ (IR_strictMono hinv h hi') (fget_IR_lt IR i)))
  have hTc : T.ncard = 191 := by
    rw [hT, Set.InjOn.ncard_image hinj]
    rw [show {i | i < 191} = ((Finset.range 191 : Finset ℕ) : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  have hST : T = S :=
    Set.eq_of_subset_of_ncard_le hTS (by rw [hTc, hS, ncard_sylowSub_involutions])
      (Set.toFinite S)
  have hxS : x ∈ S := ⟨hx, hxx, hx1⟩
  rw [← hST] at hxS
  obtain ⟨i, hi, e⟩ := hxS
  exact ⟨i, hi, e⟩

end CFSG.KC.FixBoundK.Pair

end
