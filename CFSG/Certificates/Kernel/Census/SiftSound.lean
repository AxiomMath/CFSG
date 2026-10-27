module

public import CFSG.Certificates.Kernel.Census.ToMain
import CFSG.Certificates.Kernel.Spor.SiftKComplete
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem siftK_complete {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {g : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hg : g = unpack n w G) (hG : Nat.shiftRight G (n * w) = 0)
    (hr : allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true)
    (h : siftA n (rawLevels n S base) base 0 g = true) :
    siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = true :=
  Orb.siftK_of_siftA hb hp hl hg hG hr h

end CFSG.KS.Raw

namespace CFSG.KC.Census

open CFSG.KC.Enum

theorem range_of_pvalid {n w G : Nat} (h : pvalid n w G = true) :
    allN n (fun i => Nat.blt (pg w (CFSG.KS.mask w) G i) n) = true := by
  unfold pvalid at h
  rw [CFSG.KS.Raw.strictB_eq] at h
  refine CFSG.KS.Raw.allN_of_forall fun i hi => ?_
  have h2 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at h2
  exact h2.1

theorem testBit_pset {w r j v : Nat} (hv : v < 2 ^ w) {i k : Nat} (hk : k < w) :
    (pset w r j v).testBit (w * i + k) = if i = j then v.testBit k else r.testBit (w * i + k) := by
  have hpg : at' w r j = r / 2 ^ (w * j) % 2 ^ w := by
    have e : at' w r j = (r >>> (w * j)) &&& (2 ^ w - 1) := by
      rw [← CFSG.KS.PF.mask_eq]
      rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.div_add_mod r (2 ^ (w * j))
  have h2 := Nat.div_add_mod (r / 2 ^ (w * j)) (2 ^ w)
  have hA := Nat.mod_lt r (Nat.two_pow_pos (w * j))
  have hf := Nat.mod_lt (r / 2 ^ (w * j)) (Nat.two_pow_pos w)
  generalize r % 2 ^ (w * j) = A at h1 hA
  generalize r / 2 ^ (w * j) / 2 ^ w = B at h2
  generalize r / 2 ^ (w * j) % 2 ^ w = f at h2 hf hpg
  rw [← h2] at h1
  have hset : pset w r j v = 2 ^ (w * j) * (2 ^ w * B + v) + A := by
    unfold pset
    rw [hpg, CFSG.KS.PF.shl_eq, CFSG.KS.PF.shl_eq]
    simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
    rw [← h1, Nat.mul_add, Nat.mul_add, Nat.mul_comm f, Nat.mul_comm v]
    omega
  rw [hset, ← h1, Nat.testBit_two_pow_mul_add _ hA, Nat.testBit_two_pow_mul_add _ hA,
    Nat.testBit_two_pow_mul_add _ hv, Nat.testBit_two_pow_mul_add _ hf]
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have m := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hij)
    rw [Nat.mul_succ] at m
    have hne : i ≠ j := by omega
    have hlt : w * i + k < w * j := by omega
    simp only [hne, hlt, ↓reduceIte]
  · have hlt : ¬ w * i + k < w * i := by omega
    have e : w * i + k - w * i = k := by omega
    simp only [hlt, e, hk, ↓reduceIte]
  · have m := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hij)
    rw [Nat.mul_succ] at m
    have hne : i ≠ j := by omega
    have hlt : ¬ w * i + k < w * j := by omega
    have hlt2 : ¬ w * i + k - w * j < w := by omega
    simp only [hne, hlt, hlt2, ↓reduceIte]

theorem at'_pset {w r j v : Nat} (hv : v < 2 ^ w) (j' : Nat) :
    at' w (pset w r j v) j' = if j' = j then v else at' w r j' := by
  apply Nat.eq_of_testBit_eq
  intro k
  have e := CFSG.KS.PF.testBit_pgM w (pset w r j v) j' k
  have er := CFSG.KS.PF.testBit_pgM w r j' k
  change (at' w (pset w r j v) j').testBit k = _ at e
  change (at' w r j').testBit k = _ at er
  rw [e]
  by_cases hk : k < w
  · rw [testBit_pset hv hk]
    by_cases hj : j' = j
    · simp only [hj, hk, ↓reduceIte, decide_true, Bool.true_and]
    · simp only [hj, hk, ↓reduceIte, decide_true, Bool.true_and, er]
  · have hv' : v.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
    by_cases hj : j' = j
    · simp only [hj, hk, ↓reduceIte, decide_false, Bool.false_and, hv']
    · simp only [hj, hk, ↓reduceIte, decide_false, Bool.false_and, er]

theorem at'_pinv {n w P : Nat} (hw : n ≤ 2 ^ w) (hlt : ∀ i < n, at' w P i < n)
    (hinj : ∀ i < n, ∀ j < n, at' w P i = at' w P j → i = j) :
    ∀ i < n, at' w (pinv n w P) (at' w P i) = i := by
  suffices key : ∀ k ≤ n, ∀ i < k, at' w ((List.range k).foldl (fun r i =>
      strictN r fun r => nIf(Nat.blt (at' w P i) n, pset w r (at' w P i) i, r)) 0) (at' w P i) = i
    from key n (Nat.le_refl n)
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro hk i hi
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      CFSG.KS.PF.strictN_eqP, show Nat.blt (at' w P k) n = true from Nat.blt_eq.mpr (hlt k hk)]
    dsimp only
    rw [at'_pset (by omega)]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte]
    · have hne : at' w P i ≠ at' w P k := fun e => hik (hinj i (by omega) k hk e)
      simp only [hne, ↓reduceIte]
      exact ih (by omega) i (by omega)

theorem pvalid_of_inj {n w P : Nat} (hw : n ≤ 2 ^ w) (hlt : ∀ i < n, at' w P i < n)
    (hinj : ∀ i < n, ∀ j < n, at' w P i = at' w P j → i = j) : pvalid n w P = true := by
  unfold pvalid
  rw [CFSG.KS.Raw.strictB_eq]
  refine List.all_eq_true.2 fun i hi => ?_
  have hi' := List.mem_range.1 hi
  simp only [Bool.and_eq_true, Nat.blt_eq]
  exact ⟨hlt i hi', Nat.beq_eq_true_eq _ _ ▸ at'_pinv hw hlt hinj i hi'⟩

theorem inj_of_pvalid {n w P : Nat} (h : pvalid n w P = true) :
    (∀ i < n, at' w P i < n) ∧ ∀ i < n, ∀ j < n, at' w P i = at' w P j → i = j := by
  unfold pvalid at h
  rw [CFSG.KS.Raw.strictB_eq] at h
  have hP : ∀ i < n, at' w P i < n ∧ at' w (pinv n w P) (at' w P i) = i := fun i hi => by
    have h2 := List.all_eq_true.1 h i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, Nat.blt_eq] at h2
    exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩
  refine ⟨fun i hi => (hP i hi).1, fun i hi j hj e => ?_⟩
  rw [← (hP i hi).2, ← (hP j hj).2, e]

theorem pvalid_pc {n w p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (_hp : canon1 n w p = true) (hpv : pvalid n w p = true) (_hq : canon1 n w q = true)
    (hqv : pvalid n w q = true) : pvalid n w (pc n w p q) = true := by
  obtain ⟨hpl, hpi⟩ := inj_of_pvalid hpv
  obtain ⟨hql, hqi⟩ := inj_of_pvalid hqv
  have e : ∀ i < n, at' w (pc n w p q) i = at' w p (at' w q i) := fun i hi =>
    CFSG.KS.PF.pg_pcomp hn hi
  refine pvalid_of_inj hw (fun i hi => ?_) (fun i hi j hj h => ?_)
  · rw [e i hi]
    exact hpl _ (hql i hi)
  · rw [e i hi, e j hj] at h
    exact hqi i hi j hj (hpi _ (hql i hi) _ (hql j hj) h)

theorem pvalid_of_penumOK {n w : Nat} {gs : Array Nat} {ps : List Nat} {c : ArrCertP}
    (h : penumOK n w gs ps c = true) {k : Nat} (hk : k < gs.size) : pvalid n w gs[k]! = true := by
  unfold penumOK at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1 k (List.mem_range.2 hk)

theorem ppointsOK_valid {n w : Nat} {gs : Array Nat} {c : ArrCertP} :
    ∀ (i : Nat) (us : List Nat) (es : List (Array Nat)) (ps ls : List Nat),
      ppointsOK n w gs c i us es ps ls = true → ∀ x ∈ us, pvalid n w x = true
  | _, [], _, _, _, _ => by simp
  | i, u :: us, es, ps, ls, h => by
    simp only [ppointsOK, ppointAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, h2⟩ := h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact ppointsOK_valid _ _ _ _ _ h2 x hx

theorem pvalid_pts_of_penumOK {n w : Nat} {gs : Array Nat} {ps : List Nat} {c : ArrCertP}
    (h : penumOK n w gs ps c = true) : ∀ x ∈ c.pts.toList, pvalid n w x = true := by
  unfold penumOK at h
  simp only [Bool.and_eq_true] at h
  exact ppointsOK_valid _ _ _ _ _ h.2.1.2

end CFSG.KC.Census
