module

public import Certificates.Data.Kernel.Spor.PermL
public import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.KS.PermL

open CFSG.KC.Enum CFSG.ONSchreier.Native

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by
  cases a <;> rfl

private theorem permRun_spec (n : Nat) :
    ∀ (l : List Nat) (cnt msk : Nat), permRun n l cnt msk = true →
      cnt + l.length = n ∧ (∀ x ∈ l, x < n ∧ msk.testBit x = false) ∧ l.Nodup := by
  intro l
  induction l with
  | nil =>
    intro cnt msk h
    simpa [permRun] using h
  | cons x xs ih =>
    intro cnt msk h
    have h' : permRun n (x :: xs) cnt msk = (Nat.blt x n &&
        (Nat.beq (Nat.land msk (Nat.shiftLeft 1 x)) 0 &&
          permRun n xs (cnt + 1) (Nat.lor msk (Nat.shiftLeft 1 x)))) := by
      simp only [permRun, bAnd_eq, strictB_eq]
    rw [h'] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨hx, hm, hr⟩ := h
    obtain ⟨h1, h2, h3⟩ := ih _ _ hr
    have hmx : msk.testBit x = false := by
      have := congrArg (fun m => m.testBit x) hm
      simpa [Nat.land_eq, Nat.shiftLeft_eq, Nat.testBit_and, Nat.one_mul,
        Nat.testBit_two_pow_self] using this
    refine ⟨by simp; omega, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨hx, hmx⟩
      · refine ⟨(h2 y hy).1, ?_⟩
        have := (h2 y hy).2
        simp only [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1
    · refine List.nodup_cons.mpr ⟨fun hxs => ?_, h3⟩
      have := (h2 x hxs).2
      simp [Nat.lor_eq, Nat.shiftLeft_eq, Nat.testBit_or, Nat.one_mul,
        Nat.testBit_two_pow_self] at this

private theorem allBelowN_of (n : Nat) (p : Nat → Bool) (h : ∀ i < n, p i = true) :
    allBelowN n p = true := by
  induction n with
  | zero => simp [allBelowN]
  | succ n ih =>
    have := ih (fun i hi => h i (by omega))
    simp only [allBelowN] at this ⊢
    simp [Nat.all_succ, this, h n (by omega)]

private theorem pinv_fold (n : Nat) (a : Array Nat)
    (hlt : ∀ i < n, a[i]! < n) (hinj : ∀ i < n, ∀ j < n, a[i]! = a[j]! → i = j) :
    ∀ m ≤ n,
      (List.foldl (fun b k => b.setIfInBounds a[k]! k) (Array.replicate n 0)
          (List.range' 0 m)).size = n ∧
        ∀ i < m, (List.foldl (fun b k => b.setIfInBounds a[k]! k) (Array.replicate n 0)
          (List.range' 0 m))[a[i]!]? = some i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨hs, hv⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    refine ⟨by simp [hs], fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hne : a[m]! ≠ a[i]! := fun he => by
        have := hinj m (by omega) i (by omega) he
        omega
      rw [Array.getElem?_setIfInBounds_ne hne]
      exact hv i hi
    · exact Array.getElem?_setIfInBounds_self_of_lt (by rw [hs]; exact hlt _ (by omega))

theorem permLK_sound_proved {n : Nat} {a : Array Nat} (h : permLK n a.toList = true) :
    a.size = n ∧ pisInv n a (pinvCand n a) = true := by
  obtain ⟨h1, h2, h3⟩ := permRun_spec n a.toList 0 0 h
  simp only [Nat.zero_add, Array.length_toList] at h1
  have hlt : ∀ i < n, a[i]! < n := by
    intro i hi
    rw [getElem!_pos a i (by omega)]
    exact (h2 _ (Array.getElem_mem_toList (by omega))).1
  have hinj : ∀ i < n, ∀ j < n, a[i]! = a[j]! → i = j := by
    intro i hi j hj he
    rw [getElem!_pos a i (by omega), getElem!_pos a j (by omega)] at he
    have hi' : i < a.toList.length := by simp; omega
    have hj' : j < a.toList.length := by simp; omega
    exact (h3.getElem_inj (hi := hi') (hj := hj')).mp he
  refine ⟨h1, ?_⟩
  have hc : pinvCand n a = List.foldl (fun b k => b.setIfInBounds a[k]! k)
      (Array.replicate n 0) (List.range' 0 n) := by
    simp [pinvCand]
  obtain ⟨hs, hv⟩ := pinv_fold n a hlt hinj n (Nat.le_refl n)
  rw [hc]
  apply allBelowN_of
  intro i hi
  have hl := hlt i hi
  have hr := hv i hi
  have hr' : (List.foldl (fun b k => b.setIfInBounds a[k]! k) (Array.replicate n 0)
      (List.range' 0 n))[a[i]!]! = i := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hr]
    rfl
  simp [hl, hr']

end CFSG.KS.PermL

end
