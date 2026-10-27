module

public import CFSG.Certificates.Kernel.Spor.PK.BFS
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import Certificates.Data.Kernel.Spor.M11

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.M11

@[expose] def cycW (f : Nat → Nat) (i : Nat) : Nat → Nat → Nat → Nat
  | 0, _, c => c
  | k + 1, p, c => if f p = i then c else cycW f i k (f p) (c + 1)

@[expose] def cycF (n : Nat) (f : Nat → Nat) (i : Nat) : Nat := cycW f i n i 1

@[expose] def ordF (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldr (fun i s => Nat.lcm s (cycF n f i)) 1

private theorem cycRec_eq (w z i : Nat) (k : Nat) : ∀ p c : Nat,
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
      (fun _ ih p c => strictN (pg w (mask w) z p) (fun q => nIf(Nat.beq q i, c, ih q (Nat.succ c))))
      k p c = cycW (fd w z) i k p c := by
  induction k with
  | zero => intro p c; rfl
  | succ k ih =>
    intro p c
    have hpg : pg w (mask w) z p = fd w z p := pg_eq w z p
    show strictN (pg w (mask w) z p) _ = _
    rw [strictN_eq, nIf_eq, ih, cycW, hpg]
    simp only [Nat.beq_eq, Nat.succ_eq_add_one]

theorem cycLen_eq (n w z i : Nat) : cycLen n w (mask w) z i = cycF n (fd w z) i :=
  cycRec_eq w z i n i 1

theorem ordC_eq (n w z : Nat) : ordC n w (mask w) z = ordF n (fd w z) := by
  unfold ordC ordF
  rw [foldN_eq]
  simp only [cycLen_eq]

private theorem cycW_congr {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n)
    (h : ∀ x < n, f x = g x) (i : Nat) :
    ∀ (k p c : Nat), p < n → cycW f i k p c = cycW g i k p c := by
  intro k
  induction k with
  | zero => intro p c _; rfl
  | succ k ih =>
    intro p c hp
    rw [cycW, cycW, ← h p hp]
    by_cases hfp : f p = i
    · rw [if_pos hfp, if_pos hfp]
    · rw [if_neg hfp, if_neg hfp]
      exact ih (f p) (c + 1) (hf p hp)

theorem cycF_congr {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n) (h : ∀ x < n, f x = g x)
    {i : Nat} (hi : i < n) : cycF n f i = cycF n g i :=
  cycW_congr hf h i n i 1 hi

private theorem foldr_lcm_dvd_iff (a : Nat → Nat) (m : Nat) : ∀ l : List Nat,
    l.foldr (fun i s => Nat.lcm s (a i)) 1 ∣ m ↔ ∀ i ∈ l, a i ∣ m
  | [] => by simp
  | i :: l => by
    rw [List.foldr_cons, Nat.lcm_dvd_iff, foldr_lcm_dvd_iff a m l]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_comm

private theorem ordF_dvd_iff (n : Nat) (f : Nat → Nat) (m : Nat) :
    ordF n f ∣ m ↔ ∀ i < n, cycF n f i ∣ m := by
  unfold ordF
  rw [foldr_lcm_dvd_iff]
  simp only [List.mem_range]

private theorem cycF_dvd_ordF {n : Nat} (f : Nat → Nat) {i : Nat} (hi : i < n) :
    cycF n f i ∣ ordF n f :=
  (ordF_dvd_iff n f _).1 (Nat.dvd_refl _) i hi

private theorem ordF_eq_of_cyc {n : Nat} {f g : Nat → Nat}
    (h1 : ∀ i < n, ∃ j < n, cycF n f i = cycF n g j)
    (h2 : ∀ j < n, ∃ i < n, cycF n g j = cycF n f i) : ordF n f = ordF n g := by
  refine Nat.dvd_antisymm ((ordF_dvd_iff n f _).2 fun i hi => ?_)
    ((ordF_dvd_iff n g _).2 fun j hj => ?_)
  · obtain ⟨j, hj, e⟩ := h1 i hi
    rw [e]
    exact cycF_dvd_ordF g hj
  · obtain ⟨i, hi, e⟩ := h2 j hj
    rw [e]
    exact cycF_dvd_ordF f hi

theorem ordF_congr {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n) (h : ∀ x < n, f x = g x) :
    ordF n f = ordF n g :=
  ordF_eq_of_cyc (fun i hi => ⟨i, hi, cycF_congr hf h hi⟩)
    (fun j hj => ⟨j, hj, (cycF_congr hf h hj).symm⟩)

private theorem cycW_conj {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n) (hg : IsPermN n g)
    {i : Nat} (hi : i < n) :
    ∀ (k p c : Nat), p < n →
      cycW (fun x => g (f (finv n g x))) (g i) k (g p) c = cycW f i k p c := by
  intro k
  induction k with
  | zero => intro p c _; rfl
  | succ k ih =>
    intro p c hp
    have hfp : f p < n := hf p hp
    have h1 : g (f (finv n g (g p))) = g (f p) := by rw [finv_apply hg hp]
    rw [cycW, cycW]
    show (if g (f (finv n g (g p))) = g i then c else
        cycW (fun x => g (f (finv n g x))) (g i) k (g (f (finv n g (g p)))) (c + 1)) = _
    rw [h1]
    by_cases h : f p = i
    · rw [if_pos (congrArg g h), if_pos h]
    · rw [if_neg (fun e => h (hg.2 _ hfp _ hi e)), if_neg h]
      exact ih (f p) (c + 1) hfp

theorem cycF_conj {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n) (hg : IsPermN n g) {i : Nat}
    (hi : i < n) : cycF n (fun x => g (f (finv n g x))) (g i) = cycF n f i :=
  cycW_conj hf hg hi n i 1 hi

theorem ordF_conj {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n) (hg : IsPermN n g) :
    ordF n (fun x => g (f (finv n g x))) = ordF n f :=
  ordF_eq_of_cyc
    (fun i hi => by
      obtain ⟨j, hj, rfl⟩ := hg.surj hi
      exact ⟨j, hj, cycF_conj hf hg hj⟩)
    (fun j hj => ⟨g j, hg.1 j hj, (cycF_conj hf hg hj).symm⟩)

end CFSG.KS.PK

end
