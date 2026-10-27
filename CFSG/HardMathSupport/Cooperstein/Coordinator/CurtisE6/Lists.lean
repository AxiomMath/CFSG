module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.SortCheck
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.ClassSep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Wts

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

@[expose] def contentL (l : List ℤ) : ℕ := l.foldl (fun g x => Nat.gcd g x.natAbs) 0

theorem dvd_foldl_gcd (d : ℕ) (l : List ℤ) (hl : ∀ x ∈ l, (d : ℤ) ∣ x) :
    ∀ g : ℕ, d ∣ g → d ∣ l.foldl (fun g x => Nat.gcd g x.natAbs) g := by
  induction l with
  | nil => intro g hg; exact hg
  | cons a t ih =>
    intro g hg
    refine ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ ?_
    exact Nat.dvd_gcd hg (Int.natCast_dvd.1 (hl a List.mem_cons_self))

theorem dvd_contentL (d : ℕ) (l : List ℤ) (hl : ∀ x ∈ l, (d : ℤ) ∣ x) : d ∣ contentL l :=
  dvd_foldl_gcd d l hl 0 (dvd_zero d)

@[expose] def subL (a b : List ℤ) : List ℤ := List.zipWith (· - ·) a b

@[expose] def codeL (l : List ℤ) : ℕ := l.foldr (fun x a => (x + 64).toNat + 128 * a) 0

@[expose] def reflectL6 (i : N6) (l : List ℤ) : List ℤ :=
  List.ofFn fun j : N6 =>
    l.getD j 0 - if j = i then (List.finRange (Tag.rank .E6)).map
      (fun k => Tag.cartan .E6 i k * l.getD k 0) |>.sum else 0

theorem ofFn_reflect6 (i : N6) (v : N6 → ℤ) :
    List.ofFn (reflect Tag.E6 i v) = reflectL6 i (List.ofFn v) := by
  unfold reflectL6 reflect
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have hs : ∑ k, Tag.cartan .E6 i k * v k =
      ((List.finRange (Tag.rank .E6)).map
        (fun k => Tag.cartan .E6 i k * (List.ofFn v).getD k 0)).sum := by
    rw [Fin.sum_univ_def]
    refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
    simp [List.getD_eq_getElem?_getD]
  rw [hs]
  by_cases hj : j = i <;> simp [hj]

theorem ofFn_foldr_reflect6 (l : List N6) (v : N6 → ℤ) :
    List.ofFn (l.foldr (reflect Tag.E6) v) = l.foldr reflectL6 (List.ofFn v) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, ofFn_reflect6, ih]

@[expose] def refEL (j : N6) (l : List ℤ) : List ℤ :=
  List.ofFn fun i : N6 => l.getD i 0 - Tag.cartan .E6 i j * l.getD j 0

theorem ofFn_refE (j : N6) (v : N6 → ℤ) : List.ofFn (refE j v) = refEL j (List.ofFn v) := by
  unfold refEL refE
  refine congrArg List.ofFn (funext fun i => ?_)
  simp [List.getD_eq_getElem?_getD]

theorem ofFn_foldr_refEL (l : List N6) (v : N6 → ℤ) :
    List.ofFn (l.foldr refE v) = l.foldr refEL (List.ofFn v) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, ofFn_refE, ih]

theorem cont2_of_contentL {r : ℕ} {x y : Fin r → ℤ}
    (h : 1 ≤ contentL (subL (List.ofFn x) (List.ofFn y)) ∧
      contentL (subL (List.ofFn x) (List.ofFn y)) ≤ 2) : Cont2 (x - y) := by
  intro d hd
  have h1 : d ∣ contentL (subL (List.ofFn x) (List.ofFn y)) := by
    refine dvd_contentL d _ fun z hz => ?_
    have e : subL (List.ofFn x) (List.ofFn y) = List.ofFn (x - y) := by
      unfold subL
      refine List.ext_getElem (by simp) fun n h1 h2 => ?_
      simp
    rw [e, List.mem_ofFn] at hz
    obtain ⟨c, rfl⟩ := hz
    exact hd c
  have hc : contentL (subL (List.ofFn x) (List.ofFn y)) = 1 ∨
      contentL (subL (List.ofFn x) (List.ofFn y)) = 2 := by omega
  rcases hc with hc | hc <;> rw [hc] at h1
  · exact h1.trans (by norm_num)
  · exact h1

@[expose] def msortR (f : ℕ) (l : List ℕ) : List ℕ := (msortLoop f (l.map fun x => [x])).flatten

theorem msortR_perm (f : ℕ) (l : List ℕ) : (msortR f l).Perm l := by
  refine (msortLoop_perm f _).trans ?_
  induction l with
  | nil => exact List.Perm.refl _
  | cons a t ih => simpa using ih.cons a

theorem nodup_of_strictB_R {f : ℕ} {l : List ℕ} (h : strictB (msortR f l) = true) : l.Nodup :=
  (msortR_perm f l).nodup_iff.1 ((pairwise_of_strictB _ h).imp Nat.ne_of_lt)

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
