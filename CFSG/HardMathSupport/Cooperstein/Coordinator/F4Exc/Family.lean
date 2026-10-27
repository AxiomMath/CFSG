module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ChevIndep

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

@[expose] def f4Omega : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  ![![2, 3, 4, 2], ![3, 6, 8, 4], ![2, 4, 6, 3], ![1, 2, 3, 2]]

theorem reflect_f4Omega : ∀ s j : Fin Tag.F4.rank, j ≠ s → reflect .F4 j (f4Omega s) = f4Omega s := by
  decide +kernel

theorem f4Omega_mul_cartan : ∀ l j : Fin Tag.F4.rank,
    ∑ c, f4Omega c l * Tag.F4.cartan c j = if l = j then 1 else 0 := by
  decide +kernel

@[expose] def reflectLF (i : Fin Tag.F4.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun j : Fin Tag.F4.rank =>
    l.getD j 0 - if j = i then (List.finRange Tag.F4.rank).map
      (fun k => Tag.F4.cartan i k * l.getD k 0) |>.sum else 0

theorem ofFn_reflect (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ℤ) :
    List.ofFn (reflect .F4 i v) = reflectLF i (List.ofFn v) := by
  unfold reflectLF reflect
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have hs : ∑ k, Tag.F4.cartan i k * v k =
      ((List.finRange Tag.F4.rank).map (fun k => Tag.F4.cartan i k * (List.ofFn v).getD k 0)).sum := by
    rw [Fin.sum_univ_def]
    refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
    simp [List.getD_eq_getElem?_getD]
  rw [hs]
  by_cases hj : j = i <;> simp [hj]

theorem ofFn_foldr_reflect (l : List (Fin Tag.F4.rank)) (v : Fin Tag.F4.rank → ℤ) :
    List.ofFn (l.foldr (reflect .F4) v) = l.foldr reflectLF (List.ofFn v) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, ofFn_reflect, ih]

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

@[expose] def minorsL (a b : List ℤ) : List ℤ :=
  [a.getD 0 0 * b.getD 1 0 - a.getD 1 0 * b.getD 0 0, a.getD 0 0 * b.getD 2 0 - a.getD 2 0 * b.getD 0 0,
   a.getD 0 0 * b.getD 3 0 - a.getD 3 0 * b.getD 0 0, a.getD 1 0 * b.getD 2 0 - a.getD 2 0 * b.getD 1 0,
   a.getD 1 0 * b.getD 3 0 - a.getD 3 0 * b.getD 1 0, a.getD 2 0 * b.getD 3 0 - a.getD 3 0 * b.getD 2 0]

@[expose] def f4n (i : ℕ) (h : i < 4 := by decide) : Fin Tag.F4.rank := ⟨i, h⟩

@[expose] def minorF (x y : Fin Tag.F4.rank → ℤ) (c c' : Fin Tag.F4.rank) : ℤ :=
  x c * y c' - x c' * y c

theorem dvd_foldl_gcd_mul (d m : ℕ) (l : List ℤ) (hl : ∀ x ∈ l, (d : ℤ) ∣ (m : ℤ) * x) :
    ∀ g : ℕ, d ∣ m * g → d ∣ m * l.foldl (fun g x => Nat.gcd g x.natAbs) g := by
  induction l with
  | nil => intro g hg; exact hg
  | cons a t ih =>
    intro g hg
    refine (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ ?_)
    show d ∣ m * Nat.gcd g a.natAbs
    rw [← Nat.gcd_mul_left]
    refine Nat.dvd_gcd hg ?_
    have := hl a List.mem_cons_self
    have h2 : d ∣ (m * a).natAbs := Int.natCast_dvd.1 (by simpa using this)
    simpa [Int.natAbs_mul] using h2

theorem dvd_mul_contentL (d m : ℕ) (l : List ℤ) (hl : ∀ x ∈ l, (d : ℤ) ∣ (m : ℤ) * x) :
    d ∣ m * contentL l :=
  dvd_foldl_gcd_mul d m l hl 0 (by simp)

theorem dvd_of_content_one {x : Fin Tag.F4.rank → ℤ} (h : contentL (List.ofFn x) = 1) (d m : ℕ)
    (hc : ∀ c, (d : ℤ) ∣ (m : ℤ) * x c) : d ∣ m := by
  have h1 : d ∣ m * contentL (List.ofFn x) := by
    refine dvd_mul_contentL d m _ fun z hz => ?_
    rw [List.mem_ofFn] at hz
    obtain ⟨c, rfl⟩ := hz
    exact hc c
  rwa [h, Nat.mul_one] at h1

theorem not_dvd_minors {x y : Fin Tag.F4.rank → ℤ}
    (h : 1 ≤ contentL (minorsL (List.ofFn x) (List.ofFn y)) ∧
      contentL (minorsL (List.ofFn x) (List.ofFn y)) ≤ 2) (d : ℕ) (hd : 3 ≤ d) :
    ¬ ∀ c c', (d : ℤ) ∣ minorF x y c c' := by
  intro hc
  have h1 : d ∣ contentL (minorsL (List.ofFn x) (List.ofFn y)) := by
    refine dvd_contentL d _ fun z hz => ?_
    simp only [minorsL, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hc (f4n 0) (f4n 1)
      | exact hc (f4n 0) (f4n 2)
      | exact hc (f4n 0) (f4n 3)
      | exact hc (f4n 1) (f4n 2)
      | exact hc (f4n 1) (f4n 3)
      | exact hc (f4n 2) (f4n 3)
  have := Nat.le_of_dvd (by omega) h1
  omega

@[expose] def gamWords : List (List (List (Fin Tag.F4.rank))) :=
  ([
  [[0, 1, 2, 3, 1, 2, 1, 0], [1, 2, 3, 1, 2, 1, 0], [2, 3, 1, 2, 1, 0], [3, 1, 2, 1, 0], [1, 2, 1, 0], [3, 2, 1, 0], [2, 1, 0], [1, 0], [0], [3, 2, 0, 1, 0], [2, 0, 1, 0], [0, 1, 0]],
  [[0, 1, 2, 3, 1, 2, 0, 1], [1, 2, 3, 1, 2, 0, 1], [2, 3, 1, 2, 0, 1], [3, 1, 2, 0, 1], [1, 2, 0, 1], [3, 2, 0, 1], [2, 0, 1], [0, 1], [0, 1, 0], [3, 2, 1], [2, 1], [1]],
  [[3, 2, 1, 2, 3, 0, 1, 2], [2, 1, 2, 3, 0, 1, 2], [1, 2, 3, 0, 1, 2], [2, 3, 0, 1, 2], [3, 0, 1, 2], [0, 1, 2], [2, 3, 1, 2], [3, 1, 2], [1, 2], [3, 2], [2], [2, 3, 2]],
  [[3, 2, 1, 2, 0, 1, 2, 3], [2, 1, 2, 0, 1, 2, 3], [1, 2, 0, 1, 2, 3], [2, 0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3, 2], [2, 1, 2, 3], [1, 2, 3], [1, 2, 3, 2], [2, 3], [2, 3, 2], [3]]] : List (List (List (Fin 4))))

@[expose] def uWords : List (List (List (Fin Tag.F4.rank))) :=
  ([
  [[1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2, 0, 1], [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1], [1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1], [2, 3, 1, 2, 0, 1, 2, 0, 1], [3, 1, 2, 0, 1, 2, 0, 1], [1, 2, 0, 1, 2, 0, 1], []],
  [[2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0], [2, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2], [2, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2], [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2], [2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2]],
  [[3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2, 0, 1], [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1], [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 1, 2, 1], [1, 2, 3, 1, 2, 0, 1, 2, 3, 1, 2, 0, 1, 2, 0, 1], [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 1, 2, 1]],
  [[2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2], [1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2], [2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2], [1, 2, 0, 1, 2, 3, 2, 1, 2], [2, 0, 1, 2, 3, 2, 1, 2], [2, 1, 2, 3, 2, 1, 2], []]] : List (List (List (Fin 4))))

@[expose] def gamWord (s : Fin Tag.F4.rank) (i : ℕ) : List (Fin Tag.F4.rank) :=
  (gamWords.getD s []).getD i []

@[expose] def uWord (s : Fin Tag.F4.rank) (j : ℕ) : List (Fin Tag.F4.rank) :=
  (uWords.getD s []).getD j []

@[expose] def gamL (s : Fin Tag.F4.rank) (i : ℕ) : List ℤ :=
  (gamWord s i).foldr reflectLF (List.ofFn (Pi.single s (1 : ℤ)))

@[expose] def uvecL (s : Fin Tag.F4.rank) (j : ℕ) : List ℤ :=
  (uWord s j).foldr reflectLF (List.ofFn (f4Omega s))

theorem gamL_content : ∀ (s : Fin Tag.F4.rank) (i : Fin 12), contentL (gamL s i) = 1 := by
  decide +kernel

theorem gamL_minors : ∀ (s : Fin Tag.F4.rank) (i i' : Fin 12), i ≠ i' →
    1 ≤ contentL (minorsL (gamL s i) (gamL s i')) ∧ contentL (minorsL (gamL s i) (gamL s i')) ≤ 2 := by
  decide +kernel

theorem uWord_fix : ∀ (s : Fin Tag.F4.rank) (j : Fin 8),
    (uWord s j).foldr reflectLF (List.ofFn (Pi.single s (1 : ℤ))) = List.ofFn (Pi.single s (1 : ℤ)) := by
  decide +kernel

theorem uvecL_ne : ∀ (s : Fin Tag.F4.rank) (j j' : Fin 8), j ≠ j' → uvecL s j ≠ uvecL s j' := by
  decide +kernel

@[expose] def wF (s : Fin Tag.F4.rank) (i : ℕ) : WeylGroup .F4 :=
  (coxeterSystem .F4).wordProd (gamWord s i)

@[expose] def uF (s : Fin Tag.F4.rank) (j : ℕ) : WeylGroup .F4 :=
  (coxeterSystem .F4).wordProd (uWord s j)

@[expose] def betaL (s : Fin Tag.F4.rank) (i j : ℕ) : List ℤ :=
  (gamWord s i).foldr reflectLF ((uWord s j).foldr reflectLF (List.ofFn (f4Omega s)))

theorem ofFn_wF_single
    (s : Fin Tag.F4.rank) (i : ℕ) :
    List.ofFn (wF s i • (Pi.single s 1 : Fin Tag.F4.rank → ℤ)) = gamL s i := by
  simp only [wF, CurtisExc.wordProd_smul']
  rw [ofFn_foldr_reflect]
  rfl

theorem ofFn_uF_Omega
    (s : Fin Tag.F4.rank) (j : ℕ) : List.ofFn (uF s j • f4Omega s) = uvecL s j := by
  simp only [uF, CurtisExc.wordProd_smul']
  rw [ofFn_foldr_reflect]
  rfl

theorem ofFn_wF_uF_Omega
    (s : Fin Tag.F4.rank) (i j : ℕ) :
    List.ofFn (wF s i • (uF s j • f4Omega s)) = betaL s i j := by
  simp only [wF, uF, CurtisExc.wordProd_smul']
  rw [ofFn_foldr_reflect, ofFn_foldr_reflect]
  rfl

theorem family_props
    (s : Fin Tag.F4.rank) :
    (∀ j : Fin 8, uF s j • (Pi.single s 1 : Fin Tag.F4.rank → ℤ) = Pi.single s 1) ∧
      (∀ j j' : Fin 8, j ≠ j' → uF s j • f4Omega s ≠ uF s j' • f4Omega s) ∧
      (∀ i : Fin 12, ∀ d m : ℕ,
        (∀ c, (d : ℤ) ∣ (m : ℤ) * (wF s i • (Pi.single s 1 : Fin Tag.F4.rank → ℤ)) c) → d ∣ m) ∧
      (∀ i i' : Fin 12, i ≠ i' → ∀ d : ℕ, 3 ≤ d →
        ¬ ∀ c c', (d : ℤ) ∣ minorF (wF s i • (Pi.single s 1 : Fin Tag.F4.rank → ℤ))
          (wF s i' • (Pi.single s 1 : Fin Tag.F4.rank → ℤ)) c c') := by
  refine ⟨fun j => ?_, fun j j' hjj' h => ?_, fun i d m hdm => ?_, fun i i' hii' d hd => ?_⟩
  · simp only [uF, CurtisExc.wordProd_smul']
    refine List.ofFn_injective ?_
    rw [ofFn_foldr_reflect]
    exact uWord_fix s j
  · have h2 := congrArg List.ofFn h
    rw [ofFn_uF_Omega, ofFn_uF_Omega] at h2
    exact uvecL_ne s j j' hjj' h2
  · refine dvd_of_content_one ?_ d m hdm
    rw [ofFn_wF_single]
    exact gamL_content s i
  · apply not_dvd_minors _ d hd
    rw [ofFn_wF_single, ofFn_wF_single]
    exact gamL_minors s i i' hii'

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
