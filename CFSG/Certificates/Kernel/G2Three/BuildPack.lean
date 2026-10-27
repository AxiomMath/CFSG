module

public import CFSG.Certificates.Kernel.G2Three.Pack
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.G2Three

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U

variable {f LO RM CI ONE UP : ℕ}

@[expose] noncomputable def mulP (LO CI RM a b : ℕ) : ℕ := mul3s 14 196 LO CI RM a b

theorem getD_push_lt {α : Type} {acc : Array α} {x : α} {t : ℕ} (d : α) (ht : t < acc.size) :
    (acc.push x).getD t d = acc.getD t d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt ht,
    Array.getElem?_eq_getElem ht]

theorem getD_push_eq {α : Type} {acc : Array α} {x : α} (d : α) :
    (acc.push x).getD acc.size d = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
  rfl

theorem push_table_pk {start : List ℕ} {K : ℕ} {step : List ℕ → ℕ × ℕ → List ℕ}
    {stepP : ℕ → ℕ × ℕ → ℕ} {X : ℕ → ℕ}
    (hstep : ∀ x ps, canon14 x = true → ps.2 < K →
      canon14 (step x ps) = true ∧ pk (step x ps) = stepP (pk x) ps) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)),
      (∀ i < par.length, (par.getD i (0, 0)).1 < acc.size + i ∧ (par.getD i (0, 0)).2 < K ∧
        X (acc.size + i) = stepP (X (par.getD i (0, 0)).1) (par.getD i (0, 0))) →
      (∀ t < acc.size, canon14 (acc.getD t start) = true ∧ pk (acc.getD t start) = X t) →
      (par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).size =
          acc.size + par.length ∧
        ∀ t < acc.size + par.length,
          canon14 ((par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).getD
            t start) = true ∧
          pk ((par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).getD
            t start) = X t
  | [], acc, _, hacc => by simpa using hacc
  | ps :: par, acc, hpar, hacc => by
    have h0' := hpar 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0'
    obtain ⟨hp1, hp2, hp3⟩ := h0'
    obtain ⟨hc, hk⟩ := hacc ps.1 hp1
    obtain ⟨hc', hk'⟩ := hstep (acc.getD ps.1 start) ps hc hp2
    have hacc' : ∀ t < (acc.push (step (acc.getD ps.1 start) ps)).size,
        canon14 ((acc.push (step (acc.getD ps.1 start) ps)).getD t start) = true ∧
          pk ((acc.push (step (acc.getD ps.1 start) ps)).getD t start) = X t := by
      intro t ht
      rw [Array.size_push] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · rw [getD_push_lt start ht]
        exact hacc t ht
      · subst ht
        rw [getD_push_eq]
        exact ⟨hc', by rw [hk', hk, hp3]⟩
    have ih := push_table_pk hstep par (acc.push (step (acc.getD ps.1 start) ps))
      (fun i hi => by
        have := hpar (i + 1) (by simp; omega)
        simp only [List.getD_cons_succ, Array.size_push] at this ⊢
        refine ⟨by omega, this.2.1, ?_⟩
        rw [(by omega : acc.size + 1 + i = acc.size + (i + 1))]
        exact this.2.2)
      hacc'
    simp only [Array.size_push] at ih
    rw [List.foldl_cons, List.length_cons]
    refine ⟨by rw [ih.1]; omega, fun t ht => ih.2 t (by omega)⟩

theorem getD_canon {gens : List (List ℕ)} (hg : ∀ g ∈ gens, canon14 g = true) (d : List ℕ)
    (hd : canon14 d = true) (s : ℕ) : canon14 (gens.getD s d) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases h : gens[s]? with
  | none => exact hd
  | some g => exact hg g (List.mem_of_getElem? h)

theorem build_pk (hc : consts3OK 14 f 196 LO RM CI ONE UP = true) {gens : List (List ℕ)}
    (hg : ∀ g ∈ gens, canon14 g = true) {G : ℕ → ℕ}
    (hG : ∀ s < gens.length, pk (gens.getD s one14) = G s)
    {par : List (ℕ × ℕ)} {X : ℕ → ℕ} (h0 : X 0 = pk one14)
    (hpar : ∀ i < par.length, (par.getD i (0, 0)).1 ≤ i ∧ (par.getD i (0, 0)).2 < gens.length ∧
      X (i + 1) = mulP LO CI RM (X (par.getD i (0, 0)).1) (G (par.getD i (0, 0)).2)) :
    (build one14 mul14 gens par).size = par.length + 1 ∧
      ∀ t < par.length + 1, canon14 ((build one14 mul14 gens par).getD t one14) = true ∧
        pk ((build one14 mul14 gens par).getD t one14) = X t := by
  have key := push_table_pk (start := one14) (K := gens.length)
    (step := fun x ps => mul14 x (gens.getD ps.2 one14))
    (stepP := fun x ps => mulP LO CI RM x (G ps.2)) (X := X)
    (fun x ps hx hs => ⟨canon14_mul14 _ _, by
      rw [pk_mul14 hc hx (getD_canon hg one14 canon14_one14 _), hG _ hs]
      rfl⟩) par #[one14]
    (fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hpar i hi
      refine ⟨by rw [List.size_toArray, List.length_singleton]; omega, h2, ?_⟩
      rw [List.size_toArray, List.length_singleton, Nat.add_comm]
      exact h3)
    (fun t ht => by
      have : t = 0 := by simpa using ht
      subst this
      exact ⟨canon14_one14, by simpa using h0.symm⟩)
  unfold build
  simp only [List.size_toArray, List.length_singleton] at key
  exact ⟨by rw [key.1]; omega, fun t ht => key.2 t (by omega)⟩

theorem orbitBuild_pk (hc : consts3OK 14 f 196 LO RM CI ONE UP = true) {t0 : List ℕ}
    (ht0 : canon14 t0 = true) {gps : List (List ℕ)}
    (hg : ∀ s < gps.length, canon14 ((gps.getD s (one14 ++ one14)).take 196) = true ∧
      canon14 ((gps.getD s (one14 ++ one14)).drop 196) = true)
    {GA GB : ℕ → ℕ}
    (hG : ∀ s < gps.length, pk ((gps.getD s (one14 ++ one14)).take 196) = GA s ∧
      pk ((gps.getD s (one14 ++ one14)).drop 196) = GB s)
    {par : List (ℕ × ℕ)} {X : ℕ → ℕ} (h0 : X 0 = pk t0)
    (hpar : ∀ i < par.length, (par.getD i (0, 0)).1 ≤ i ∧ (par.getD i (0, 0)).2 < gps.length ∧
      X (i + 1) = mulP LO CI RM (mulP LO CI RM (GA (par.getD i (0, 0)).2)
        (X (par.getD i (0, 0)).1)) (GB (par.getD i (0, 0)).2)) :
    (orbitBuild t0 gps par).size = par.length + 1 ∧
      ∀ t < par.length + 1, canon14 ((orbitBuild t0 gps par).getD t t0) = true ∧
        pk ((orbitBuild t0 gps par).getD t t0) = X t := by
  have key := push_table_pk (start := t0) (K := gps.length)
    (step := fun x ps => conjStep (gps.getD ps.2 (one14 ++ one14)) x)
    (stepP := fun x ps => mulP LO CI RM (mulP LO CI RM (GA ps.2) x) (GB ps.2)) (X := X)
    (fun x ps hx hs => ⟨canon14_mul14 _ _, by
      obtain ⟨hl, hr⟩ := hg ps.2 hs
      obtain ⟨el, er⟩ := hG ps.2 hs
      unfold conjStep
      rw [pk_mul14 hc (canon14_mul14 _ _) hr, pk_mul14 hc hl hx, el, er]
      rfl⟩) par #[t0]
    (fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hpar i hi
      refine ⟨by rw [List.size_toArray, List.length_singleton]; omega, h2, ?_⟩
      rw [List.size_toArray, List.length_singleton, Nat.add_comm]
      exact h3)
    (fun t ht => by
      have : t = 0 := by simpa using ht
      subst this
      exact ⟨ht0, by simpa using h0.symm⟩)
  unfold orbitBuild
  simp only [List.size_toArray, List.length_singleton] at key
  exact ⟨by rw [key.1]; omega, fun t ht => key.2 t (by omega)⟩

theorem inj_of_sorted {n : ℕ} {X SRT SRI : ℕ → ℕ}
    (hs : ∀ i < n, SRT i < n ∧ SRI i < n ∧ SRI (SRT i) = i ∧ SRT (SRI i) = i)
    (hinc : ∀ i, i + 1 < n → X (SRT i) < X (SRT (i + 1))) :
    ∀ t < n, ∀ t' < n, X t = X t' → t = t' := by
  have hmono : ∀ i j, j < n → i < j → X (SRT i) < X (SRT j) := by
    intro i j hj hij
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact (ih (by omega) h).trans (hinc j hj)
      · subst h
        exact hinc i hj
  intro t ht t' ht' he
  obtain ⟨-, a1, -, a2⟩ := hs t ht
  obtain ⟨-, b1, -, b2⟩ := hs t' ht'
  rcases Nat.lt_trichotomy (SRI t) (SRI t') with h | h | h
  · have := hmono _ _ b1 h
    rw [a2, b2, he] at this
    omega
  · rw [← a2, ← b2, h]
  · have := hmono _ _ a1 h
    rw [a2, b2, he] at this
    omega

end CFSG.KC.G2Three

end
