module

public import CFSG.LieType.Ree.LargeReeInvolutionFusionWord

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open scoped commutatorElement

@[expose] def fuel : ℕ := 100000

section Weq

@[expose] def inRange (w : Word) : Bool :=
  w.all fun f => Nat.ble 24 f.1 && Nat.ble f.1 47

theorem forall_of_inRange {w : Word} (h : inRange w = true) : ∀ f ∈ w, 24 ≤ f.1 ∧ f.1 ≤ 47 := by
  intro f hf
  simp only [inRange, List.all_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  exact h f hf

@[expose] def weq (n : ℕ) (w w' : Word) : Bool :=
  inRange w && inRange w' && collect n [] w == collect n [] w'

variable {R : Type} [CommRing R] [CharP R 2]

theorem wordEval_eq_of_weq
    {n : ℕ} {w w' : Word} (h : weq n w w' = true) (x : ℕ → R) :
    wordEval R x w = wordEval R x w' := by
  simp only [weq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hw, hw'⟩, hc⟩ := h
  have h1 := wordEval_collect x n [] w (by simp) (forall_of_inRange hw)
  have h2 := wordEval_collect x n [] w' (by simp) (forall_of_inRange hw')
  simp only [List.reverse_nil, List.nil_append] at h1 h2
  rw [← h1, ← h2, hc]

theorem comm_eq_of_weq
    {n : ℕ} {w₁ w₂ w₃ : Word}
    (h : weq n (w₁ ++ w₂) (w₃ ++ w₂ ++ w₁) = true) (x : ℕ → R) :
    ⁅wordEval R x w₁, wordEval R x w₂⁆ = wordEval R x w₃ := by
  have h1 := wordEval_eq_of_weq h x
  simp only [wordEval_append] at h1
  rw [commutatorElement_def]
  calc wordEval R x w₁ * wordEval R x w₂ * (wordEval R x w₁)⁻¹ * (wordEval R x w₂)⁻¹ =
      (wordEval R x w₃ * wordEval R x w₂ * wordEval R x w₁) * (wordEval R x w₁)⁻¹ *
        (wordEval R x w₂)⁻¹ := by rw [h1]
    _ = wordEval R x w₃ := by group

theorem wordEval_reverse
    (x : ℕ → R) (w : Word) :
    wordEval R x w.reverse = (wordEval R x w)⁻¹ := by
  induction w with
  | nil => simp [wordEval_nil]
  | cons f w ih =>
    have hf : wordEval R x [f] =
        (pinnedX F4.tag R (orbitCertRoot F4.tag f.1) (polyEval x f.2))⁻¹ := by
      rw [pinnedX_neg, CharTwo.neg_eq]
      simp [wordEval]
    rw [List.reverse_cons, wordEval_append, ih, hf, wordEval_cons, mul_inv_rev]

end Weq

section Fam

@[expose] def famWord (n : ℕ) (s s' : Poly) : Word :=
  match n with
  | 0 => [(24, s), (33, s')]
  | 1 => [(25, s), (27, s'), (30, polyMul (polyMul s s) s')]
  | 2 => [(28, s), (30, s')]
  | 3 => [(26, s), (34, s'), (39, polyMul (polyMul s s) s')]
  | 4 => [(36, s), (39, s')]
  | 5 => [(29, s), (37, s'), (46, polyMul (polyMul s s) s')]
  | 6 => [(43, s), (46, s')]
  | 7 => [(35, s), (32, s'), (47, polyMul (polyMul s s) s')]
  | 8 => [(44, s), (47, s')]
  | 9 => [(31, s), (40, s')]
  | 10 => [(38, s), (42, s')]
  | _ => [(41, s), (45, s')]

@[expose] noncomputable def fam
    (m : ℕ) (K : Type) [Field K] (n : ℕ) (c : K) : ModGL F4.tag K :=
  match n with
  | 0 => sylowA m K c
  | 1 => sylowB m K c 0
  | 2 => sylowB m K 0 c
  | 3 => sylowD m K c 0
  | 4 => sylowD m K 0 c
  | 5 => sylowF m K c 0
  | 6 => sylowF m K 0 c
  | 7 => sylowH m K c 0
  | 8 => sylowH m K 0 c
  | 9 => sylowJ m K c
  | 10 => sylowK m K c
  | _ => sylowL m K c

variable {m : ℕ} {K : Type} [Field K]

theorem wordEval_eq_prod_sylowX
    (x : ℕ → K) (w : Word) :
    wordEval K x w = (w.map fun f => sylowX K f.1 (polyEval x f.2)).prod := rfl

theorem sylowX_zero
    (r : ℕ) : sylowX K r (0 : K) = 1 := pinnedX_zero _ _ _

set_option linter.unusedSimpArgs false

theorem wordEval_famWord_0
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 0 s s') = fam m K 0 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowA m K _
  simp only [sylowA, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_1
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 1 s s') = fam m K 1 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowB m K _ 0
  simp only [sylowB, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_2
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 2 s s') = fam m K 2 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowB m K 0 _
  simp only [sylowB, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_3
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 3 s s') = fam m K 3 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowD m K _ 0
  simp only [sylowD, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_4
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 4 s s') = fam m K 4 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowD m K 0 _
  simp only [sylowD, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_5
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 5 s s') = fam m K 5 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowF m K _ 0
  simp only [sylowF, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_6
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 6 s s') = fam m K 6 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowF m K 0 _
  simp only [sylowF, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_7
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 7 s s') = fam m K 7 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowH m K _ 0
  simp only [sylowH, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_8
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 8 s s') = fam m K 8 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowH m K 0 _
  simp only [sylowH, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_9
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 9 s s') = fam m K 9 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowJ m K _
  simp only [sylowJ, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_10
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 10 s s') = fam m K 10 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowK m K _
  simp only [sylowK, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord_11
    [CharP K F4.prime] (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord 11 s s') = fam m K 11 (polyEval x s) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [wordEval_eq_prod_sylowX]
  simp only [famWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    polyEval_polyMul, h]
  show _ = sylowL m K _
  simp only [sylowL, sylowX_zero, largeReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add,
    one_mul, mul_one, sq, mul_assoc]

theorem wordEval_famWord
    [CharP K F4.prime] {n : ℕ} (hn : n ≤ 11) (x : ℕ → K) (s s' : Poly)
    (h : polyEval x s' = largeReeSigma m (polyEval x s)) :
    wordEval K x (famWord n s s') = fam m K n (polyEval x s) := by
  match n, hn with
  | 0, _ => exact wordEval_famWord_0 x s s' h
  | 1, _ => exact wordEval_famWord_1 x s s' h
  | 2, _ => exact wordEval_famWord_2 x s s' h
  | 3, _ => exact wordEval_famWord_3 x s s' h
  | 4, _ => exact wordEval_famWord_4 x s s' h
  | 5, _ => exact wordEval_famWord_5 x s s' h
  | 6, _ => exact wordEval_famWord_6 x s s' h
  | 7, _ => exact wordEval_famWord_7 x s s' h
  | 8, _ => exact wordEval_famWord_8 x s s' h
  | 9, _ => exact wordEval_famWord_9 x s s' h
  | 10, _ => exact wordEval_famWord_10 x s s' h
  | 11, _ => exact wordEval_famWord_11 x s s' h

end Fam

section CommFam

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

theorem polyEval_sigmaPoly (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : ℕ → K)
    (hx : ∀ n < 12, x (n + 12) = largeReeSigma m (x n)) {p : Poly}
    (hp : varsBelow 24 p = true) :
    polyEval x (sigmaPoly p) = largeReeSigma m (polyEval x p) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨σ, hσ, hσσ⟩ := exists_sigma (m := m) hK
  have := polyEval_polySubst_sigmaVar σ hσσ (n := 12) x (fun i hi => by rw [hx i hi, ← hσ]) hp
  rw [← hσ]
  exact this

theorem comm_fam
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {n i j k : ℕ} (hi : i ≤ 11) (hj : j ≤ 11)
    (hk : k ≤ 11) {p q r : Poly} (hp : varsBelow 24 p = true) (hq : varsBelow 24 q = true)
    (hr : varsBelow 24 r = true)
    (h : weq n (famWord i p (sigmaPoly p) ++ famWord j q (sigmaPoly q))
      (famWord k r (sigmaPoly r) ++ famWord j q (sigmaPoly q) ++ famWord i p (sigmaPoly p)) = true)
    (x : ℕ → K) (hx : ∀ n < 12, x (n + 12) = largeReeSigma m (x n)) :
    ⁅fam m K i (polyEval x p), fam m K j (polyEval x q)⁆ = fam m K k (polyEval x r) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨σ, hσ, hσσ⟩ := exists_sigma (m := m) hK
  have hs : ∀ p : Poly, varsBelow 24 p = true →
      polyEval x (sigmaPoly p) = largeReeSigma m (polyEval x p) := by
    intro p hp
    have := polyEval_polySubst_sigmaVar σ hσσ (n := 12) x
      (fun i hi => by rw [hx i hi, ← hσ]) hp
    rw [← hσ]
    exact this
  have e := comm_eq_of_weq h x
  rw [wordEval_famWord hi x p _ (hs p hp), wordEval_famWord hj x q _ (hs q hq),
    wordEval_famWord hk x r _ (hs r hr)] at e
  exact e

@[expose] def famProdWord (l : List (ℕ × Poly)) : Word :=
  l.flatMap fun e => famWord e.1 e.2 (sigmaPoly e.2)

theorem wordEval_famProdWord
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : ℕ → K)
    (hx : ∀ n < 12, x (n + 12) = largeReeSigma m (x n)) :
    ∀ l : List (ℕ × Poly), (∀ e ∈ l, e.1 ≤ 11 ∧ varsBelow 24 e.2 = true) →
      wordEval K x (famProdWord l) = (l.map fun e => fam m K e.1 (polyEval x e.2)).prod
  | [], _ => by simp [famProdWord, wordEval_nil]
  | e :: l, h => by
    have : CharP K 2 := ‹CharP K F4.prime›
    obtain ⟨σ, hσ, hσσ⟩ := exists_sigma (m := m) hK
    have hs : polyEval x (sigmaPoly e.2) = largeReeSigma m (polyEval x e.2) := by
      have := polyEval_polySubst_sigmaVar σ hσσ (n := 12) x
        (fun i hi => by rw [hx i hi, ← hσ]) (h e List.mem_cons_self).2
      rw [← hσ]
      exact this
    have ih := wordEval_famProdWord hK x hx l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have e1 : famProdWord (e :: l) = famWord e.1 e.2 (sigmaPoly e.2) ++ famProdWord l := by
      simp [famProdWord]
    rw [e1, wordEval_append, wordEval_famWord (h e List.mem_cons_self).1 x e.2 _ hs, ih]
    simp

theorem comm_famL
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {n i j : ℕ} (hi : i ≤ 11) (hj : j ≤ 11)
    {p q : Poly} (hp : varsBelow 24 p = true) (hq : varsBelow 24 q = true)
    {l : List (ℕ × Poly)} (hl : ∀ e ∈ l, e.1 ≤ 11 ∧ varsBelow 24 e.2 = true)
    (h : weq n (famWord i p (sigmaPoly p) ++ famWord j q (sigmaPoly q))
      (famProdWord l ++ famWord j q (sigmaPoly q) ++ famWord i p (sigmaPoly p)) = true)
    (x : ℕ → K) (hx : ∀ n < 12, x (n + 12) = largeReeSigma m (x n)) :
    ⁅fam m K i (polyEval x p), fam m K j (polyEval x q)⁆ =
      (l.map fun e => fam m K e.1 (polyEval x e.2)).prod := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨σ, hσ, hσσ⟩ := exists_sigma (m := m) hK
  have hs : ∀ p : Poly, varsBelow 24 p = true →
      polyEval x (sigmaPoly p) = largeReeSigma m (polyEval x p) := by
    intro p hp
    have := polyEval_polySubst_sigmaVar σ hσσ (n := 12) x
      (fun i hi => by rw [hx i hi, ← hσ]) hp
    rw [← hσ]
    exact this
  have e := comm_eq_of_weq h x
  rw [wordEval_famWord hi x p _ (hs p hp), wordEval_famWord hj x q _ (hs q hq),
    wordEval_famProdWord hK x hx l hl] at e
  exact e

end CommFam

section Weyl

@[expose] def img1 (r : ℕ) : ℕ := (weylOnePairs.lookup r).getD r

@[expose] def img2 (r : ℕ) : ℕ := (weylTwoPairs.lookup r).getD r

@[expose] def mapPos (img : ℕ → ℕ) (w : Word) : Word := w.map fun f => (img f.1, f.2)

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime]

omit [CharP K F4.prime] in
theorem wordEval_cons_sylowX
    (x : ℕ → K) (f : ℕ × Poly) (w : Word) :
    wordEval K x (f :: w) = sylowX K f.1 (polyEval x f.2) * wordEval K x w := rfl

theorem weylOne_conj_wordEval
    (x : ℕ → K) : ∀ w : Word,
    (∀ f ∈ w, (f.1, img1 f.1) ∈ weylOnePairs) →
      weylOne K * wordEval K x w * (weylOne K)⁻¹ = wordEval K x (mapPos img1 w)
  | [], _ => by simp [wordEval_nil, mapPos]
  | f :: w, h => by
    have h1 := weylOne_conj_sylowX (K := K) (h f List.mem_cons_self) (polyEval x f.2)
    have h2 := weylOne_conj_wordEval x w fun g hg => h g (List.mem_cons_of_mem _ hg)
    have e : mapPos img1 (f :: w) = (img1 f.1, f.2) :: mapPos img1 w := rfl
    rw [e, wordEval_cons_sylowX, wordEval_cons_sylowX]
    calc weylOne K * (sylowX K f.1 (polyEval x f.2) * wordEval K x w) * (weylOne K)⁻¹ =
        (weylOne K * sylowX K f.1 (polyEval x f.2) * (weylOne K)⁻¹) *
          (weylOne K * wordEval K x w * (weylOne K)⁻¹) := by group
      _ = _ := by rw [h1, h2]

theorem weylTwo_conj_wordEval
    (x : ℕ → K) : ∀ w : Word,
    (∀ f ∈ w, (f.1, img2 f.1) ∈ weylTwoPairs) →
      weylTwo K * wordEval K x w * (weylTwo K)⁻¹ = wordEval K x (mapPos img2 w)
  | [], _ => by simp [wordEval_nil, mapPos]
  | f :: w, h => by
    have h1 := weylTwo_conj_sylowX (K := K) (h f List.mem_cons_self) (polyEval x f.2)
    have h2 := weylTwo_conj_wordEval x w fun g hg => h g (List.mem_cons_of_mem _ hg)
    have e : mapPos img2 (f :: w) = (img2 f.1, f.2) :: mapPos img2 w := rfl
    rw [e, wordEval_cons_sylowX, wordEval_cons_sylowX]
    calc weylTwo K * (sylowX K f.1 (polyEval x f.2) * wordEval K x w) * (weylTwo K)⁻¹ =
        (weylTwo K * sylowX K f.1 (polyEval x f.2) * (weylTwo K)⁻¹) *
          (weylTwo K * wordEval K x w * (weylTwo K)⁻¹) := by group
      _ = _ := by rw [h1, h2]

@[expose] def weylCheck1 (n n' : ℕ) : Bool :=
  Nat.ble n 11 && Nat.ble n' 11 &&
    (famWord n [[0]] [[1]]).all (fun f => decide ((f.1, img1 f.1) ∈ weylOnePairs)) &&
      mapPos img1 (famWord n [[0]] [[1]]) == famWord n' [[0]] [[1]]

@[expose] def weylCheck2 (n n' : ℕ) : Bool :=
  Nat.ble n 11 && Nat.ble n' 11 &&
    (famWord n [[0]] [[1]]).all (fun f => decide ((f.1, img2 f.1) ∈ weylTwoPairs)) &&
      mapPos img2 (famWord n [[0]] [[1]]) == famWord n' [[0]] [[1]]

@[expose] def x01 (m : ℕ) (c : K) : ℕ → K := fun i => if i = 0 then c else if i = 1 then
  largeReeSigma m c else 0

theorem wordEval_famWord_x01
    {n : ℕ} (hn : n ≤ 11) (c : K) :
    wordEval K (x01 m c) (famWord n [[0]] [[1]]) = fam m K n c := by
  have h := wordEval_famWord (m := m) hn (x01 m c) [[0]] [[1]] (by simp [polyEval, monoEval, x01])
  rw [h]
  simp [polyEval, monoEval, x01]

theorem weylOne_conj_fam
    {n n' : ℕ} (h : weylCheck1 n n' = true) (c : K) :
    weylOne K * fam m K n c * (weylOne K)⁻¹ = fam m K n' c := by
  simp only [weylCheck1, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hn'⟩, hall⟩, hmap⟩ := h
  rw [← wordEval_famWord_x01 hn c, ← wordEval_famWord_x01 hn' c,
    weylOne_conj_wordEval (x01 m c) _ hall, hmap]

theorem weylTwo_conj_fam
    {n n' : ℕ} (h : weylCheck2 n n' = true) (c : K) :
    weylTwo K * fam m K n c * (weylTwo K)⁻¹ = fam m K n' c := by
  simp only [weylCheck2, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hn'⟩, hall⟩, hmap⟩ := h
  rw [← wordEval_famWord_x01 hn c, ← wordEval_famWord_x01 hn' c,
    weylTwo_conj_wordEval (x01 m c) _ hall, hmap]

end Weyl

section Coords

@[expose] def shiftWord (off : ℕ) (w : Word) : Word :=
  w.map fun f => (f.1, polySubst (fun i => [[i + off]]) f.2)

@[expose] def coordsOf (n : ℕ) (w : Word) : List Poly :=
  (List.range 24).map fun i => (((collect n [] w).find? fun f => f.1 == 24 + i).map (·.2)).getD []

variable {R : Type} [CommRing R] [CharP R 2]

theorem wordEval_shiftWord
    (off : ℕ) (x : ℕ → R) (w : Word) :
    wordEval R x (shiftWord off w) = wordEval R (fun n => x (n + off)) w := by
  have hφ : (fun i => polyEval x [[i + off]]) = fun i => x (i + off) :=
    funext fun i => by simp [polyEval, monoEval]
  unfold wordEval shiftWord
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_apply, polyEval_polySubst, hφ]

theorem eqs_of_wordEval_eq
    {n n' : ℕ} {w w' : Word}
    (h : collectCheck n w (coordsOf n w) = true) (h' : collectCheck n' w' (coordsOf n' w') = true)
    {x : ℕ → R} (hx : wordEval R x w = wordEval R x w') (i : ℕ) (hi : i < 24) :
    polyEval x (polyAdd ((coordsOf n w).getD i []) ((coordsOf n' w').getD i [])) = 0 := by
  have := (wordEval_eq_iff h h' x).1 hx ⟨i, hi⟩
  rw [polyEval_polyAdd, this, CharTwo.add_self_eq_zero]

@[expose] def killZ (zs : List ℕ) (p : Poly) : Poly :=
  polySubst (fun i => if zs.contains i then [] else [[i]]) p

theorem polyEval_killZ (x : ℕ → R) (zs : List ℕ) (hz : ∀ i ∈ zs, x i = 0) (p : Poly) :
    polyEval x (killZ zs p) = polyEval x p := by
  refine polyEval_polySubst_of x (fun i => ?_) p
  by_cases hi : zs.contains i = true
  · have : x i = 0 := hz i (by simpa using hi)
    simp only [hi, ↓reduceIte, this]
    rfl
  · have hi' : zs.contains i = false := by simpa using hi
    simp only [hi', Bool.false_eq_true, ↓reduceIte]
    simp [polyEval, monoEval]

@[expose] def twin (i : ℕ) : ℕ := if i < 12 then i + 12 else i - 12

@[expose] def runTrace (eqs : List Poly) : List ℕ → List (ℕ × ℕ) → Option (List ℕ)
  | zs, [] => some zs
  | zs, (e, v) :: tr =>
    if Nat.blt v 24 && killZ zs (eqs.getD e []) == [[v]] then
      runTrace eqs (v :: twin v :: zs) tr
    else none

theorem runTrace_sound {m : ℕ} {K : Type} [Field K] [CharP K 2] (x : ℕ → K)
    (hx : ∀ i < 12, x (i + 12) = largeReeSigma m (x i)) (eqs : List Poly)
    (heq : ∀ p ∈ eqs, polyEval x p = 0) :
    ∀ (tr : List (ℕ × ℕ)) (zs zs' : List ℕ), (∀ i ∈ zs, x i = 0) → runTrace eqs zs tr = some zs' →
      ∀ i ∈ zs', x i = 0
  | [], zs, zs', hz, h => by
    simp only [runTrace, Option.some.injEq] at h
    subst h
    exact hz
  | (e, v) :: tr, zs, zs', hz, h => by
    simp only [runTrace] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
      obtain ⟨hv, hk⟩ := hc
      have hp : polyEval x (eqs.getD e []) = 0 := by
        by_cases he : e < eqs.length
        · rw [List.getD_eq_getElem _ _ he]
          exact heq _ (List.getElem_mem he)
        · rw [List.getD_eq_default _ _ (by omega)]
          rfl
      have hxv : x v = 0 := by
        have h1 := polyEval_killZ x zs hz (eqs.getD e [])
        rw [hk, hp] at h1
        simpa [polyEval, monoEval] using h1
      have htw : x (twin v) = 0 := by
        unfold twin
        split
        · rw [hx v (by omega), hxv]
          exact largeReeSigma_zero
        · rename_i hv12
          have h2 := hx (v - 12) (by omega)
          rw [Nat.sub_add_cancel (by omega), hxv] at h2
          exact (largeReeSigma_eq_zero_iff _).1 h2.symm
      refine runTrace_sound x hx eqs heq tr _ zs' (fun i hi => ?_) h
      rcases List.mem_cons.1 hi with rfl | hi
      · exact hxv
      · rcases List.mem_cons.1 hi with rfl | hi
        · exact htw
        · exact hz i hi
    · simp at h

@[expose] def traceZeros (eqs : List Poly) (zs₀ : List ℕ) (tr : List (ℕ × ℕ)) (want : List ℕ) :
    Bool :=
  match runTrace eqs zs₀ tr with
  | some zs => want.all fun i => zs.contains i
  | none => false

theorem traceZeros_sound {m : ℕ} {K : Type} [Field K] [CharP K 2] (x : ℕ → K)
    (hx : ∀ i < 12, x (i + 12) = largeReeSigma m (x i)) (eqs : List Poly)
    (heq : ∀ p ∈ eqs, polyEval x p = 0) {zs₀ : List ℕ} (hz : ∀ i ∈ zs₀, x i = 0)
    {tr : List (ℕ × ℕ)} {want : List ℕ} (h : traceZeros eqs zs₀ tr want = true) :
    ∀ i ∈ want, x i = 0 := by
  unfold traceZeros at h
  split at h
  · rename_i zs hzs
    intro i hi
    simp only [List.all_eq_true, List.contains_iff_mem] at h
    exact runTrace_sound x hx eqs heq tr zs₀ zs hz hzs i (h i hi)
  · simp at h

end Coords

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4
