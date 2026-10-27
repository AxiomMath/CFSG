module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24CheckInputs
public import CFSG.Certificates.Kernel.LocalQTPermWCodes
public import CFSG.Certificates.Kernel.LocalQTEvalZKProved
public import CFSG.Certificates.Kernel.LocalQTTab2KSound
public import CFSG.Certificates.Kernel.LocalQTChainWSound
import CFSG.Certificates.Kernel.LocalQTPairsHSnd.Sims
import CFSG.Certificates.Kernel.LocalQTPairsHSnd.SortN
import CFSG.Certificates.Kernel.LocalQTPairsHSnd.Orbit
import CFSG.Certificates.Kernel.LocalQTPairsHSnd.Bfs
import CFSG.Certificates.Kernel.LocalQTPermWSnd.Gen

public section

namespace CFSG.KC.LQT.PH

open Equiv CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs
  CFSG.KC.LQT.W CFSG.KC.LQT.L CFSG.Sporadic.Mathieu
open scoped Pointwise

@[expose] def cX (x : X24) : ℕ := codeP (x : Perm (Fin 24))

theorem cX_mul (x y : X24) : cX (x * y) = CFSG.KC.LQT.P.mul 24 (cX x) (cX y) :=
  (CFSG.KC.LQT.P.code_mul (by norm_num) x.1 y.1).symm

theorem cX_inv (x : X24) : cX x⁻¹ = CFSG.KC.LQT.P.inv 24 (cX x) :=
  (CFSG.KC.LQT.P.code_inv (by norm_num) x.1).symm

theorem cX_one : cX 1 = CFSG.KC.LQT.P.one 24 := CFSG.KC.LQT.P.code_one.symm

theorem codeP_injective : Function.Injective (codeP : Perm (Fin 24) → ℕ) :=
  fun _ _ h => CFSG.KC.LQT.P.code_inj (by norm_num) h

theorem enc_code (x : X24) : enc x = encK 24 (cX x) := by
  have e : encK 24 (cX x) = Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => acc * 24 + CFSG.KC.LQT.P.img (cX x) (24 - 1 - k)) 24 := rfl
  rw [e, CFSG.KC.LQT.PW.horner 24 _ 24 le_rfl, enc, encPerm]
  congr 1
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Nat.sub_self,
    Nat.zero_add]
  exact (CFSG.KC.LQT.P.img_code (by norm_num) x.1 ⟨j, h2⟩).symm

theorem evalW_eq_evalG {G : Type*} [Group G] (S : List G) (w : List ℤ) :
    evalW S w = CFSG.QuasithinUnique.Setup.X1.evalG S w := by
  induction w with
  | nil => rfl
  | cons z w ih => rw [evalW, CFSG.QuasithinUnique.Setup.X1.evalG, ih]

theorem genX_code {cA cB : ℕ} (hA : cX m24a = cA) (hB : cX m24b = cB) (w : List ℤ) :
    cX (genX w) = CFSG.KC.LQT.W.evalZK 24 [cA, cB] w := by
  have hL : [cA, cB] = [(m24a : Perm (Fin 24)), (m24b : Perm (Fin 24))].map codeP := by
    rw [← hA, ← hB]
    rfl
  have ht : ((tabX (evalW [m24a, m24b] w) : X24) : Perm (Fin 24)) =
      (evalW [m24a, m24b] w : X24) := CFSG.Sporadic.Schreier.tab_eq _
  rw [hL, CFSG.KC.LQT.W.evalZK_codeP (by norm_num), genX, cX, ht, evalW_eq_evalG,
    CFSG.KC.LQT.W.coe_evalG]
  rfl

theorem cX_injective : Function.Injective cX := fun _ _ h => Subtype.ext (codeP_injective h)

private theorem tabX_eq (x : X24) : tabX x = x := Subtype.ext (CFSG.Sporadic.Schreier.tab_eq x.1)

private theorem lift_codes (p : X24 → Prop) : ∀ {L : List ℕ}, (∀ c ∈ L, ∃ y, p y ∧ cX y = c) →
    ∃ Tr : List X24, Tr.map cX = L ∧ ∀ y ∈ Tr, p y
  | [], _ => ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
  | c :: t, hex => by
    obtain ⟨y, hyp, hy⟩ := hex c List.mem_cons_self
    obtain ⟨Tr, hTr, hTrp⟩ := lift_codes p fun c' hc' => hex c' (List.mem_cons_of_mem _ hc')
    refine ⟨y :: Tr, by rw [List.map_cons, hy, hTr], fun y' hy' => ?_⟩
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact hyp
    · exact hTrp y' hy'

private theorem mem_iff_code_mem {Tr : List X24} {L : List ℕ} (h : Tr.map cX = L) (y : X24) :
    y ∈ Tr ↔ cX y ∈ L := by
  rw [← h]
  constructor
  · exact fun hy => List.mem_map_of_mem hy
  · intro hy
    obtain ⟨y', hy', e⟩ := List.mem_map.1 hy
    rw [← cX_injective e]
    exact hy'

private theorem map_code_val : ∀ l : List X24,
    (l.map Subtype.val).map (CFSG.KC.LQT.P.code : Perm (Fin 24) → ℕ) = l.map cX
  | [] => by simp only [List.map_nil]
  | x :: l => by
    rw [List.map_cons, List.map_cons, List.map_cons, map_code_val l]
    rfl

theorem enc_injective' : Function.Injective enc := fun _ _ h =>
  Subtype.ext (encPerm_injective (by norm_num) h)

theorem hkey_code (x : X24) : hkey x = hkK (cX x) := by
  rw [hkey, enc_code]
  rfl

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.LQT.Syl.letN y k = k y := by
  cases y <;> rfl

theorem sqK_zero (n y : ℕ) : CFSG.KC.LQT.Syl.sqK n y 0 = y := rfl

theorem sqK_succ (n y e : ℕ) :
    CFSG.KC.LQT.Syl.sqK n y (e + 1) = CFSG.KC.LQT.Syl.sqK n (CFSG.KC.LQT.P.mul n y y) e :=
  letN_eq _ _

theorem powK_zero (n s : ℕ) : CFSG.KC.LQT.P.pow n s 0 = CFSG.KC.LQT.P.one n := rfl

theorem powK_succ (n s k : ℕ) :
    CFSG.KC.LQT.P.pow n s (k + 1) = CFSG.KC.LQT.P.mul n (CFSG.KC.LQT.P.pow n s k) s := rfl

theorem cX_sq (x : X24) (e : ℕ) : cX (x ^ 2 ^ e) = CFSG.KC.LQT.Syl.sqK 24 (cX x) e := by
  induction e generalizing x with
  | zero => rw [pow_zero, pow_one, sqK_zero]
  | succ e ih =>
    have h1 : x ^ 2 ^ (e + 1) = (x * x) ^ 2 ^ e := by rw [pow_succ', pow_mul, sq]
    rw [h1, sqK_succ, ← cX_mul, ih]

theorem cX_pow (x : X24) (k : ℕ) : cX (x ^ k) = CFSG.KC.LQT.P.pow 24 (cX x) k := by
  induction k with
  | zero => rw [pow_zero, cX_one, powK_zero]
  | succ k ih => rw [pow_succ, cX_mul, ih, powK_succ]

theorem beq_enc (u v : X24) : (enc u == enc v) = Nat.beq (cX u) (cX v) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, enc_injective'.eq_iff, cX_injective.eq_iff]

theorem beq_code (u v : X24) : Nat.beq (cX u) (cX v) = decide (u = v) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, cX_injective.eq_iff, decide_eq_true_eq]

theorem andB_true {a b : Bool} : CFSG.KC.Ord.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [CFSG.KC.Ord.andB]

theorem orB_true {a b : Bool} : CFSG.KC.Ord.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [CFSG.KC.Ord.orB]

theorem impB_true {a b : Bool} (h : CFSG.KC.LQT.P.impB a b = true) (ha : a = true) : b = true := by
  subst ha
  exact h

theorem notB_eq (b : Bool) : CFSG.KC.Ord.notB b = !b := by
  cases b <;> rfl

theorem lenL_eq (l : List ℕ) : CFSG.KC.LQT.S.lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg Nat.succ ih

theorem filtL_eq (l : List ℕ) (f : ℕ → Bool) : CFSG.KC.LQT.S.filtL l f = l.filter f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => List ℕ) (CFSG.KC.LQT.S.filtL l f)
      (x :: CFSG.KC.LQT.S.filtL l f) (f x) = _
    rw [List.filter_cons, ih]
    cases f x <;> rfl

theorem list_single {l : List ℕ} {a : ℕ} (hnd : l.Nodup) (hall : ∀ c ∈ l, c = a) (hmem : a ∈ l) :
    l = [a] := by
  rcases l with _ | ⟨b, _ | ⟨c, t⟩⟩
  · exact absurd hmem (by simp)
  · rw [hall b (by simp)]
  · exfalso
    have hb := hall b (by simp)
    have hc := hall c (by simp)
    exact (List.nodup_cons.1 hnd).1 (by rw [hb, ← hc]; simp)

theorem memL_iff (c : ℕ) (l : List ℕ) : CFSG.KC.LQT.S.memL c l = true ↔ c ∈ l := by
  induction l with
  | nil => simp [CFSG.KC.LQT.S.memL]
  | cons x l ih =>
    change CFSG.KC.Ord.orB (Nat.beq c x) (CFSG.KC.LQT.S.memL c l) = true ↔ c ∈ x :: l
    rw [List.mem_cons, ← ih]
    cases h : Nat.beq c x
    · have : c ≠ x := Nat.ne_of_beq_eq_false h
      simp [CFSG.KC.Ord.orB, this]
    · have : c = x := Nat.eq_of_beq_eq_true h
      simp [CFSG.KC.Ord.orB, this]

theorem allL_iff (l : List ℕ) (f : ℕ → Bool) :
    CFSG.KC.LQT.P.allL l f = true ↔ ∀ c ∈ l, f c = true := by
  induction l with
  | nil => simp [CFSG.KC.LQT.P.allL]
  | cons x l ih =>
    change CFSG.KC.Ord.andB (f x) (CFSG.KC.LQT.P.allL l f) = true ↔ _
    rw [List.forall_mem_cons, ← ih]
    cases f x <;> simp [CFSG.KC.Ord.andB]

theorem eqL_eq {l m : List ℕ} (h : CFSG.KC.LQT.L.eqL l m = true) : l = m := by
  induction l generalizing m with
  | nil => cases m with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [CFSG.KC.LQT.L.eqL])
  | cons x l ih => cases m with
    | nil => exact absurd h (by simp [CFSG.KC.LQT.L.eqL])
    | cons y m =>
      change CFSG.KC.Ord.andB (Nat.beq x y) (CFSG.KC.LQT.L.eqL l m) = true at h
      cases hxy : Nat.beq x y
      · rw [hxy] at h
        exact absurd h (by simp [CFSG.KC.Ord.andB])
      · rw [hxy] at h
        rw [Nat.eq_of_beq_eq_true hxy, ih h]

theorem mem_codes {L : List X24} {LC : List ℕ} (hL : (L.map cX).Perm LC) (w : X24) :
    w ∈ L ↔ cX w ∈ LC := by
  rw [← hL.mem_iff, List.mem_map]
  constructor
  · exact fun h => ⟨w, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← cX_injective e]

theorem mem_enc {L : List X24} {LC : List ℕ} (hL : (L.map cX).Perm LC) (w : X24) :
    enc w ∈ L.map enc ↔ cX w ∈ LC := by
  rw [← mem_codes hL, List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    rwa [← enc_injective' e]
  · exact fun h => ⟨w, h, rfl⟩

theorem contains_enc {L : List X24} {LC : List ℕ} (hL : (L.map cX).Perm LC) (w : X24) :
    (L.map enc).contains (enc w) = CFSG.KC.LQT.S.memL (cX w) LC := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, memL_iff, mem_enc hL]

theorem decide_enc {L : List X24} {LC : List ℕ} (hL : (L.map cX).Perm LC) (w : X24) :
    decide (enc w ∈ L.map enc) = CFSG.KC.LQT.S.memL (cX w) LC := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, memL_iff, mem_enc hL]

theorem all_codes {L : List X24} {LC : List ℕ} (hL : (L.map cX).Perm LC) (g : X24 → Bool)
    (gk : ℕ → Bool) (hg : ∀ y, g y = gk (cX y)) : L.all g = CFSG.KC.LQT.P.allL LC gk := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allL_iff]
  constructor
  · intro h c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hL.mem_iff.2 hc)
    rw [← hg]
    exact h y hy
  · intro h y hy
    rw [hg]
    exact h _ (hL.mem_iff.1 (List.mem_map_of_mem hy))

theorem strictAsc_of_pairwise : ∀ {l : List ℕ}, l.Pairwise (· < ·) → strictAsc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [List.pairwise_cons] at h
    simp only [strictAsc, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1 b List.mem_cons_self, strictAsc_of_pairwise h.2⟩

theorem strictAsc_nat {l : List ℕ} (h : l.Nodup) :
    strictAsc (l.mergeSort fun a b => decide (a ≤ b)) = true := by
  apply strictAsc_of_pairwise
  have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have hn : (l.mergeSort fun a b => decide (a ≤ b)).Nodup := (List.mergeSort_perm l _).nodup_iff.2 h
  exact (hs.and hn).imp fun h => lt_of_le_of_ne (by simpa using h.1) h.2

theorem strictAsc_enc {L : List X24} (h : L.Nodup) :
    strictAsc ((L.map enc).mergeSort fun a b => decide (a ≤ b)) = true :=
  strictAsc_nat (h.map enc_injective')

theorem head_code {F : List X24} {c : ℕ} (hF : F.map cX = [c]) : cX (F.headD 1) = c := by
  rcases F with _ | ⟨x, _ | ⟨y, t⟩⟩
  · exact absurd hF (by simp)
  · rw [List.map_cons, List.map_nil, List.cons.injEq] at hF
    exact hF.1
  · exact absurd hF (by simp)

theorem filter_perm_codes (L : List X24) (hnd : L.Nodup) (Ps : List (Perm (Fin 24))) {PC : List ℕ}
    (hPC : Ps.map codeP = PC) (hd : PC.Nodup) (hmem : ∀ c ∈ PC, ∃ x ∈ L, cX x = c) :
    ((L.filter fun x => (Ps.map encPerm).contains (enc x)).map cX).Perm PC := by
  have key : ∀ x : X24, (Ps.map encPerm).contains (enc x) = true ↔ cX x ∈ PC := by
    intro x
    rw [List.contains_iff_mem, List.mem_map, ← hPC, List.mem_map]
    constructor
    · rintro ⟨g, hg, e⟩
      have : g = x.1 := encPerm_injective (by norm_num) e
      exact ⟨g, hg, by rw [this]; rfl⟩
    · rintro ⟨g, hg, e⟩
      have : g = x.1 := codeP_injective e
      exact ⟨g, hg, by rw [this]; rfl⟩
  refine (List.perm_ext_iff_of_nodup ((hnd.filter _).map cX_injective) hd).2 fun c => ?_
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).1 (List.mem_filter.1 hx).2
  · intro hc
    obtain ⟨x, hx, rfl⟩ := hmem c hc
    exact ⟨x, List.mem_filter.2 ⟨hx, (key x).2 hc⟩, rfl⟩

theorem sortN_perm (l : List ℕ) : (CFSG.KC.LQT.Syl.sortN l).Perm l := by
  have key : ∀ m, (Nat.rec (motive := fun _ => List (List ℕ)) (List.map (fun x => [x]) l)
      (fun _ ih => CFSG.KC.LQT.T2.passK ih) m).flatten.Perm l := by
    intro m
    induction m with
    | zero =>
      change (List.map (fun x => [x]) l).flatten.Perm l
      rw [CFSG.KC.LQT.T2.flatten_singletonsT]
    | succ m ih => exact (CFSG.KC.LQT.T2.passGoT_perm _ none).trans ih
  exact key 17

theorem sincK_nodup {l : List ℕ} (h : CFSG.KC.LQT.T2.sincK l = true) : l.Nodup :=
  (CFSG.KC.LQT.T2.sincA_spec l none h).1

private noncomputable def fiveGo (f : ℕ → ℕ) (Q : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun _ => false)
    (fun q _ ih seen => CFSG.KC.LQT.P.letB (f q) fun v => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih (List.cons v seen)) true
        (Nat.beq (CFSG.KC.LQT.S.lenL seen) 4))
      (ih seen) (CFSG.KC.LQT.S.memL v seen)) Q

private theorem fiveGo_cons (f : ℕ → ℕ) (q : ℕ) (Q seen : List ℕ) :
    fiveGo f (q :: Q) seen = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (fiveGo f Q (f q :: seen)) true
        (Nat.beq (CFSG.KC.LQT.S.lenL seen) 4))
      (fiveGo f Q seen) (CFSG.KC.LQT.S.memL (f q) seen) :=
  CFSG.KC.LQT.P.letB_eq (f q) fun v => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (fiveGo f Q (v :: seen)) true
      (Nat.beq (CFSG.KC.LQT.S.lenL seen) 4))
    (fiveGo f Q seen) (CFSG.KC.LQT.S.memL v seen)

private theorem fiveK_go (f : ℕ → ℕ) : ∀ (Q seen : List ℕ), fiveGo f Q seen = true →
    seen.Nodup → seen.length ≤ 4 →
    ∃ S : List ℕ, S.Nodup ∧ S.length = 5 ∧ ∀ v ∈ S, v ∈ seen ∨ v ∈ Q.map f
  | [], _, h, _, _ => absurd h Bool.false_ne_true
  | q :: Q, seen, h, hnd, hlen => by
    rw [fiveGo_cons] at h
    cases hm : CFSG.KC.LQT.S.memL (f q) seen
    · have hv : f q ∉ seen := fun hv => by rw [(memL_iff _ _).2 hv] at hm; cases hm
      cases hl : Nat.beq (CFSG.KC.LQT.S.lenL seen) 4
      · rw [hm, hl] at h
        have hl' : seen.length ≠ 4 := fun e => by
          rw [lenL_eq, e] at hl
          cases hl
        obtain ⟨S, hS, hS5, hSm⟩ := fiveK_go f Q (f q :: seen) h (List.nodup_cons.2 ⟨hv, hnd⟩)
          (by rw [List.length_cons]; omega)
        refine ⟨S, hS, hS5, fun v hvS => ?_⟩
        rcases hSm v hvS with hv' | hv'
        · rcases List.mem_cons.1 hv' with rfl | hv'
          · exact Or.inr (List.mem_map_of_mem List.mem_cons_self)
          · exact Or.inl hv'
        · exact Or.inr (List.mem_cons_of_mem _ hv')
      · have h4 : seen.length = 4 := by
          rw [← lenL_eq]
          exact Nat.eq_of_beq_eq_true hl
        refine ⟨f q :: seen, List.nodup_cons.2 ⟨hv, hnd⟩, by rw [List.length_cons, h4],
          fun v hvS => ?_⟩
        rcases List.mem_cons.1 hvS with rfl | hv'
        · exact Or.inr (List.mem_map_of_mem List.mem_cons_self)
        · exact Or.inl hv'
    · rw [hm] at h
      obtain ⟨S, hS, hS5, hSm⟩ := fiveK_go f Q seen h hnd hlen
      exact ⟨S, hS, hS5, fun v hvS => (hSm v hvS).imp id (List.mem_cons_of_mem _)⟩

theorem fiveK_sound (f : ℕ → ℕ) (Q : List ℕ) (h : fiveK f Q = true) :
    4 < (Q.map f).dedup.length := by
  obtain ⟨S, hS, hS5, hSm⟩ := fiveK_go f Q [] h List.nodup_nil (by simp)
  have hsub : S ⊆ (Q.map f).dedup := fun v hv => by
    rw [List.mem_dedup]
    exact (hSm v hv).resolve_left List.not_mem_nil
  have := hS.length_le_of_subset hsub
  omega

private theorem prod_mem_ball (gens : List X24) :
    ∀ l : List X24, (∀ y ∈ l, y ∈ gens) → l.prod ∈ CFSG.KC.LQT.PWSnd.Ball gens l.length
  | [], _ => by
    rw [List.prod_nil]
    exact CFSG.KC.LQT.PWSnd.one_mem_ball gens 0
  | y :: t, h => by
    rw [List.prod_cons, List.length_cons]
    exact CFSG.KC.LQT.PWSnd.mul_mem_ball gens (h y List.mem_cons_self)
      (prod_mem_ball gens t fun y' hy' => h y' (List.mem_cons_of_mem _ hy'))

private theorem lift_word (gens : List X24) (G : List (Perm (Fin 24)))
    (hG : ∀ σ, σ ∈ G ↔ ∃ x ∈ gens, (x : Perm (Fin 24)) = σ) :
    ∀ l : List (Perm (Fin 24)), (∀ g ∈ l, g ∈ G) →
      ∃ l' : List X24, (∀ y ∈ l', y ∈ gens) ∧ l'.length = l.length ∧
        ((l'.prod : X24) : Perm (Fin 24)) = l.prod
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, rfl, by simp⟩
  | g :: t, hl => by
    obtain ⟨y, hy, hyg⟩ := (hG g).1 (hl g List.mem_cons_self)
    obtain ⟨l', hl', hlen, hprod⟩ :=
      lift_word gens G hG t fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')
    refine ⟨y :: l', ?_, by rw [List.length_cons, List.length_cons, hlen], ?_⟩
    · intro y' hy'
      rcases List.mem_cons.1 hy' with rfl | hy'
      · exact hy
      · exact hl' y' hy'
    · rw [List.prod_cons, List.prod_cons, Subgroup.coe_mul, hyg, hprod]


theorem clH_sound (gens : List X24) {GC : List ℕ} (hG : (gens.map cX).Perm GC) (fuel d : ℕ)
    (hd : d ≤ fuel) (C : List Lvl) (W : List (List (List ℕ))) (hC : chainOK 24 C = true)
    (hIn : CFSG.KC.LQT.L.chainInj 24 C = true) (hg : grpC 24 C (chainF C) GC W d = true)
    (hk : ∀ x y : X24, inC 24 C (chainF C) (cX x) = true → inC 24 C (chainF C) (cX y) = true →
      hkey x = hkey y → x = y) :
    (closureListH tabX hkey gens fuel).Nodup ∧
      (closureListH tabX hkey gens fuel).length = chainF C ∧
      (∀ x, (x ∈ closureListH tabX hkey gens fuel ↔ inC 24 C (chainF C) (cX x) = true) ∧
        (x ∈ closureListH tabX hkey gens fuel ↔ x ∈ Subgroup.closure {g | g ∈ gens})) ∧
      ∀ σ : Perm (Fin 24), inC 24 C (chainF C) (codeP σ) = true →
        ∃ x ∈ closureListH tabX hkey gens fuel, cX x = codeP σ := by
  obtain ⟨G₀, hG₀code, hG₀gens⟩ := lift_codes (· ∈ gens) fun c hc =>
    List.mem_map.1 (hG.symm.subset hc)
  have hGcode : (G₀.map Subtype.val).map (CFSG.KC.LQT.P.code : Perm (Fin 24) → ℕ) = GC := by
    rw [map_code_val, hG₀code]
  have hGmem : ∀ σ, σ ∈ G₀.map Subtype.val ↔ ∃ x ∈ gens, (x : Perm (Fin 24)) = σ := by
    intro σ
    rw [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hG₀gens x hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (mem_iff_code_mem hG₀code x).2 (hG.subset (List.mem_map_of_mem hx)), rfl⟩
  have h24 : (24 : ℕ) ≤ 32 := by norm_num
  obtain ⟨hcl, hword⟩ :=
    CFSG.KC.LQT.CM.grpC_sound h24 hC hIn (G₀.map Subtype.val) (by rw [hGcode]; exact hg)
  have hCv := CFSG.KC.LQT.CM.chainP_lvOK (CFSG.KC.LQT.CM.chainP_of_ok hC hIn)
  have hinC : ∀ σ : Perm (Fin 24),
      inC 24 C (chainF C) (codeP σ) = true ↔ CFSG.KC.LQT.CM.InC 24 C σ :=
    fun σ => CFSG.KC.LQT.CM.inC_iff h24 hCv σ
  have hInBall : ∀ σ, CFSG.KC.LQT.CM.InC 24 C σ →
      ∃ x ∈ CFSG.KC.LQT.PWSnd.Ball gens fuel, (x : Perm (Fin 24)) = σ := by
    intro σ hσ
    obtain ⟨l, hl, hlen, hprod⟩ := hword σ hσ
    obtain ⟨l', hl', hlen', hprod'⟩ := lift_word gens _ hGmem l hl
    refine ⟨l'.prod, CFSG.KC.LQT.PWSnd.ball_mono gens (by omega) (prod_mem_ball gens l' hl'), ?_⟩
    rw [hprod', hprod]
  have hclInC : ∀ x : X24, x ∈ Subgroup.closure {g | g ∈ gens} →
      CFSG.KC.LQT.CM.InC 24 C (x : Perm (Fin 24)) := by
    intro x hx
    refine (hcl x.1).2 ?_
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact Subgroup.subset_closure ((hGmem g.1).2 ⟨g, hg, rfl⟩)
    | one =>
      rw [Subgroup.coe_one]
      exact Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      rw [Subgroup.coe_mul]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [Subgroup.coe_inv]
      exact Subgroup.inv_mem _ ha
  have hBallInC : ∀ x ∈ CFSG.KC.LQT.PWSnd.Ball gens fuel,
      CFSG.KC.LQT.CM.InC 24 C (x : Perm (Fin 24)) :=
    fun x hx => hclInC x (CFSG.KC.LQT.PWSnd.ball_subset_closure gens fuel hx)
  have hinj : ∀ x ∈ CFSG.KC.LQT.PWSnd.Ball gens fuel, ∀ y ∈ CFSG.KC.LQT.PWSnd.Ball gens fuel,
      hkey x = hkey y → x = y := fun x hx y hy h =>
    hk x y ((hinC x.1).2 (hBallInC x hx)) ((hinC y.1).2 (hBallInC y hy)) h
  obtain ⟨hnd, hmem⟩ := CFSG.KC.LQT.PWSnd.closureListH_spec tabX tabX_eq hkey gens fuel hinj
  have hball : ∀ x : X24, x ∈ CFSG.KC.LQT.PWSnd.Ball gens fuel ↔
      CFSG.KC.LQT.CM.InC 24 C (x : Perm (Fin 24)) := by
    intro x
    refine ⟨hBallInC x, fun hx => ?_⟩
    obtain ⟨x', hx', hxx'⟩ := hInBall x.1 hx
    have e : x' = x := Subtype.ext hxx'
    rw [← e]
    exact hx'
  refine ⟨hnd, ?_, fun x => ⟨?_, ?_⟩, ?_⟩
  · have hH : ∀ σ : Perm (Fin 24),
        σ ∈ ((closureListH tabX hkey gens fuel).map Subtype.val).toFinset ↔
          CFSG.KC.LQT.CM.InC 24 C σ := by
      intro σ
      rw [List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hball x).1 ((hmem x).1 hx)
      · intro hσ
        obtain ⟨x, hx, hxσ⟩ := hInBall σ hσ
        exact ⟨x, (hmem x).2 hx, hxσ⟩
    rw [← CFSG.KC.LQT.CM.card_inC h24 hC hIn, Nat.subtype_card _ hH,
      List.toFinset_card_of_nodup (List.Nodup.map Subtype.val_injective hnd), List.length_map]
  · rw [hmem, hball]
    exact (hinC x.1).symm
  · rw [hmem]
    exact ⟨fun hx => CFSG.KC.LQT.PWSnd.ball_subset_closure gens fuel hx,
      fun hx => (hball x).2 (hclInC x hx)⟩
  · intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := hInBall σ ((hinC σ).1 hσ)
    refine ⟨x, (hmem x).2 hx, ?_⟩
    show codeP x.1 = codeP σ
    rw [hxσ]

theorem grpS_imp {n : ℕ} (hn : n ≤ 32) {C : List Lvl} {G : List ℕ} {W : List (List (List ℕ))}
    {d : ℕ} (hC : chainOK n C = true) (hG : CFSG.KC.LQT.P.allL G (CFSG.KC.LQT.P.permK n) = true)
    (h : grpS n C (chainF C) G W d = true) :
    grpC n C (chainF C) G W d = true :=
  CFSG.KC.LQT.PHSnd.grpC_of_grpS hn hC hG h

@[expose] noncomputable def prodsK (n : ℕ) : List Lvl → ℕ → List ℕ
  | [], p => [p]
  | lv :: C, p => ((List.range n).filter fun j => CFSG.KC.LQT.S.getK lv.2.1 j != 0).flatMap
      fun j => prodsK n C (CFSG.KC.LQT.P.mul n p (CFSG.KC.LQT.S.getK lv.2.1 j))

@[expose] noncomputable def colLv (n : ℕ) (C : List Lvl) (f : ℕ → ℕ) (s : ℕ → Bool) (lv : Lvl)
    (p : ℕ) (acc : List ℕ) (m : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) acc
    (fun j accJ => Bool.rec (motive := fun _ => List ℕ)
      (CFSG.KC.LQT.T2.letL (CFSG.KC.LQT.P.mul n p (CFSG.KC.LQT.S.getK lv.2.1 j))
        fun q => colFrom n C f s q accJ) accJ
      (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0)) m

theorem colLv_succ (n : ℕ) (C : List Lvl) (f : ℕ → ℕ) (s : ℕ → Bool) (lv : Lvl) (p : ℕ)
    (acc : List ℕ) (m : ℕ) : colLv n C f s lv p acc (m + 1) =
      Bool.rec (motive := fun _ => List ℕ)
        (CFSG.KC.LQT.T2.letL (CFSG.KC.LQT.P.mul n p (CFSG.KC.LQT.S.getK lv.2.1 m))
          fun q => colFrom n C f s q (colLv n C f s lv p acc m)) (colLv n C f s lv p acc m)
        (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 m) 0) := rfl

theorem colFrom_perm (n : ℕ) (f : ℕ → ℕ) (s : ℕ → Bool) : ∀ (C : List Lvl) (p : ℕ) (acc : List ℕ),
    (colFrom n C f s p acc).Perm (((prodsK n C p).map f).filter s ++ acc)
  | [], p, acc => by
    change (CFSG.KC.LQT.T2.letL (f p) fun h => Bool.rec (motive := fun _ => List ℕ) acc
      (List.cons h acc) (s h)).Perm _
    rw [CFSG.KC.LQT.T2.letL_eq, prodsK, List.map_singleton, List.filter_singleton]
    cases s (f p) <;> exact List.Perm.refl _
  | lv :: C, p, acc => by
    have step : ∀ m, (colLv n C f s lv p acc m).Perm
        (((((List.range m).filter fun j => CFSG.KC.LQT.S.getK lv.2.1 j != 0).flatMap
          fun j => prodsK n C (CFSG.KC.LQT.P.mul n p (CFSG.KC.LQT.S.getK lv.2.1 j))).map f).filter
            s ++ acc) := by
      intro m
      induction m with
      | zero => exact List.Perm.refl _
      | succ m ih =>
        rw [colLv_succ, List.range_succ, List.filter_append, List.flatMap_append,
          List.map_append, List.filter_append, List.append_assoc]
        cases hb : Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 m) 0
        · have hne : (CFSG.KC.LQT.S.getK lv.2.1 m != 0) = true := by
            rw [bne_iff_ne]
            exact Nat.ne_of_beq_eq_false hb
          rw [CFSG.KC.LQT.T2.letL_eq]
          simp only [List.filter_singleton, hne, cond_true, List.flatMap_singleton]
          refine (colFrom_perm n f s C _ _).trans ((ih.append_left _).trans ?_)
          rw [← List.append_assoc, ← List.append_assoc]
          exact List.perm_append_comm.append_right acc
        · have heq : (CFSG.KC.LQT.S.getK lv.2.1 m != 0) = false := by
            rw [bne_eq_false_iff_eq]
            exact Nat.eq_of_beq_eq_true hb
          simp only [List.filter_singleton, heq, List.flatMap_nil, List.map_nil, List.filter_nil,
            List.nil_append]
          exact ih
    have e : colFrom n (lv :: C) f s p acc = colLv n C f s lv p acc n := rfl
    rw [e]
    exact step n

theorem code_mem_prodsK : ∀ (C : List Lvl), (∀ lv ∈ C, CFSG.KC.LQT.CM.LvOK 24 lv) →
    ∀ (π σ : Perm (Fin 24)), CFSG.KC.LQT.CM.InC 24 C σ →
      CFSG.KC.LQT.P.code (π * σ) ∈ prodsK 24 C (CFSG.KC.LQT.P.code π)
  | [], _, π, σ, hσ => by
    simp only [CFSG.KC.LQT.CM.InC, CFSG.KC.LQT.CM.sift] at hσ
    split_ifs at hσ with e
    · rw [CFSG.KC.LQT.P.code_one] at e
      rw [CFSG.KC.LQT.P.code_inj (by norm_num) e, mul_one]
      exact List.mem_singleton_self _
    · exact absurd hσ (by simp)
  | lv :: C, hC, π, σ, hσ => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ :=
      CFSG.KC.LQT.CM.sift_cons_code (by norm_num) (hC lv (List.mem_cons_self ..)) σ hk
    have ih := code_mem_prodsK C (fun l hl => hC l (List.mem_cons_of_mem _ hl)) (π * τ) (τ⁻¹ * σ)
      (by rw [CFSG.KC.LQT.CM.InC, h']; rfl)
    rw [mul_assoc, mul_inv_cancel_left, ← CFSG.KC.LQT.P.code_mul (by norm_num), hτ] at ih
    rw [prodsK, List.mem_flatMap]
    refine ⟨j, List.mem_filter.2 ⟨List.mem_range.2 hj, ?_⟩, ih⟩
    rw [bne_iff_ne]
    exact e

theorem hk_radix (C : List Lvl) (hC : chainOK 24 C = true)
    (hIn : CFSG.KC.LQT.L.chainInj 24 C = true) (R : ℕ) (hR : 0 < R)
    (hk : ∀ r < R, hkR 24 C R r = true) (x y : X24) (hx : inC 24 C (chainF C) (cX x) = true)
    (hy : inC 24 C (chainF C) (cX y) = true) (h : hkey x = hkey y) : x = y := by
  have hlv : ∀ lv ∈ C, CFSG.KC.LQT.CM.LvOK 24 lv :=
    CFSG.KC.LQT.CM.all_lvOK C [] (by rw [← CFSG.KC.LQT.CM.chainOK_eq]; exact hC) hIn
  have hkx : hkey x = hkK (cX x) := hkey_code x
  have hky : hkey y = hkK (cX y) := hkey_code y
  have hP0 : 0 < hP := by unfold hP; norm_num
  set v := hkK (cX x) with hv
  have hvlt : v < hP := Nat.mod_lt _ hP0
  set r := v * R / hP with hr
  have hrR : r < R := by
    rw [hr, Nat.div_lt_iff_lt_mul hP0]
    exact Nat.mul_lt_mul_of_lt_of_le hvlt le_rfl hR |>.trans_eq (Nat.mul_comm _ _)
  have hin : ∀ c, hkK c = v → inRange R r (hkK c) = true := by
    intro c hc
    rw [hc]
    exact Nat.beq_refl _
  have hnd : ((((prodsK 24 C (CFSG.KC.LQT.P.one 24)).filter fun c => inRange R r (hkK c)).map
      hkK)).Nodup := by
    have h1 := sincK_nodup (hk r hrR)
    rw [(sortN_perm _).nodup_iff] at h1
    have h2 := (colFrom_perm 24 hkK (inRange R r) C (CFSG.KC.LQT.P.one 24) []).nodup_iff.1 h1
    rw [List.append_nil, List.filter_map] at h2
    exact h2
  have hmem : ∀ z : X24, inC 24 C (chainF C) (cX z) = true → hkK (cX z) = v →
      cX z ∈ (prodsK 24 C (CFSG.KC.LQT.P.one 24)).filter fun c => inRange R r (hkK c) := by
    intro z hz hzv
    refine List.mem_filter.2 ⟨?_, hin _ hzv⟩
    have hs := (CFSG.KC.LQT.CM.inC_iff (by norm_num) hlv z.1).1 hz
    have := code_mem_prodsK C hlv 1 z.1 hs
    rwa [one_mul, ← CFSG.KC.LQT.P.code_one] at this
  have hyv : hkK (cX y) = v := by rw [← hky, ← h, hkx]
  exact cX_injective (List.inj_on_of_nodup_map hnd (hmem x hx rfl) (hmem y hy hyv)
    (by rw [hyv]))

theorem sincA_pairwise : ∀ (l : List ℕ) (o : Option ℕ), CFSG.KC.LQT.T2.sincA l o = true →
    l.Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | x :: l, o, h => by
    have h' : CFSG.KC.Ord.andB (Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o)
        (CFSG.KC.LQT.T2.sincA l (some x)) = true := h
    rw [andB_true] at h'
    refine List.Pairwise.cons (fun z hz => ?_) (sincA_pairwise l (some x) h'.2)
    exact (CFSG.KC.LQT.T2.sincA_spec l (some x) h'.2).2 x rfl z hz

private theorem getK_Syl_eq {α : Type} : ∀ (l : List α) (i : ℕ) (d : α),
    CFSG.KC.LQT.Syl.getK l i d = l.getD i d
  | [], _, _ => by rw [List.getD_nil]; rfl
  | _ :: _, 0, _ => by rw [List.getD_cons_zero]; rfl
  | _ :: t, i + 1, d => by
    rw [List.getD_cons_succ]
    exact getK_Syl_eq t i d

private theorem getK_S_eq : ∀ (l : List ℕ) (i : ℕ), CFSG.KC.LQT.S.getK l i = l.getD i 0
  | [], _ => rfl
  | x :: t, i => by
    change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.LQT.S.getK t (Nat.sub i 1)) x
      (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      have e : Nat.beq (i + 1) 0 = false := rfl
      rw [e]
      dsimp only
      rw [getK_S_eq t, List.getD_cons_succ]
      rfl

private theorem lastK_cons : ∀ (x : ℕ) (t : List ℕ),
    lastK (x :: t) = (x :: t).getLast (List.cons_ne_nil x t)
  | _, [] => rfl
  | x, y :: t => by
    rw [List.getLast_cons_cons]
    exact lastK_cons y t

private theorem lastK_spec {B : List ℕ} (hB : B ≠ []) : B = B.dropLast ++ [lastK B] := by
  obtain ⟨x, t, e⟩ := List.exists_cons_of_ne_nil hB
  subst e
  rw [lastK_cons]
  exact (List.dropLast_append_getLast _).symm

private theorem le_lastK (g : ℕ → ℕ) {p B : List ℕ} (hB : B ≠ [])
    (h : ((p ++ B).map g).Pairwise (· < ·)) : ∀ a ∈ (p ++ B).map g, a ≤ g (lastK B) := by
  have e' : p ++ B = (p ++ B.dropLast) ++ [lastK B] := by
    rw [List.append_assoc, ← lastK_spec hB]
  rw [e', List.map_append, List.pairwise_append] at h
  intro a ha
  rw [e', List.map_append, List.mem_append] at ha
  rcases ha with ha | ha
  · exact (h.2.2 a ha _ (by simp)).le
  · rw [List.map_singleton, List.mem_singleton] at ha
    exact ha.le

private theorem pairwise_blocks (g : ℕ → ℕ) : ∀ (I : List (List ℕ)) (p : List ℕ),
    (p.map g).Pairwise (· < ·) →
    (∀ B I', I = B :: I' → B ≠ [] ∧ ((p ++ B).map g).Pairwise (· < ·)) →
    (∀ k, k + 1 < I.length → I.getD (k + 1) [] ≠ [] ∧
      ((lastK (I.getD k []) :: I.getD (k + 1) []).map g).Pairwise (· < ·)) →
    ((p ++ I.flatten).map g).Pairwise (· < ·)
  | [], p, hp, _, _ => by rw [List.flatten_nil, List.append_nil]; exact hp
  | B :: I, p, _, h0, hs => by
    obtain ⟨hB, hpB⟩ := h0 B I rfl
    have ih := pairwise_blocks g I [lastK B] (List.pairwise_singleton _ _)
      (fun B' I' e => by
        subst e
        have := hs 0 (by simp)
        rw [List.getD_cons_succ, List.getD_cons_zero, List.getD_cons_zero] at this
        exact this)
      (fun k hk => by
        have := hs (k + 1) (by simp only [List.length_cons]; omega)
        rw [List.getD_cons_succ, List.getD_cons_succ] at this
        exact this)
    rw [List.singleton_append, List.map_cons, List.pairwise_cons] at ih
    rw [List.flatten_cons, ← List.append_assoc, List.map_append, List.pairwise_append]
    exact ⟨hpB, ih.2, fun a ha b hb => lt_of_le_of_lt (le_lastK g hB hpB a ha) (ih.1 b hb)⟩

private noncomputable def prF (lv : Lvl) (d m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc => Bool.rec (motive := fun _ => ℕ) acc (CFSG.KC.LQT.S.getK lv.2.1 j)
      (CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.2.1 j) d)
        (CFSG.KC.Ord.notB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0)))) m

private theorem prF_spec (lv : Lvl) (d : ℕ) : ∀ m, (∃ j < m, CFSG.KC.LQT.S.getK lv.2.1 j ≠ 0 ∧
    CFSG.KC.LQT.S.getK lv.2.2.1 j = d) →
    ∃ j < m, CFSG.KC.LQT.S.getK lv.2.1 j ≠ 0 ∧ prF lv d m = CFSG.KC.LQT.S.getK lv.2.1 j
  | 0, ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)
  | m + 1, ⟨j, hj, hne, hd⟩ => by
    change ∃ j' < m + 1, CFSG.KC.LQT.S.getK lv.2.1 j' ≠ 0 ∧
      Bool.rec (motive := fun _ => ℕ) (prF lv d m) (CFSG.KC.LQT.S.getK lv.2.1 m)
        (CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.2.1 m) d)
          (CFSG.KC.Ord.notB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 m) 0))) =
        CFSG.KC.LQT.S.getK lv.2.1 j'
    cases hc : CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.2.1 m) d)
        (CFSG.KC.Ord.notB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 m) 0)) with
    | true =>
      rw [andB_true, notB_eq, Bool.not_eq_true'] at hc
      exact ⟨m, Nat.lt_succ_self m, Nat.ne_of_beq_eq_false hc.2, rfl⟩
    | false =>
      have hjm : j < m := by
        by_contra hjm
        have hjm' : j = m := by omega
        subst hjm'
        have hb1 : Nat.beq (CFSG.KC.LQT.S.getK lv.2.2.1 j) d = true := by
          rw [hd]
          exact Nat.beq_refl d
        have hb2 : Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0 = false := by
          cases h : Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) hne
        rw [hb1, hb2, notB_eq] at hc
        exact Bool.false_ne_true (hc.symm.trans (andB_true.2 ⟨rfl, rfl⟩))
      obtain ⟨j', hj', hne', e⟩ := prF_spec lv d m ⟨j, hjm, hne, hd⟩
      exact ⟨j', Nat.lt_succ_of_lt hj', hne', e⟩

private theorem getK_posReps (lv : Lvl) {d : ℕ} (hd : d < lv.2.2.2) :
    CFSG.KC.LQT.S.getK (posReps 24 lv) d = prF lv d 24 := by
  rw [getK_S_eq]
  unfold posReps
  rw [List.getD_eq_getElem _ _ (by simpa using hd), List.getElem_map, List.getElem_range]
  rfl

private theorem pos_of : ∀ (C : List Lvl) (prev : List ℕ),
    CFSG.KC.LQT.CM.okFrom 24 C prev = true → CFSG.KC.LQT.L.chainInj 24 C = true → ∀ lv ∈ C,
      (∀ i < lv.2.2.2, ∃ j < 24, CFSG.KC.LQT.S.getK lv.2.1 j ≠ 0 ∧
        CFSG.KC.LQT.S.getK lv.2.2.1 j = i) ∧ 0 < lv.2.2.2
  | [], _, _, _ => fun _ h => absurd h List.not_mem_nil
  | lv :: C, prev, h, hI => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB _ _)
      (CFSG.KC.LQT.CM.okFrom 24 C (lv.1 :: prev)) = true at h
    change CFSG.KC.Ord.andB _ (CFSG.KC.LQT.L.chainInj 24 C) = true at hI
    rw [andB_true, andB_true] at h
    rw [andB_true] at hI
    intro l hl
    rcases List.mem_cons.1 hl with e | hl
    · subst e
      exact (CFSG.KC.LQT.CM.lvP_of (prev := prev) h.1.1 h.1.2 hI.1).2.2
    · exact pos_of C _ h.2 hI.2 l hl

private theorem prodIdx_strip : ∀ {prev : List ℕ} {C : List Lvl},
    CFSG.KC.LQT.PHSnd.ChainW 24 prev C →
    (∀ lv ∈ C, (∀ i < lv.2.2.2, ∃ j < 24, CFSG.KC.LQT.S.getK lv.2.1 j ≠ 0 ∧
        CFSG.KC.LQT.S.getK lv.2.2.1 j = i) ∧ 0 < lv.2.2.2) → ∀ i : ℕ, ∃ σ : Perm (Fin 24),
      CFSG.KC.LQT.CM.InC 24 C σ ∧ prodIdx 24 C (C.map (posReps 24)) i = CFSG.KC.LQT.P.code σ
  | _, [], _, _, _ => ⟨1, by
      simp only [CFSG.KC.LQT.CM.InC, CFSG.KC.LQT.CM.sift]
      rw [CFSG.KC.LQT.P.code_one]
      simp, CFSG.KC.LQT.P.code_one⟩
  | _, lv :: C, h, hpos, i => by
    obtain ⟨hpos', hr⟩ := hpos lv List.mem_cons_self
    obtain ⟨j, hj, hne, e⟩ := prF_spec lv (i % lv.2.2.2) 24 (hpos' _ (Nat.mod_lt _ hr))
    obtain ⟨τ, hτ⟩ := (h.1.2 j hj hne).1
    obtain ⟨ρ, hρ, e'⟩ := prodIdx_strip h.2.2 (fun l hl => hpos l (List.mem_cons_of_mem _ hl))
      (i / lv.2.2.2)
    refine ⟨τ * ρ, CFSG.KC.LQT.PHSnd.inC_rep_mul_w (by norm_num) h hj hτ hne hρ, ?_⟩
    change CFSG.KC.LQT.P.mul 24 (CFSG.KC.LQT.S.getK (posReps 24 lv) (i % lv.2.2.2))
      (prodIdx 24 C (C.map (posReps 24)) (i / lv.2.2.2)) = _
    rw [getK_posReps lv (Nat.mod_lt _ hr), e, ← hτ, e', CFSG.KC.LQT.P.code_mul (by norm_num)]

theorem hk_data (C : List Lvl) (hC : chainOK 24 C = true)
    (hIn : CFSG.KC.LQT.L.chainInj 24 C = true) (I : List (List ℕ)) (K : ℕ)
    (hI : CFSG.KC.LQT.S.lenL I.flatten = chainF C) (hK : lenA I = K)
    (hb : ∀ k < K, hkDBlk 24 C (C.map (posReps 24)) I k = true) (x y : X24)
    (hx : inC 24 C (chainF C) (cX x) = true) (hy : inC 24 C (chainF C) (cX y) = true)
    (h : hkey x = hkey y) : x = y := by
  classical
  have hW := CFSG.KC.LQT.PHSnd.chainW_of_ok (n := 24) (by norm_num) hC
  have hpos := pos_of C [] (by rw [← CFSG.KC.LQT.CM.chainOK_eq]; exact hC) hIn
  have hlv := CFSG.KC.LQT.CM.chainP_lvOK (CFSG.KC.LQT.CM.chainP_of_ok hC hIn)
  set g : ℕ → ℕ := fun i => hkK (prodIdx 24 C (C.map (posReps 24)) i) with hg
  have hKl : K = I.length := by rw [← hK, CFSG.KC.LQT.LK.lenA_eq]
  have hpw : (I.flatten.map g).Pairwise (· < ·) := by
    have := pairwise_blocks g I [] List.Pairwise.nil ?_ ?_
    · rwa [List.nil_append] at this
    · intro B I' e
      subst e
      have h' : CFSG.KC.Ord.andB (Nat.blt 0 (CFSG.KC.LQT.S.lenL B))
          (CFSG.KC.LQT.T2.sincK (List.map g (List.append [] B))) = true :=
        hb 0 (by rw [hKl]; simp)
      rw [andB_true, lenL_eq] at h'
      refine ⟨fun e => ?_, sincA_pairwise _ none h'.2⟩
      rw [e] at h'
      exact absurd h'.1 (by decide)
    · intro k hk
      have h' : CFSG.KC.Ord.andB
          (Nat.blt 0 (CFSG.KC.LQT.S.lenL (CFSG.KC.LQT.Syl.getK I (k + 1) [])))
          (CFSG.KC.LQT.T2.sincK (List.map g (List.append [lastK (CFSG.KC.LQT.Syl.getK I k [])]
            (CFSG.KC.LQT.Syl.getK I (k + 1) [])))) = true :=
        hb (k + 1) (by rw [hKl]; exact hk)
      rw [andB_true, lenL_eq, getK_Syl_eq, getK_Syl_eq] at h'
      refine ⟨fun e => ?_, sincA_pairwise _ none h'.2⟩
      rw [e] at h'
      exact absurd h'.1 (by decide)
  set D := I.flatten.map (prodIdx 24 C (C.map (posReps 24))) with hD
  have hDk : (D.map hkK).Pairwise (· < ·) := by
    rw [hD, List.map_map]
    exact hpw
  have hDnd : D.Nodup := List.Nodup.of_map hkK (hDk.imp ne_of_lt)
  have hDlen : D.length = chainF C := by
    rw [hD, List.length_map, ← lenL_eq]
    exact hI
  have hDs : ∀ c ∈ D, ∃ σ : Perm (Fin 24), CFSG.KC.LQT.CM.InC 24 C σ ∧
      c = CFSG.KC.LQT.P.code σ := by
    intro c hc
    rw [hD, List.mem_map] at hc
    obtain ⟨i, -, e⟩ := hc
    obtain ⟨σ, hσ, e'⟩ := prodIdx_strip hW hpos i
    exact ⟨σ, hσ, e.symm.trans e'⟩
  have hall : ∀ σ : Perm (Fin 24), CFSG.KC.LQT.CM.InC 24 C σ → CFSG.KC.LQT.P.code σ ∈ D := by
    have hinj : Function.Injective (CFSG.KC.LQT.P.code : Perm (Fin 24) → ℕ) :=
      fun a b e => CFSG.KC.LQT.P.code_inj (by norm_num) e
    have hT : (Finset.univ.filter fun σ : Perm (Fin 24) => CFSG.KC.LQT.CM.InC 24 C σ).card =
        chainF C := by
      rw [← CFSG.KC.LQT.CM.card_inC (by norm_num) hC hIn, Nat.card_eq_fintype_card,
        Fintype.card_subtype]
    have hsub : D.toFinset ⊆ (Finset.univ.filter fun σ : Perm (Fin 24) =>
        CFSG.KC.LQT.CM.InC 24 C σ).image CFSG.KC.LQT.P.code := by
      intro c hc
      obtain ⟨σ, hσ, e⟩ := hDs c (List.mem_toFinset.1 hc)
      rw [e]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩)
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq (by
      rw [Finset.card_image_of_injective _ hinj, hT, List.toFinset_card_of_nodup hDnd, hDlen]))
    intro σ hσ
    have h1 : CFSG.KC.LQT.P.code σ ∈ (Finset.univ.filter fun σ : Perm (Fin 24) =>
        CFSG.KC.LQT.CM.InC 24 C σ).image CFSG.KC.LQT.P.code :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩)
    rw [← heq] at h1
    exact List.mem_toFinset.1 h1
  have hx' := hall x.1 ((CFSG.KC.LQT.CM.inC_iff (by norm_num) hlv x.1).1 hx)
  have hy' := hall y.1 ((CFSG.KC.LQT.CM.inC_iff (by norm_num) hlv y.1).1 hy)
  exact cX_injective (List.inj_on_of_nodup_map (hDk.imp ne_of_lt) hx' hy'
    ((hkey_code x).symm.trans (h.trans (hkey_code y))))

theorem chain_allC (C : List Lvl) (hC : chainOK 24 C = true) (f : ℕ → Bool)
    (h : allChain 24 C f = true) (x : X24) (hx : inC 24 C (chainF C) (cX x) = true) :
    f (cX x) = true := by
  have hW := CFSG.KC.LQT.CM.lvW_of_chainOK (by norm_num) hC
  exact CFSG.KC.LQT.CM.allChain_sound_w (by norm_num) hW f h x.1
    ((CFSG.KC.LQT.CM.inC_iff_w (by norm_num) hW x.1).1 hx)

theorem chain_all (C : List Lvl) (hC : chainOK 24 C = true) (f : ℕ → Bool)
    (h : ∀ j < 24, chainChunk 24 C f j = true) (x : X24)
    (hx : inC 24 C (chainF C) (cX x) = true) : f (cX x) = true :=
  chain_allC C hC f (CFSG.KC.LQT.CM.allChain_of_chunks (by norm_num) h) x hx

private theorem mem_prodsK_w : ∀ {prev : List ℕ} {C : List Lvl},
    CFSG.KC.LQT.PHSnd.ChainW 24 prev C → ∀ (π : Perm (Fin 24)) (c : ℕ),
      c ∈ prodsK 24 C (CFSG.KC.LQT.P.code π) →
        ∃ σ, CFSG.KC.LQT.CM.InC 24 C σ ∧ c = CFSG.KC.LQT.P.code (π * σ)
  | _, [], _, π, c, hc => by
    rw [prodsK, List.mem_singleton] at hc
    refine ⟨1, ?_, by rw [hc, mul_one]⟩
    simp only [CFSG.KC.LQT.CM.InC, CFSG.KC.LQT.CM.sift]
    rw [CFSG.KC.LQT.P.code_one]
    simp
  | _, lv :: C, h, π, c, hc => by
    rw [prodsK, List.mem_flatMap] at hc
    obtain ⟨j, hj, hc⟩ := hc
    simp only [List.mem_filter, List.mem_range, bne_iff_ne] at hj
    obtain ⟨⟨τ, hτ⟩, -⟩ := h.1.2 j hj.1 hj.2
    rw [← hτ, CFSG.KC.LQT.P.code_mul (by norm_num)] at hc
    obtain ⟨ρ, hρ, e⟩ := mem_prodsK_w h.2.2 (π * τ) c hc
    refine ⟨τ * ρ, CFSG.KC.LQT.PHSnd.inC_rep_mul_w (by norm_num) h hj.1 hτ hj.2 hρ, ?_⟩
    rw [e, mul_assoc]

private theorem code_mem_prodsK_w : ∀ {prev : List ℕ} {C : List Lvl},
    CFSG.KC.LQT.PHSnd.ChainW 24 prev C → ∀ (π σ : Perm (Fin 24)),
      CFSG.KC.LQT.CM.InC 24 C σ →
        CFSG.KC.LQT.P.code (π * σ) ∈ prodsK 24 C (CFSG.KC.LQT.P.code π)
  | _, [], _, π, σ, hσ => by
    simp only [CFSG.KC.LQT.CM.InC, CFSG.KC.LQT.CM.sift] at hσ
    split_ifs at hσ with e
    · rw [CFSG.KC.LQT.P.code_one] at e
      rw [CFSG.KC.LQT.P.code_inj (by norm_num) e, mul_one]
      exact List.mem_singleton_self _
    · exact absurd hσ (by simp)
  | _, lv :: C, h, π, σ, hσ => by
    obtain ⟨j, hj, τ, hτ, e, h', -⟩ := CFSG.KC.LQT.PHSnd.inC_cons_w (by norm_num) h hσ
    have ih := code_mem_prodsK_w h.2.2 (π * τ) (τ⁻¹ * σ) h'
    rw [mul_assoc, mul_inv_cancel_left, ← CFSG.KC.LQT.P.code_mul (by norm_num), hτ] at ih
    rw [prodsK, List.mem_flatMap]
    refine ⟨j, List.mem_filter.2 ⟨List.mem_range.2 hj, ?_⟩, ih⟩
    rw [bne_iff_ne]
    exact e

private theorem img_base_w {prev : List ℕ} {lv : Lvl} {C : List Lvl}
    (h : CFSG.KC.LQT.PHSnd.ChainW 24 prev (lv :: C)) {j : ℕ} (hj : j < 24) {τ : Perm (Fin 24)}
    (hτ : CFSG.KC.LQT.P.code τ = CFSG.KC.LQT.S.getK lv.2.1 j)
    (hne : CFSG.KC.LQT.S.getK lv.2.1 j ≠ 0) {ρ : Perm (Fin 24)}
    (hρ : CFSG.KC.LQT.CM.InC 24 C ρ) :
    CFSG.KC.LQT.P.img (CFSG.KC.LQT.P.code (τ * ρ)) lv.1 = j := by
  have hb := (h.2.1 j hj hne).2
  rw [← hτ] at hb
  by_cases hbn : lv.1 < 24
  · have hfix := CFSG.KC.LQT.PHSnd.fix_of_inC_w (by norm_num) h.2.2 hρ lv.1 List.mem_cons_self hbn
    rw [CFSG.KC.LQT.CM.img_code_fix (by norm_num) τ hbn] at hb
    rw [CFSG.KC.LQT.CM.img_code_fix (by norm_num) (τ * ρ) hbn, Perm.mul_apply, hfix]
    exact hb
  · rw [CFSG.KC.LQT.CM.img_ge (by norm_num) (CFSG.KC.LQT.CM.fc_code (by norm_num) τ)
      (not_lt.1 hbn)] at hb
    rw [CFSG.KC.LQT.CM.img_ge (by norm_num) (CFSG.KC.LQT.CM.fc_code (by norm_num) (τ * ρ))
      (not_lt.1 hbn)]
    exact hb

private theorem prodsK_nodup_w : ∀ {prev : List ℕ} {C : List Lvl},
    CFSG.KC.LQT.PHSnd.ChainW 24 prev C → ∀ π : Perm (Fin 24),
      (prodsK 24 C (CFSG.KC.LQT.P.code π)).Nodup
  | _, [], _, π => List.nodup_singleton _
  | _, lv :: C, h, π => by
    have hrep : ∀ j ∈ (List.range 24).filter fun j => CFSG.KC.LQT.S.getK lv.2.1 j != 0,
        j < 24 ∧ CFSG.KC.LQT.S.getK lv.2.1 j ≠ 0 ∧ ∃ τ : Perm (Fin 24),
          CFSG.KC.LQT.P.code τ = CFSG.KC.LQT.S.getK lv.2.1 j := by
      intro j hj
      simp only [List.mem_filter, List.mem_range, bne_iff_ne] at hj
      exact ⟨hj.1, hj.2, (h.1.2 j hj.1 hj.2).1⟩
    rw [prodsK, List.nodup_flatMap]
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain ⟨-, -, τ, hτ⟩ := hrep j hj
      rw [← hτ, CFSG.KC.LQT.P.code_mul (by norm_num)]
      exact prodsK_nodup_w h.2.2 (π * τ)
    · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range.filter _)
      intro j j' hj hj' hne c hc hc'
      dsimp only at hc hc'
      obtain ⟨hj1, hj2, τ, hτ⟩ := hrep j hj
      obtain ⟨hj1', hj2', τ', hτ'⟩ := hrep j' hj'
      rw [← hτ, CFSG.KC.LQT.P.code_mul (by norm_num)] at hc
      rw [← hτ', CFSG.KC.LQT.P.code_mul (by norm_num)] at hc'
      obtain ⟨ρ, hρ, e1⟩ := mem_prodsK_w h.2.2 (π * τ) c hc
      obtain ⟨ρ', hρ', e2⟩ := mem_prodsK_w h.2.2 (π * τ') c hc'
      have e' : τ * ρ = τ' * ρ' := by
        have := CFSG.KC.LQT.P.code_inj (by norm_num) (e1.symm.trans e2)
        rw [mul_assoc, mul_assoc] at this
        exact mul_left_cancel this
      apply hne
      rw [← img_base_w h hj1 hτ hj2 hρ, ← img_base_w h hj1' hτ' hj2' hρ', e']

private theorem prodsK_perm (C : List Lvl) (hC : chainOK 24 C = true) (L : List X24)
    (hnd : L.Nodup) (hL : ∀ x, x ∈ L ↔ inC 24 C (chainF C) (cX x) = true)
    (hs : ∀ σ : Perm (Fin 24), inC 24 C (chainF C) (codeP σ) = true → ∃ x ∈ L, cX x = codeP σ) :
    (L.map cX).Perm (prodsK 24 C (CFSG.KC.LQT.P.one 24)) := by
  have hW := CFSG.KC.LQT.PHSnd.chainW_of_ok (n := 24) (by norm_num) hC
  have hlv := CFSG.KC.LQT.CM.lvW_of_chainOK (n := 24) (by norm_num) hC
  rw [CFSG.KC.LQT.P.code_one]
  refine (List.perm_ext_iff_of_nodup (hnd.map cX_injective) (prodsK_nodup_w hW 1)).2 fun c => ?_
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := code_mem_prodsK_w hW 1 x.1
      ((CFSG.KC.LQT.CM.inC_iff_w (by norm_num) hlv x.1).1 ((hL x).1 hx))
    rw [one_mul] at this
    exact this
  · intro hc
    obtain ⟨σ, hσ, e⟩ := mem_prodsK_w hW 1 c hc
    rw [e, one_mul]
    exact hs σ ((CFSG.KC.LQT.CM.inC_iff_w (by norm_num) hlv σ).2 hσ)

private noncomputable def cntS (n : ℕ) (C : List Lvl) (f : ℕ → Bool) (lv : Lvl) (p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (CFSG.KC.LQT.Syl.letN (CFSG.KC.LQT.P.mul n p (CFSG.KC.LQT.S.getK lv.2.1 j)) (cntFrom n C f)) 0
    (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0)

private noncomputable def cntLv (n : ℕ) (C : List Lvl) (f : ℕ → Bool) (lv : Lvl) (p : ℕ) (m : ℕ) :
    ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.add acc (cntS n C f lv p j)) m

private theorem cntLv_succ (n : ℕ) (C : List Lvl) (f : ℕ → Bool) (lv : Lvl) (p m : ℕ) :
    cntLv n C f lv p (m + 1) = cntLv n C f lv p m + cntS n C f lv p m := rfl

private theorem cntLv_eq (n : ℕ) (C : List Lvl) (f : ℕ → Bool) (lv : Lvl) (p : ℕ) :
    ∀ m, cntLv n C f lv p m = ((List.range m).map (cntS n C f lv p)).sum
  | 0 => rfl
  | m + 1 => by
    rw [cntLv_succ, cntLv_eq n C f lv p m, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]

private theorem cntFrom_eq (n : ℕ) (f : ℕ → Bool) : ∀ (C : List Lvl) (p : ℕ),
    cntFrom n C f p = ((prodsK n C p).filter f).length
  | [], p => by
    rw [prodsK, List.filter_singleton]
    change Bool.rec (motive := fun _ => ℕ) 0 1 (f p) = _
    cases f p <;> rfl
  | lv :: C, p => by
    have step : ∀ m, cntLv n C f lv p m = ((((List.range m).filter fun j =>
        CFSG.KC.LQT.S.getK lv.2.1 j != 0).flatMap fun j =>
          prodsK n C (CFSG.KC.LQT.P.mul n p (CFSG.KC.LQT.S.getK lv.2.1 j))).filter f).length := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [cntLv_succ, ih, List.range_succ, List.filter_append, List.flatMap_append,
          List.filter_append, List.length_append]
        congr 1
        cases hb : Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 m) 0
        · have hne : (CFSG.KC.LQT.S.getK lv.2.1 m != 0) = true := by
            rw [bne_iff_ne]
            exact Nat.ne_of_beq_eq_false hb
          have e1 : cntS n C f lv p m =
              cntFrom n C f (CFSG.KC.LQT.P.mul n p (CFSG.KC.LQT.S.getK lv.2.1 m)) := by
            unfold cntS
            rw [hb]
            exact letN_eq _ _
          rw [e1, cntFrom_eq n f C]
          simp only [List.filter_singleton, hne, cond_true, List.flatMap_singleton]
        · have heq : (CFSG.KC.LQT.S.getK lv.2.1 m != 0) = false := by
            rw [bne_eq_false_iff_eq]
            exact Nat.eq_of_beq_eq_true hb
          have e1 : cntS n C f lv p m = 0 := by
            unfold cntS
            rw [hb]
          rw [e1]
          simp only [List.filter_singleton, heq, cond_false, List.flatMap_nil, List.filter_nil,
            List.length_nil]
    change cntLv n C f lv p n = _
    rw [prodsK]
    exact step n

private theorem sum_cntChunk {n : ℕ} (hn : 0 < n) (C : List Lvl) (f : ℕ → Bool) :
    ((List.range n).map (cntChunk n C f)).sum = cntFrom n C f (CFSG.KC.LQT.P.one n) := by
  cases C with
  | nil =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have key : ∀ m, ((List.range (m + 1)).map (cntChunk (k + 1) [] f)).sum =
        cntFrom (k + 1) [] f (CFSG.KC.LQT.P.one (k + 1)) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih]
        rfl
    exact key k
  | cons lv C =>
    change ((List.range n).map (cntS n C f lv (CFSG.KC.LQT.P.one n))).sum =
      cntLv n C f lv (CFSG.KC.LQT.P.one n) n
    rw [cntLv_eq]

theorem chain_cnt (C : List Lvl) (hC : chainOK 24 C = true) (L : List X24) (hnd : L.Nodup)
    (hL : ∀ x, x ∈ L ↔ inC 24 C (chainF C) (cX x) = true)
    (hs : ∀ σ : Perm (Fin 24), inC 24 C (chainF C) (codeP σ) = true → ∃ x ∈ L, cX x = codeP σ)
    (p : X24 → Bool) (pk : ℕ → Bool)
    (hp : ∀ x, p x = pk (cX x)) (cs : List ℕ) (hcs : cs.length = 24)
    (hc : ∀ j < 24, cntChunk 24 C pk j = cs.getD j 0) : (L.filter p).length = cs.sum := by
  have hp' : p = pk ∘ cX := funext hp
  subst hp'
  have e1 : cs = (List.range 24).map (cntChunk 24 C pk) := by
    refine List.ext_getElem (by rw [hcs, List.length_map, List.length_range]) fun j h1 h2 => ?_
    rw [List.getElem_map, List.getElem_range, hc j (hcs ▸ h1), List.getD_eq_getElem _ _ h1]
  rw [e1, sum_cntChunk (by norm_num), cntFrom_eq,
    ← ((prodsK_perm C hC L hnd hL hs).filter pk).length_eq, List.filter_map, List.length_map]

theorem chain_col (C : List Lvl) (hC : chainOK 24 C = true) (L : List X24) (hnd : L.Nodup)
    (hL : ∀ x, x ∈ L ↔ inC 24 C (chainF C) (cX x) = true)
    (hs : ∀ σ : Perm (Fin 24), inC 24 C (chainF C) (codeP σ) = true → ∃ x ∈ L, cX x = codeP σ)
    (p : X24 → Bool) (pk : ℕ → Bool)
    (hp : ∀ x, p x = pk (cX x)) :
    ((L.filter p).map cX).Perm (colAll 24 C (fun c => c) pk) := by
  have h1 := colFrom_perm 24 (fun c => c) pk C (CFSG.KC.LQT.P.one 24) []
  rw [List.append_nil, List.map_id'] at h1
  have hp' : p = pk ∘ cX := funext hp
  subst hp'
  rw [← List.filter_map]
  exact ((prodsK_perm C hC L hnd hL hs).filter pk).trans h1.symm

section Reach

variable {Γ : Type*} [Group Γ] {Ω : Type*} [MulAction Γ Ω] {E : Type*} [BEq E] [Hashable E]

def BfsInv (gens : List Γ) (x₀ : Ω) (st : BfsState Ω E) : Prop :=
  st.par.size = st.O.size ∧ st.lab.size = st.O.size ∧ 0 < st.O.size ∧
    st.O.toList.getD 0 x₀ = x₀ ∧ ∀ k < st.O.size, 0 < k → st.par.toList.getD k 0 < k ∧
      st.O.toList.getD k x₀ = gens.getD (st.lab.toList.getD k 0) 1 • st.O.toList.getD
        (st.par.toList.getD k 0) x₀

theorem getD_push {α : Type*} (a : Array α) (y d : α) (k : ℕ) (hk : k < a.size) :
    (a.push y).toList.getD k d = a.toList.getD k d := by
  rw [Array.toList_push, List.getD_append _ _ _ _ (by simpa using hk)]

theorem getD_push_size {α : Type*} (a : Array α) (y d : α) :
    (a.push y).toList.getD a.size d = y := by
  rw [Array.toList_push, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem bfs_step_inv (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ x : Ω) (i j : ℕ) (st : BfsState Ω E) (hI : BfsInv gens x₀ st) (hi : i < st.O.size)
    (hx : st.O.toList.getD i x₀ = x) :
    let st' := if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
      else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
        st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩
    BfsInv gens x₀ st' ∧ i < st'.O.size ∧ st'.O.toList.getD i x₀ = x := by
  intro st'
  by_cases hc : st.seen.contains (enc (nrm (gens.getD j 1 • x))) = true
  · simp only [st', hc, ite_true]
    exact ⟨hI, hi, hx⟩
  · simp only [st', hc, Bool.false_eq_true, ite_false]
    obtain ⟨hp, hl, h0, hz, hk⟩ := hI
    refine ⟨⟨?_, ?_, ?_, ?_, fun k hk1 hk0 => ?_⟩, ?_, ?_⟩ <;> try dsimp only
    · rw [Array.size_push, Array.size_push, hp]
    · rw [Array.size_push, Array.size_push, hl]
    · rw [Array.size_push]
      omega
    · rw [getD_push _ _ _ _ h0, hz]
    rotate_left
    · rw [Array.size_push]
      omega
    · rw [getD_push _ _ _ _ hi, hx]
    rw [Array.size_push] at hk1
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk1 with hk1 | rfl
    · have hpk := hk k hk1 hk0
      rw [getD_push _ _ _ _ (hp ▸ hk1), getD_push _ _ _ _ hk1, getD_push _ _ _ _ (hl ▸ hk1),
        getD_push _ _ _ _ (by omega)]
      exact hpk
    · rw [← hp, getD_push_size, hp, getD_push_size, ← hl, getD_push_size, hl,
        getD_push _ _ _ _ hi, hx, hnrm]
      exact ⟨hi, rfl⟩

theorem bfs_fold_inv (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ x : Ω) (i : ℕ) : ∀ (js : List ℕ) (st : BfsState Ω E), BfsInv gens x₀ st →
      i < st.O.size → st.O.toList.getD i x₀ = x →
      BfsInv gens x₀ (js.foldl (fun (st : BfsState Ω E) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st)
  | [], _, hI, _, _ => hI
  | j :: js, st, hI, hi, hx => by
    obtain ⟨h1, h2, h3⟩ := bfs_step_inv nrm hnrm enc gens x₀ x i j st hI hi hx
    exact bfs_fold_inv nrm hnrm enc gens x₀ x i js _ h1 h2 h3

theorem bfs_loop_inv (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ : Ω) : ∀ (f i : ℕ) (st : BfsState Ω E), BfsInv gens x₀ st →
      BfsInv gens x₀ (bfsLoop nrm enc gens f i st)
  | 0, _, _, h => h
  | f + 1, i, st, h => by
    rw [bfsLoop]
    split_ifs with hi
    · refine bfs_loop_inv nrm hnrm enc gens x₀ f (i + 1) _
        (bfs_fold_inv nrm hnrm enc gens x₀ _ i (List.range gens.length) st h hi ?_)
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    · exact h

theorem reach_bfsOrbit (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → E) (gens : List Γ)
    (x₀ : Ω) (fuel : ℕ) :
    Reach gens x₀ (bfsOrbit nrm enc gens x₀ fuel).1 (bfsOrbit nrm enc gens x₀ fuel).2.1
      (bfsOrbit nrm enc gens x₀ fuel).2.2 := by
  have h0 : BfsInv gens x₀
      (⟨#[x₀], #[0], #[0], (∅ : Std.HashSet E).insert (enc x₀)⟩ : BfsState Ω E) :=
    ⟨rfl, rfl, by simp, rfl, fun k hk hk0 => by simp at hk; omega⟩
  obtain ⟨-, -, hpos, hz, hk⟩ := bfs_loop_inv nrm hnrm enc gens x₀ fuel 0 _ h0
  refine ⟨?_, hz, fun k hk1 hk0 => hk k ?_ hk0⟩
  · simpa [bfsOrbit] using hpos
  · simpa [bfsOrbit] using hk1

end Reach

@[expose] def packL (l : List ℕ) : ℕ := l.foldl (fun acc m => acc * 2 ^ 24 + m) 0

theorem packK_eq (l : List ℕ) : packK l = packL l := by
  have key : ∀ (l : List ℕ) (acc : ℕ), List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun m _ ih acc => CFSG.KC.LQT.Syl.letN (Nat.add (Nat.mul acc 16777216) m) ih) l acc =
      l.foldl (fun acc m => acc * 2 ^ 24 + m) acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons m l ih =>
      intro acc
      refine (letN_eq _ _).trans ?_
      exact ih _
  exact key l 0

theorem encTrioN_eq (τ : Finset (Finset (Fin 24))) : encTrioN τ = packL (encTrio τ) := rfl

@[expose] def unpR (k : ℕ) : ℕ × List ℕ → ℕ × List ℕ :=
  Nat.rec (motive := fun _ => ℕ × List ℕ → ℕ × List ℕ) (fun st => st)
    (fun _ ih st => Bool.rec (motive := fun _ => ℕ × List ℕ)
      (ih (Nat.shiftRight st.1 24, List.cons (Nat.land st.1 16777215) st.2)) st
      (Nat.beq st.1 0)) k

theorem unpackK_eq (t : ℕ) : unpackK t = (unpR 24 (t, [])).2 := rfl

theorem unpR_succ (k : ℕ) (st : ℕ × List ℕ) : unpR (k + 1) st =
    Bool.rec (motive := fun _ => ℕ × List ℕ)
      (unpR k (Nat.shiftRight st.1 24, List.cons (Nat.land st.1 16777215) st.2)) st
      (Nat.beq st.1 0) := rfl

theorem unpR_zero (k : ℕ) (acc : List ℕ) : unpR k (0, acc) = (0, acc) := by
  cases k with
  | zero => rfl
  | succ k => rw [unpR_succ]; rfl

theorem unpR_stepN (k N P b : ℕ) (acc : List ℕ) (h0 : Nat.beq N 0 = false)
    (h1 : Nat.shiftRight N 24 = P) (h2 : Nat.land N 16777215 = b) :
    unpR (k + 1) (N, acc) = unpR k (P, b :: acc) := by
  rw [unpR_succ, h0]
  subst h1 h2
  rfl

theorem unpR_step (k P b : ℕ) (acc : List ℕ) (hb : 0 < b ∧ b < 2 ^ 24) :
    unpR (k + 1) (P * 2 ^ 24 + b, acc) = unpR k (P, b :: acc) := by
  have hpos : 0 < P * 2 ^ 24 + b := Nat.lt_of_lt_of_le hb.1 (Nat.le_add_left b _)
  have h0 : Nat.beq (P * 2 ^ 24 + b) 0 = false := by
    generalize P * 2 ^ 24 + b = N at hpos
    cases hc : Nat.beq N 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hc) (Nat.ne_of_gt hpos)
  refine unpR_stepN k _ P b acc h0 ?_ ?_
  · have h : (P * 2 ^ 24 + b) >>> 24 = P := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hb.2, Nat.zero_add]
    exact h
  · have h : (P * 2 ^ 24 + b) &&& (2 ^ 24 - 1) = b := by
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_comm, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hb.2]
    exact h

theorem unpR_pack (k : ℕ) : ∀ (D : List ℕ), D.length ≤ k → (∀ d ∈ D, 0 < d ∧ d < 2 ^ 24) →
    ∀ acc, unpR k (packL D, acc) = (0, D ++ acc) := by
  induction k with
  | zero =>
    intro D hl _ acc
    have : D = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ k ih =>
    intro D hl hD acc
    rcases List.eq_nil_or_concat D with rfl | ⟨L, b, rfl⟩
    · exact unpR_zero _ acc
    · have hb := hD b (by simp)
      have hL : ∀ d ∈ L, 0 < d ∧ d < 2 ^ 24 := fun d hd => hD d (by simp [hd])
      have hp : packL (L.concat b) = packL L * 2 ^ 24 + b := by
        rw [packL, List.concat_eq_append, List.foldl_append, ← packL]
        rfl
      rw [hp, unpR_step k _ b acc hb, ih L (by simp at hl; omega) hL (b :: acc)]
      simp

theorem unpack_pack {D : List ℕ} (hl : D.length ≤ 24) (hD : ∀ d ∈ D, 0 < d ∧ d < 2 ^ 24) :
    unpackK (packL D) = D := by
  rw [unpackK_eq, unpR_pack 24 D hl hD []]
  simp

theorem maskF_eq' (B : Finset (Fin 24)) : maskF B = ∑ i ∈ B, 2 ^ (i : ℕ) := rfl

theorem maskF_inj {B C : Finset (Fin 24)} (h : maskF B = maskF C) : B = C :=
  CFSG.KC.LQT.PW.sum_two_pow_inj h

theorem maskF_bound {B : Finset (Fin 24)} (h : B.Nonempty) : 0 < maskF B ∧ maskF B < 2 ^ 24 :=
  ⟨CFSG.KC.LQT.PW.sum_two_pow_pos h, CFSG.KC.LQT.PW.sum_two_pow_lt B⟩

theorem mem_encTrio {τ : Finset (Finset (Fin 24))} {m : ℕ} :
    m ∈ encTrio τ ↔ ∃ B ∈ τ, maskF B = m := by
  rw [encTrio, Finset.mem_sort, Finset.mem_image]

theorem encTrio_bound {τ : Finset (Finset (Fin 24))} (hne : ∅ ∉ τ) :
    ∀ d ∈ encTrio τ, 0 < d ∧ d < 2 ^ 24 := by
  intro d hd
  obtain ⟨B, hB, rfl⟩ := mem_encTrio.1 hd
  exact maskF_bound (Finset.nonempty_iff_ne_empty.2 fun e => hne (e ▸ hB))

theorem encTrio_length (τ : Finset (Finset (Fin 24))) : (encTrio τ).length = τ.card := by
  rw [encTrio, Finset.length_sort, Finset.card_image_of_injective _ fun _ _ h => maskF_inj h]

theorem dedupA_spec : ∀ (l : List ℕ) (o : Option ℕ),
    (∀ y ∈ List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
      (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
        (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x))) (ih (some x))
          (Nat.beq x y)) o) l o, y ∈ l) ∧
    (List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
      (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
        (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x))) (ih (some x))
          (Nat.beq x y)) o) l o).length ≤ l.length ∧
    (∀ y ∈ l, y ∈ List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
      (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
        (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x))) (ih (some x))
          (Nat.beq x y)) o) l o ∨ some y = o)
  | [], _ => ⟨fun _ h => absurd h List.not_mem_nil, le_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: t, o => by
    obtain ⟨h1, h2, h3⟩ := dedupA_spec t (some x)
    have keep : ∀ r, r = x :: List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
        (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
          (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x))) (ih (some x))
            (Nat.beq x y)) o) t (some x) →
        (∀ y ∈ r, y ∈ x :: t) ∧ r.length ≤ (x :: t).length ∧ (∀ y ∈ x :: t, y ∈ r ∨ some y = o) := by
      rintro r rfl
      refine ⟨fun y hy => ?_, by simp; omega, fun y hy => ?_⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h1 y hy)
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl List.mem_cons_self
        · rcases h3 y hy with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inl (by rw [Option.some.inj h]; exact List.mem_cons_self)
    cases o with
    | none => exact keep _ rfl
    | some p =>
      cases hxp : Nat.beq x p
      · exact keep _ (by simp only [hxp])
      · have hx : x = p := Nat.eq_of_beq_eq_true hxp
        have e : List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
            (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
              (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
                (ih (some x)) (Nat.beq x y)) o) (x :: t) (some p) =
            List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
            (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
              (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
                (ih (some x)) (Nat.beq x y)) o) t (some x) := by
          change Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq x p) = _
          rw [hxp]
        rw [e]
        refine ⟨fun y hy => List.mem_cons_of_mem _ (h1 y hy), by simp; omega, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inr (by rw [hx])
        · rcases h3 y hy with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [← hx]; exact h)

theorem mem_dedupS {l : List ℕ} {y : ℕ} : y ∈ CFSG.KC.LQT.Syl.dedupS l ↔ y ∈ l := by
  obtain ⟨h1, -, h3⟩ := dedupA_spec l none
  exact ⟨h1 y, fun hy => (h3 y hy).resolve_right (by simp)⟩

theorem length_dedupS (l : List ℕ) : (CFSG.KC.LQT.Syl.dedupS l).length ≤ l.length :=
  (dedupA_spec l none).2.1

theorem mem_dedupS_sortN {l : List ℕ} {y : ℕ} :
    y ∈ CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN l) ↔ y ∈ l := by
  rw [mem_dedupS, (sortN_perm l).mem_iff]

theorem imgMask_eq (n g m : ℕ) :
    imgMask n g m = CFSG.KC.LQT.PW.orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1
      (m.testBit i)) (CFSG.KC.LQT.P.img g) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : imgMask (n + 1) g m = Bool.rec (motive := fun _ => ℕ) (imgMask n g m)
        (Nat.lor (imgMask n g m) (Nat.shiftLeft 1 (CFSG.KC.LQT.P.img g n)))
        (Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1) := rfl
    have e2 : CFSG.KC.LQT.PW.orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1 (m.testBit i))
        (CFSG.KC.LQT.P.img g) (n + 1) = Nat.lor (CFSG.KC.LQT.PW.orW 1
          (fun i => Bool.rec (motive := fun _ => ℕ) 0 1 (m.testBit i)) (CFSG.KC.LQT.P.img g) n)
          (Nat.shiftLeft (Bool.rec (motive := fun _ => ℕ) 0 1 (m.testBit n))
          (Nat.mul 1 (CFSG.KC.LQT.P.img g n))) := rfl
    rw [e1, e2, ← ih, CFSG.KC.LQT.PW.bit_eq]
    cases m.testBit n
    · change imgMask n g m = imgMask n g m ||| (0 <<< (1 * CFSG.KC.LQT.P.img g n))
      rw [Nat.zero_shiftLeft, Nat.or_zero]
    · change imgMask n g m ||| (1 <<< CFSG.KC.LQT.P.img g n) =
        imgMask n g m ||| (1 <<< (1 * CFSG.KC.LQT.P.img g n))
      rw [Nat.one_mul]

theorem img_cX (x : X24) (i : Fin 24) : CFSG.KC.LQT.P.img (cX x) i = ((x : Perm (Fin 24)) i : ℕ) :=
  CFSG.KC.LQT.P.img_code (by norm_num) x.1 i

theorem pAI24 (σ : Perm (Fin 24)) (k : Fin 24) : σ (σ⁻¹ k) = k := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

theorem pIA24 (σ : Perm (Fin 24)) (k : Fin 24) : σ⁻¹ (σ k) = k := by
  rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]

theorem mem_smul_iff (x : X24) (B : Finset (Fin 24)) (k : Fin 24) :
    k ∈ x • B ↔ (x : Perm (Fin 24))⁻¹ k ∈ B := by
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have e : (x : Perm (Fin 24))⁻¹ (x • j) = j := pIA24 _ j
    rwa [e]
  · intro hk
    exact ⟨_, hk, pAI24 _ k⟩

theorem imgMask_maskF (x : X24) (B : Finset (Fin 24)) :
    imgMask 24 (cX x) (maskF B) = maskF (x • B) := by
  have hp : ∀ i < 24, ∀ j < 24, CFSG.KC.LQT.P.img (cX x) i = CFSG.KC.LQT.P.img (cX x) j →
      i = j := by
    intro i hi j hj e
    rw [img_cX x ⟨i, hi⟩, img_cX x ⟨j, hj⟩] at e
    exact congrArg Fin.val ((x : Perm (Fin 24)).injective (Fin.ext e))
  apply CFSG.KC.LQT.PW.eq_of_imgW (w := 1) (by norm_num)
  intro k
  rw [imgMask_eq, maskF_eq' (x • B), CFSG.KC.LQT.PW.imgW_sum_two_pow]
  by_cases hk : k < 24
  · set i : Fin 24 := (x : Perm (Fin 24))⁻¹ ⟨k, hk⟩ with hi
    have hpk : CFSG.KC.LQT.P.img (cX x) i = k := by rw [img_cX, hi, pAI24]
    rw [CFSG.KC.LQT.PW.imgW_orW_of (fun j _ => CFSG.KC.LQT.PW.boolRec_lt _) hp i.isLt hpk,
      maskF_eq', CFSG.KC.LQT.PW.testBit_sum_two_pow]
    simp only [CFSG.KC.LQT.PW.indF, hk, dite_true, mem_smul_iff, ← hi]
    by_cases hm : i ∈ B <;> simp [hm]
  · have hn : ∀ i < 24, CFSG.KC.LQT.P.img (cX x) i ≠ k := fun i hi e => by
      rw [img_cX x ⟨i, hi⟩] at e
      exact hk (e ▸ Fin.isLt _)
    rw [CFSG.KC.LQT.PW.imgW_orW_none (fun j _ => CFSG.KC.LQT.PW.boolRec_lt _) hn]
    simp [CFSG.KC.LQT.PW.indF, hk]

theorem trio_fix (x : X24) (τ : Finset (Finset (Fin 24))) (hne : ∅ ∉ τ) (hcard : τ.card ≤ 24)
    (h : actTK 24 (cX x) (encTrioN τ) = encTrioN τ) : x • τ = τ := by
  have hD := encTrio_bound hne
  have hDl : (encTrio τ).length ≤ 24 := by rw [encTrio_length]; exact hcard
  set L := (encTrio τ).map (imgMask 24 (cX x)) with hLdef
  have hL : ∀ y, y ∈ L ↔ ∃ B ∈ τ, maskF (x • B) = y := by
    intro y
    rw [hLdef, List.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨B, hB, rfl⟩ := mem_encTrio.1 hm
      exact ⟨B, hB, (imgMask_maskF x B).symm⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨maskF B, mem_encTrio.2 ⟨B, hB, rfl⟩, imgMask_maskF x B⟩
  set A := CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN L) with hAdef
  have hA : ∀ a ∈ A, 0 < a ∧ a < 2 ^ 24 := by
    intro a ha
    obtain ⟨B, hB, rfl⟩ := (hL a).1 (mem_dedupS_sortN.1 ha)
    refine maskF_bound ?_
    rw [Finset.smul_finset_nonempty]
    exact Finset.nonempty_iff_ne_empty.2 fun e => hne (e ▸ hB)
  have hAl : A.length ≤ 24 := by
    refine (length_dedupS _).trans ?_
    rw [(sortN_perm L).length_eq, hLdef, List.length_map]
    exact hDl
  have heq : A = encTrio τ := by
    have h' : packL A = packL (encTrio τ) := by
      rw [← packK_eq, ← encTrioN_eq]
      have e : actTK 24 (cX x) (encTrioN τ) = packK A := by
        rw [actTK, encTrioN_eq, unpack_pack hDl hD]
      rw [← e, h]
    have := congrArg unpackK h'
    rwa [unpack_pack hAl hA, unpack_pack hDl hD] at this
  refine Finset.eq_of_subset_of_card_le (fun C hC => ?_) (by rw [Finset.card_smul_finset])
  obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.1 hC
  have hm : maskF (x • B) ∈ encTrio τ := by
    rw [← heq, hAdef, mem_dedupS_sortN, hL]
    exact ⟨B, hB, rfl⟩
  obtain ⟨B', hB', e⟩ := mem_encTrio.1 hm
  rwa [← maskF_inj e]

theorem testBit_orbMask (AC : List ℕ) (i b : ℕ) :
    (orbMask AC i).testBit b = AC.any fun c => decide (CFSG.KC.LQT.P.img c i = b) := by
  induction AC with
  | nil => exact Nat.zero_testBit b
  | cons c AC ih =>
    change (Nat.shiftLeft 1 (CFSG.KC.LQT.P.img c i) ||| orbMask AC i).testBit b = _
    rw [Nat.testBit_or, ih, List.any_cons, Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem orbMask_eq (A : List X24) {AC : List ℕ} (hA : (A.map cX).Perm AC) (i : Fin 24) :
    orbMask AC i = maskF (orbL A i) := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_orbMask, maskF_eq']
  have hany : (AC.any fun c => decide (CFSG.KC.LQT.P.img c i = b)) = true ↔
      ∃ a ∈ A, (((a : X24) : Perm (Fin 24)) i : ℕ) = b := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨c, hc, e⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (hA.mem_iff.2 hc)
      rw [decide_eq_true_eq, img_cX] at e
      exact ⟨a, ha, e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨cX a, hA.mem_iff.1 (List.mem_map_of_mem ha), by rw [decide_eq_true_eq, img_cX, e]⟩
  by_cases hb : b < 24
  · have := CFSG.KC.LQT.PW.testBit_sum_two_pow (orbL A i) ⟨b, hb⟩
    simp only at this
    rw [this, Bool.eq_iff_iff, hany, decide_eq_true_iff, orbL, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, Fin.ext e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, by rw [e]⟩
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (CFSG.KC.LQT.PW.sum_two_pow_lt _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))), Bool.eq_false_iff]
    intro h
    obtain ⟨a, -, e⟩ := hany.1 h
    exact hb (e ▸ Fin.isLt _)

theorem trio_code (A : List X24) {AC : List ℕ} (hA : (A.map cX).Perm AC)
    (hs : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN
      ((List.range 24).map (orbMask AC)))) = true) :
    encTrioN (((List.finRange 24).map (orbL A)).toFinset) = trioK 24 AC := by
  rw [trioK, packK_eq, encTrioN_eq]
  congr 1
  have hp := sincA_pairwise _ none hs
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
    (hp.imp le_of_lt) ?_
  refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
    (CFSG.KC.LQT.T2.sincA_spec _ none hs).1).2 fun m => ?_
  rw [Finset.mem_sort, Finset.mem_image, mem_dedupS_sortN, List.mem_map]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [List.mem_toFinset, List.mem_map] at hB
    obtain ⟨i, -, rfl⟩ := hB
    exact ⟨i, List.mem_range.2 i.isLt, orbMask_eq A hA i⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' := List.mem_range.1 hj
    refine ⟨orbL A ⟨j, hj'⟩, ?_, (orbMask_eq A hA ⟨j, hj'⟩).symm⟩
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨⟨j, hj'⟩, List.mem_finRange _, rfl⟩

private noncomputable def dedupR (l : List ℕ) (o : Option ℕ) : List ℕ :=
  List.rec (motive := fun _ => Option ℕ → List ℕ) (fun _ => [])
    (fun x _ ih o => Option.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x)))
      (fun y => Bool.rec (motive := fun _ => List ℕ) (List.cons x (ih (some x))) (ih (some x))
        (Nat.beq x y)) o) l o

private theorem dedupR_none (x : ℕ) (t : List ℕ) :
    dedupR (x :: t) none = x :: dedupR t (some x) := rfl

private theorem dedupR_some (x y : ℕ) (t : List ℕ) :
    dedupR (x :: t) (some y) = if x = y then dedupR t (some x) else x :: dedupR t (some x) := by
  change Bool.rec (motive := fun _ => List ℕ) (x :: dedupR t (some x)) (dedupR t (some x))
    (Nat.beq x y) = _
  cases hb : Nat.beq x y
  · exact (if_neg (Nat.ne_of_beq_eq_false hb)).symm
  · exact (if_pos (Nat.eq_of_beq_eq_true hb)).symm

private theorem dedupR_lt : ∀ (l : List ℕ) (o : Option ℕ), l.Pairwise (· ≤ ·) →
    (∀ y, o = some y → ∀ z ∈ l, y ≤ z) →
    (dedupR l o).Pairwise (· < ·) ∧ ∀ y, o = some y → ∀ z ∈ dedupR l o, y < z
  | [], _, _, _ => ⟨List.Pairwise.nil, fun _ _ _ h => absurd h List.not_mem_nil⟩
  | x :: t, o, hl, ho => by
    rw [List.pairwise_cons] at hl
    obtain ⟨ih1, ih2⟩ := dedupR_lt t (some x) hl.2 fun y hy z hz => by
      rw [← Option.some.inj hy]
      exact hl.1 z hz
    have keep : (x :: dedupR t (some x)).Pairwise (· < ·) :=
      List.Pairwise.cons (fun z hz => ih2 x rfl z hz) ih1
    cases o with
    | none =>
      rw [dedupR_none]
      exact ⟨keep, fun y hy => absurd hy (by simp)⟩
    | some p =>
      have hpx : p ≤ x := ho p rfl x List.mem_cons_self
      rw [dedupR_some]
      split_ifs with hxp
      · refine ⟨ih1, fun y hy z hz => ?_⟩
        rw [← Option.some.inj hy, ← hxp]
        exact ih2 x rfl z hz
      · refine ⟨keep, fun y hy z hz => ?_⟩
        rw [← Option.some.inj hy]
        rcases List.mem_cons.1 hz with rfl | hz
        · exact lt_of_le_of_ne hpx (Ne.symm hxp)
        · exact lt_of_le_of_lt hpx (ih2 x rfl z hz)

private theorem dedupS_lt {l : List ℕ} (h : l.Pairwise (· ≤ ·)) :
    (CFSG.KC.LQT.Syl.dedupS l).Pairwise (· < ·) :=
  (dedupR_lt l none h fun _ hy => absurd hy (by simp)).1

theorem actTK_encTrioN (x : X24) {τ : Finset (Finset (Fin 24))} (hne : ∅ ∉ τ)
    (hcard : τ.card ≤ 24) : actTK 24 (cX x) (encTrioN τ) = encTrioN (x • τ) := by
  have hD := encTrio_bound hne
  have hDl : (encTrio τ).length ≤ 24 := by rw [encTrio_length]; exact hcard
  rw [actTK, encTrioN_eq τ, unpack_pack hDl hD, encTrioN_eq (x • τ), packK_eq]
  congr 1
  set L := (encTrio τ).map (imgMask 24 (cX x)) with hLdef
  have hLl : L.length ≤ 2 ^ 17 := by rw [hLdef, List.length_map]; omega
  have hp : (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN L)).Pairwise (· < ·) :=
    dedupS_lt (CFSG.KC.LQT.PHSnd.sortN_sorted hLl)
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (hp.imp le_of_lt) (Finset.pairwise_sort _ _) ?_
  refine (List.perm_ext_iff_of_nodup (hp.imp ne_of_lt) (Finset.sort_nodup _ _)).2 fun m => ?_
  rw [mem_dedupS_sortN, hLdef, List.mem_map, Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨B, hB, rfl⟩ := mem_encTrio.1 hc
    exact ⟨x • B, Finset.smul_mem_smul_finset hB, (imgMask_maskF x B).symm⟩
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.1 hC
    exact ⟨maskF B, mem_encTrio.2 ⟨B, hB, rfl⟩, imgMask_maskF x B⟩

private theorem empty_not_mem_smul (x : X24) {τ : Finset (Finset (Fin 24))} (hne : ∅ ∉ τ) :
    ∅ ∉ x • τ := fun h => by
  obtain ⟨B, hB, e⟩ := Finset.mem_smul_finset.1 h
  exact hne (Finset.smul_finset_eq_empty.1 e ▸ hB)

private theorem trio_word {cA cB : ℕ} (hA : cX m24a = cA) (hB : cX m24b = cB)
    {τ : Finset (Finset (Fin 24))} (hne : ∅ ∉ τ) (hcard : τ.card ≤ 24) :
    ∀ w : List ℕ, (∀ i ∈ w, i < 2) →
      w.foldr (fun i y => actTK 24 ([cA, cB].getD i 0) y) (encTrioN τ) =
        encTrioN (w.foldr (fun i y => gensA.getD i 1 • y) τ) ∧
      ∅ ∉ w.foldr (fun i y => gensA.getD i 1 • y) τ ∧
      (w.foldr (fun i y => gensA.getD i 1 • y) τ).card ≤ 24
  | [], _ => ⟨rfl, hne, hcard⟩
  | i :: w, hw => by
    obtain ⟨h1, h2, h3⟩ :=
      trio_word hA hB hne hcard w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hg : [cA, cB].getD i 0 = cX (gensA.getD i 1) := by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by have := hw i List.mem_cons_self; omega
      · exact hA.symm
      · exact hB.symm
    rw [List.foldr_cons, List.foldr_cons, h1, hg, actTK_encTrioN _ h2 h3]
    exact ⟨rfl, empty_not_mem_smul _ h2, by rw [Finset.card_smul_finset]; exact h3⟩

private theorem cX_conj (g y : X24) :
    cX (g * y * g⁻¹) = CFSG.KC.LQT.P.conj 24 (cX g) (cX y) := by
  rw [cX_mul, cX_mul, cX_inv]
  rfl

private theorem class_word {cA cB : ℕ} (hA : cX m24a = cA) (hB : cX m24b = cB) (z : X24)
    (w : List ℕ) (hw : ∀ i ∈ w, i < 2) :
    w.foldr (fun i y => CFSG.KC.LQT.P.conj 24 ([cA, cB].getD i 0) y) (cX z) =
      cX (w.foldr (fun i y => gensC.getD i 1 • y) z) := by
  induction w with
  | nil => rw [List.foldr_nil, List.foldr_nil]
  | cons i w ih =>
    have h1 := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hg : [cA, cB].getD i 0 = cX (ConjAct.ofConjAct (gensC.getD i 1)) := by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by have := hw i List.mem_cons_self; omega
      · change cA = cX (ConjAct.ofConjAct (ConjAct.toConjAct m24a))
        rw [ConjAct.ofConjAct_toConjAct, hA]
      · change cB = cX (ConjAct.ofConjAct (ConjAct.toConjAct m24b))
        rw [ConjAct.ofConjAct_toConjAct, hB]
    have hs : ∀ (g : ConjAct X24) (y : X24),
        g • y = ConjAct.ofConjAct g * y * (ConjAct.ofConjAct g)⁻¹ := fun g y => ConjAct.smul_def g y
    rw [List.foldr_cons, List.foldr_cons, h1, hs, cX_conj, hg]

private theorem hkB_inj {B : List Blk} {R : ℕ} (hR : 0 < R) (hk : ∀ r < R, hkB B R r = true) :
    ∀ c ∈ flatB B, ∀ c' ∈ flatB B, hkK c = hkK c' → c = c' := by
  intro c hc c' hc' h
  have hP0 : 0 < hP := by unfold hP; norm_num
  set v := hkK c with hv
  have hvlt : v < hP := Nat.mod_lt _ hP0
  set r := v * R / hP with hr
  have hrR : r < R := by
    rw [hr, Nat.div_lt_iff_lt_mul hP0]
    exact Nat.mul_lt_mul_of_lt_of_le hvlt le_rfl hR |>.trans_eq (Nat.mul_comm _ _)
  have hnd : (((flatB B).filter fun d => inRange R r (hkK d)).map hkK).Nodup := by
    have h1 := sincK_nodup (hk r hrR)
    rw [(sortN_perm _).nodup_iff, filtL_eq, List.filter_map] at h1
    exact h1
  have hin : ∀ d, hkK d = v → inRange R r (hkK d) = true := fun d hd => by
    rw [hd]
    exact Nat.beq_refl _
  exact List.inj_on_of_nodup_map hnd (List.mem_filter.2 ⟨hc, hin c rfl⟩)
    (List.mem_filter.2 ⟨hc', hin c' h.symm⟩) h

private theorem foldr_mem {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω] (gens : List Γ) (x₀ : Ω)
    (S : Set Ω) (h0 : x₀ ∈ S) (hS : ∀ g ∈ gens, ∀ x ∈ S, g • x ∈ S) :
    ∀ w : List ℕ, (∀ i ∈ w, i < gens.length) → w.foldr (fun i y => gens.getD i 1 • y) x₀ ∈ S
  | [], _ => by rw [List.foldr_nil]; exact h0
  | i :: w, hw => by
    rw [List.foldr_cons]
    have hi := hw i List.mem_cons_self
    refine hS _ ?_ _ (foldr_mem gens x₀ S h0 hS w fun j hj => hw j (List.mem_cons_of_mem _ hj))
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

private theorem encTrio_inj {y y' : Finset (Finset (Fin 24))} (h : encTrio y = encTrio y') :
    y = y' := by
  have h1 := congrArg List.toFinset h
  simp only [encTrio, Finset.sort_toFinset] at h1
  exact Finset.image_injective (fun _ _ e => maskF_inj e) h1

private theorem encTrioN_inj {y y' : Finset (Finset (Fin 24))} (hy : ∅ ∉ y) (hyc : y.card ≤ 24)
    (hy' : ∅ ∉ y') (hyc' : y'.card ≤ 24) (h : encTrioN y = encTrioN y') : y = y' := by
  have h1 := congrArg unpackK h
  rw [encTrioN_eq y, encTrioN_eq y',
    unpack_pack (by rw [encTrio_length]; exact hyc) (encTrio_bound hy),
    unpack_pack (by rw [encTrio_length]; exact hyc') (encTrio_bound hy')] at h1
  exact encTrio_inj h1

private theorem length_two (a b : ℕ) : [a, b].length = 2 := rfl

private theorem gensC_length : gensC.length = 2 := rfl

private theorem class_code {cA cB zc : ℕ} (hA : cX m24a = cA) (hB : cX m24b = cB) {z : X24}
    (hz : cX z = zc) {w : List ℕ} (hw : ∀ i ∈ w, i < [cA, cB].length) {c : ℕ}
    (hwc : w.foldr (fun i y => CFSG.KC.LQT.P.conj 24 ([cA, cB].getD i 0) y) zc = c) :
    cX (w.foldr (fun i y => gensC.getD i 1 • y) z) = c := by
  have hw2 : ∀ i ∈ w, i < 2 := fun i hi => by
    have h := hw i hi
    rw [length_two] at h
    exact h
  rw [← class_word hA hB z w hw2, hz]
  exact hwc

private theorem class_closed {cA cB : ℕ} (hA : cX m24a = cA) (hB : cX m24b = cB)
    {Tr : List X24} {L : List ℕ} (hmem : ∀ y, y ∈ Tr ↔ cX y ∈ L)
    (hcl : ∀ y ∈ L, ∀ g ∈ [cA, cB], CFSG.KC.LQT.P.conj 24 g y ∈ L) :
    ∀ g ∈ gensC, ∀ x ∈ Tr, g • x ∈ Tr := by
  intro g hg x hx
  rw [hmem] at hx ⊢
  have hgc : cX (ConjAct.ofConjAct g) ∈ [cA, cB] := by
    have hg' : g ∈ [ConjAct.toConjAct m24a, ConjAct.toConjAct m24b] := hg
    rcases List.mem_cons.1 hg' with rfl | h
    · rw [ConjAct.ofConjAct_toConjAct, hA]
      exact List.mem_cons_self
    · rw [List.mem_singleton.1 h, ConjAct.ofConjAct_toConjAct, hB]
      exact List.mem_cons_of_mem _ List.mem_cons_self
  rw [ConjAct.smul_def, cX_conj]
  exact hcl _ hx _ hgc

private theorem class_inj {B : List Blk} {R : ℕ} (hR : 0 < R) (hk : ∀ r < R, hkB B R r = true)
    {Tr : List X24} (hmem : ∀ y, y ∈ Tr ↔ cX y ∈ flatB B) :
    ∀ a ∈ Tr, ∀ b ∈ Tr, hkey a = hkey b → a = b := by
  intro a ha b hb h
  rw [hkey_code, hkey_code] at h
  exact cX_injective (hkB_inj hR hk _ ((hmem a).1 ha) _ ((hmem b).1 hb) h)

private theorem class_reach {cA cB zc : ℕ} (hA : cX m24a = cA) (hB : cX m24b = cB) {z : X24}
    (hz : cX z = zc) {Tr : List X24} {L : List ℕ} (hmem : ∀ y, y ∈ Tr ↔ cX y ∈ L)
    (hreach : ∀ y ∈ L, ∃ w : List ℕ, (∀ i ∈ w, i < [cA, cB].length) ∧
      w.foldr (fun i y => CFSG.KC.LQT.P.conj 24 ([cA, cB].getD i 0) y) zc = y) :
    ∀ y ∈ Tr, ∀ S : Set X24, z ∈ S → (∀ g ∈ gensC, ∀ x ∈ S, g • x ∈ S) → y ∈ S := by
  intro y hy S hS0 hSc
  obtain ⟨w, hw, hwc⟩ := hreach _ ((hmem y).1 hy)
  have hwg : ∀ i ∈ w, i < gensC.length := fun i hi => by
    have h := hw i hi
    rw [length_two] at h
    rw [gensC_length]
    exact h
  rw [← cX_injective (class_code hA hB hz hw hwc)]
  exact foldr_mem gensC z S hS0 hSc w hwg

theorem class_sound (z : X24) (fuel : ℕ) {cA cB zc : ℕ} (hA : cX m24a = cA) (hB : cX m24b = cB)
    (hz : cX z = zc) (s K R : ℕ) (B : List Blk) (T : List (List (ℕ × ℕ × ℕ)))
    (hS : sortedB s B = true) (hz0 : memB zc B = true)
    (hb : ∀ k < K, blkRange (CFSG.KC.LQT.P.conj 24) zc [cA, cB] s
      (CFSG.KC.LQT.S.lenL (flatB B)) B T (k * 8) 8 = true)
    (hK : lenA B ≤ K * 8) (hR : 0 < R) (hk : ∀ r < R, hkB B R r = true)
    (hf : CFSG.KC.LQT.S.lenL (flatB B) ≤ fuel) :
    ((bfsOrbit tabX hkey gensC z fuel).1.map cX).Perm (flatB B) := by
  obtain ⟨hpw, hzc, hcl, hreach⟩ := CFSG.KC.LQT.PHSnd.orbit_cert hS hz0 hb hK
  obtain ⟨Tr, hTrmap, -⟩ := lift_codes (fun _ => True) fun c hc => by
    obtain ⟨w, hw, hwc⟩ := hreach c hc
    exact ⟨_, trivial, class_code hA hB hz hw hwc⟩
  have hmem := mem_iff_code_mem hTrmap
  have hnd : Tr.Nodup := List.Nodup.of_map cX (by rw [hTrmap]; exact hpw.imp ne_of_lt)
  have h0 : z ∈ Tr := (hmem z).2 (by rw [hz]; exact hzc)
  have hf' : Tr.length ≤ fuel := by
    have hlen : Tr.length = (flatB B).length := by rw [← hTrmap, List.length_map]
    rw [hlen, ← lenL_eq]
    exact hf
  have hP := CFSG.KC.LQT.PHSnd.bfsOrbit_perm tabX tabX_eq hkey gensC z fuel Tr hnd
    (class_inj hR hk hmem) h0 (class_closed hA hB hmem hcl) (class_reach hA hB hz hmem hreach)
    hf'
  rw [← hTrmap]
  exact hP.map cX

theorem trio_sound (τ : Finset (Finset (Fin 24))) (fuel : ℕ) {cA cB tc : ℕ}
    (hA : cX m24a = cA) (hB : cX m24b = cB) (hτ : encTrioN τ = tc) (hne : ∅ ∉ τ)
    (hcard : τ.card ≤ 24) (s K : ℕ) (B : List Blk) (T : List (List (ℕ × ℕ × ℕ)))
    (hS : sortedB s B = true) (hz0 : memB tc B = true)
    (hb : ∀ k < K, blkRange (actTK 24) tc [cA, cB] s (CFSG.KC.LQT.S.lenL (flatB B)) B T (k * 8) 8 =
      true)
    (hK : lenA B ≤ K * 8) (hf : CFSG.KC.LQT.S.lenL (flatB B) ≤ fuel) :
    ((bfsOrbit id encTrio gensA τ fuel).1.map encTrioN).Perm (flatB B) := by
  classical
  obtain ⟨hpw, htc, hcl, hreach⟩ := CFSG.KC.LQT.PHSnd.orbit_cert hS hz0 hb hK
  have hex : ∀ c ∈ flatB B, ∃ y : Finset (Finset (Fin 24)),
      (∅ ∉ y ∧ y.card ≤ 24) ∧ encTrioN y = c := by
    intro c hc
    obtain ⟨w, hw, hwc⟩ := hreach c hc
    obtain ⟨h1, h2, h3⟩ := trio_word hA hB hne hcard w hw
    refine ⟨_, ⟨h2, h3⟩, ?_⟩
    rw [← h1, hτ]
    exact hwc
  set Tr := (flatB B).attach.map fun c => (hex c.1 c.2).choose with hTr
  have hTrmap : Tr.map encTrioN = flatB B := by
    rw [hTr, List.map_map]
    refine (List.map_congr_left fun c _ => ?_).trans (List.attach_map_subtype_val _)
    exact (hex c.1 c.2).choose_spec.2
  have hgood : ∀ y ∈ Tr, ∅ ∉ y ∧ y.card ≤ 24 := by
    intro y hy
    rw [hTr, List.mem_map] at hy
    obtain ⟨c, -, rfl⟩ := hy
    exact (hex c.1 c.2).choose_spec.1
  have hmem : ∀ y, ∅ ∉ y → y.card ≤ 24 → encTrioN y ∈ flatB B → y ∈ Tr := by
    intro y hy hyc hc
    have e := (hex _ hc).choose_spec
    have e' : (hex _ hc).choose = y := encTrioN_inj e.1.1 e.1.2 hy hyc e.2
    rw [hTr, List.mem_map]
    exact ⟨⟨_, hc⟩, List.mem_attach _ _, e'⟩
  have hcode : ∀ y ∈ Tr, encTrioN y ∈ flatB B := fun y hy => by
    rw [← hTrmap]
    exact List.mem_map_of_mem hy
  have hnd : Tr.Nodup := List.Nodup.of_map encTrioN (by rw [hTrmap]; exact hpw.imp ne_of_lt)
  have h0 : τ ∈ Tr := hmem τ hne hcard (hτ ▸ htc)
  have hcl' : ∀ g ∈ gensA, ∀ x ∈ Tr, g • x ∈ Tr := by
    intro g hg x hx
    obtain ⟨hx1, hx2⟩ := hgood x hx
    have hgc : cX g ∈ [cA, cB] := by
      have hg' : g ∈ [m24a, m24b] := hg
      rcases List.mem_cons.1 hg' with rfl | h
      · rw [hA]
        exact List.mem_cons_self
      · rw [List.mem_singleton.1 h, hB]
        exact List.mem_cons_of_mem _ List.mem_cons_self
    refine hmem _ (empty_not_mem_smul g hx1) (by rw [Finset.card_smul_finset]; exact hx2) ?_
    rw [← actTK_encTrioN g hx1 hx2]
    exact hcl _ (hcode x hx) _ hgc
  have hinj : ∀ a ∈ Tr, ∀ b ∈ Tr, encTrio a = encTrio b → a = b :=
    fun _ _ _ _ h => encTrio_inj h
  have hreach' : ∀ y ∈ Tr, ∀ S : Set (Finset (Finset (Fin 24))), τ ∈ S →
      (∀ g ∈ gensA, ∀ x ∈ S, g • x ∈ S) → y ∈ S := by
    intro y hy S hS0 hSc
    obtain ⟨w, hw, hwc⟩ := hreach _ (hcode y hy)
    obtain ⟨h1, h2, h3⟩ := trio_word hA hB hne hcard w hw
    have e : w.foldr (fun i y => gensA.getD i 1 • y) τ = y := by
      obtain ⟨hy1, hy2⟩ := hgood y hy
      refine encTrioN_inj h2 h3 hy1 hy2 ?_
      rw [← h1, hτ]
      exact hwc
    rw [← e]
    exact foldr_mem gensA τ S hS0 hSc w hw
  have hf' : Tr.length ≤ fuel := by
    rw [hTr, List.length_map, List.length_attach, ← lenL_eq]
    exact hf
  have hP := CFSG.KC.LQT.PHSnd.bfsOrbit_perm id (fun _ => rfl) encTrio gensA τ fuel Tr hnd
    hinj h0 hcl' hreach' hf'
  rw [← hTrmap]
  exact hP.map encTrioN

end CFSG.KC.LQT.PH

end
