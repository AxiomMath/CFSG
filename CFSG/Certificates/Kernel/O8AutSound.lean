module

public import Certificates.Data.Kernel.O8.Aut
public import CFSG.Certificates.Kernel.O8ConstrSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.F2WordSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.KC.Enum (pidn pcomp permOK pg)

@[expose] def ChainOK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (kS kO nb BP NS CH : Nat)
    (D : List (List Int)) (S : Array (Array Nat)) (base : Array Nat) : Prop :=
  Binds n w PS kS nb BP S base ∧
    headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS nb BP ∧ n ≤ NS * CH ∧
    ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true

@[expose] def psiTArrG (n : ℕ) (Q : ℕ → Array ℕ) (y : ℕ) : Array ℕ :=
  (List.range 6).foldl (fun acc j => if y.testBit j then compA n acc (Q j) else acc) (idA n)

@[expose] def autCheckG (n k : ℕ) (S : Array (Array ℕ)) (B : Array ℕ) (D : List (List ℤ))
    (sz : List ℕ) (T : ℕ → Array ℕ) (X : ℕ → Array ℕ → Bool) : Bool :=
  let inR := fun z => allLt 63 fun y => (T (y + 1))[z]! != z
  rawChainOK n (S.extract 0 k) S B (OmegaEight.wordsOf k D) 4 &&
    rawOrbitSizes n S B == sz &&
    allLt 64 (fun y => isInvA n (T y) (invCand n (T y)) && siftA n (rawLevels n S B) B 0 (T y) &&
      X y (T y)) &&
    allLt 64 (fun y => allLt 64 fun y' => eqA n (T (y ^^^ y')) (compA n (T y) (T y'))) &&
    B.all inR &&
    allLt n (fun z => !(inR z) || (List.range 64).any fun y => (T y)[0]! == z)

namespace PA

open CFSG.Monster.B.Co2

theorem ctAndB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem ctOrB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem ctNotB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem ctAllN_iff {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [CFSG.KLie.CT.allN]
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [ctAndB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact h2 i h
      · have e : i = n := by omega
        rw [e]
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

theorem ctAnyN_iff {n : ℕ} {f : ℕ → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [CFSG.KLie.CT.anyN]
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [ctOrB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_ge i n with h' | h'
      · exact Or.inr ⟨i, h', h⟩
      · have e : i = n := by omega
        rw [e] at h
        exact Or.inl h

theorem pw2_eq (x : ℕ) : pw2 x = 2 ^ x := by
  exact (Nat.shiftLeft_eq 1 x).trans (Nat.one_mul _)

theorem fget_eq_pg (X i w : ℕ) : fget X i w = pg w (mask w) X i := by
  have h1 : fget X i w = X >>> (i * w) % 2 ^ w := by
    change (X >>> (i * w)) &&& maskN w = _
    rw [F2W.maskN_eq, Nat.and_two_pow_sub_one_eq_mod]
  rw [h1, Orb.pg_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]

theorem arr_ext {A B : Array ℕ} {n : ℕ} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ i < n, A[i]! = B[i]!) : A = B := by
  apply Array.ext (by omega)
  intro i h1 h2
  have := h i (by omega)
  rwa [getElem!_pos A i h1, getElem!_pos B i h2] at this

theorem unpack_size (n w P : ℕ) : (unpack n w P).size = n := by
  simp [unpack]

theorem wordA_size' (n : ℕ) (S Sinv : Array (Array ℕ)) (wd : List ℤ) :
    (wordA n S Sinv wd).size = n := by
  cases wd <;> simp [wordA, idA, compA]

theorem arr_eq_of_rep {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (hu : u.size = n) (hgt : Rep n t g) (hgu : Rep n u g) : t = u :=
  arr_ext ht hu fun i hi => by rw [hgt.apply hi, hgu.apply hi]

theorem unpack_of_toList {n w P : ℕ} {A : Array ℕ}
    (h : A.toList = (List.range n).map fun i => fget P i w) : A = unpack n w P := by
  have hs : A.size = n := by
    rw [← Array.length_toList, h]
    simp
  apply arr_ext hs (unpack_size _ _ _)
  intro i hi
  have e := List.getElem_of_eq h (i := i) (by rw [Array.length_toList]; omega)
  simp only [Array.getElem_toList, List.getElem_map, List.getElem_range] at e
  rw [Orb.unpack_get hi, getElem!_pos A i (by omega), e, fget_eq_pg]

private theorem prep_unique {n w P : ℕ} {g h : Equiv.Perm (Fin n)} (hg : Orb.PRep n w P g)
    (hh : Orb.PRep n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem lt_of_shr {X k : ℕ} (h : X >>> k = 0) : X < 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow] at h
  rcases Nat.lt_or_ge X (2 ^ k) with h' | h'
  · exact h'
  · have := Nat.div_pos h' (Nat.two_pow_pos k)
    omega

theorem pg_high {n w P m : ℕ} (hP : P >>> (n * w) = 0) (hm : n ≤ m) : pg w (mask w) P m = 0 := by
  rw [Orb.pg_eq, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (lt_of_shr hP)
    (Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left w hm)))]
  rfl

theorem unpack_get' {n w P m : ℕ} (hP : P >>> (n * w) = 0) :
    (unpack n w P)[m]! = pg w (mask w) P m := by
  by_cases hm : m < n
  · exact Orb.unpack_get hm
  · rw [pg_high hP (by omega), getElem!_neg (unpack n w P) m (by rw [unpack_size]; omega)]
    rfl

end PA

open CFSG.Monster.B.Co2 PA

private def gprod {n : ℕ} (q : ℕ → Equiv.Perm (Fin n)) (y : ℕ) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | m + 1 => gprod q y m * (if y.testBit m then q m else 1)

private theorem gprod_succ {n : ℕ} (q : ℕ → Equiv.Perm (Fin n)) (y m : ℕ) :
    gprod q y (m + 1) = gprod q y m * (if y.testBit m then q m else 1) := rfl

private theorem rep_psiT {n : ℕ} {Q : ℕ → Array ℕ} {q : ℕ → Equiv.Perm (Fin n)}
    (hQ : ∀ j < 6, Rep n (Q j) (q j)) (y : ℕ) : ∀ m ≤ 6,
    Rep n ((List.range m).foldl (fun acc j => if y.testBit j then compA n acc (Q j) else acc)
      (idA n)) (gprod q y m) ∧
    ((List.range m).foldl (fun acc j => if y.testBit j then compA n acc (Q j) else acc)
      (idA n)).size = n
  | 0, _ => ⟨rep_idA, by simp [idA]⟩
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := rep_psiT hQ y m (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, gprod_succ]
    cases hb : y.testBit m
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      exact ⟨ih1, ih2⟩
    · simp only [↓reduceIte]
      exact ⟨rep_compA ih1 (hQ m (by omega)), by simp [compA]⟩

private theorem bitN_eq' (x i : ℕ) : bitN x i = if x.testBit i then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

private noncomputable def fq (n w : ℕ) (QT : ℕ → ℕ) (y m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (pidn n w) (fun j ih => CFSG.KC.Loop.strictN ih fun acc =>
    Bool.rec (motive := fun _ => ℕ) acc (pcomp n w (mask w) acc (QT j)) (Nat.beq (bitN y j) 1)) m

private theorem foldQT_eq (n w : ℕ) (QT : ℕ → ℕ) (y : ℕ) : foldQT n w QT y = fq n w QT y 6 := rfl

private theorem fq_succ (n w : ℕ) (QT : ℕ → ℕ) (y m : ℕ) : fq n w QT y (m + 1) =
    if y.testBit m then pcomp n w (mask w) (fq n w QT y m) (QT m) else fq n w QT y m := by
  have e : fq n w QT y (m + 1) = CFSG.KC.Loop.strictN (fq n w QT y m) (fun acc =>
      Bool.rec (motive := fun _ => ℕ) acc (pcomp n w (mask w) acc (QT m)) (Nat.beq (bitN y m) 1)) :=
    rfl
  rw [e, F2W.strictN_eq]
  have hbit : Nat.beq (bitN y m) 1 = y.testBit m := by
    rw [bitN_eq']
    cases y.testBit m <;> rfl
  rw [hbit]
  cases y.testBit m <;> rfl

private theorem prep_fq {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {QT : ℕ → ℕ}
    {q : ℕ → Equiv.Perm (Fin n)} (hQ : ∀ j < 6, Orb.PRep n w (QT j) (q j)) (y : ℕ) :
    ∀ m ≤ 6, Orb.PRep n w (fq n w QT y m) (gprod q y m) ∧ fq n w QT y m >>> (n * w) = 0
  | 0, _ => ⟨Orb.prep_pidn hn hw, PF.pidn_shr hn hw⟩
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := prep_fq hn hw hQ y m (by omega)
    have h32 : n < 2 ^ 32 := by omega
    rw [fq_succ, gprod_succ]
    cases hb : y.testBit m
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      exact ⟨ih1, ih2⟩
    · simp only [↓reduceIte]
      exact ⟨Orb.prep_pcomp h32 ih1 (hQ m (by omega)), PF.pcomp_shr _ _ h32 (PF.w_pos hw)⟩

private theorem fget_orN' {d m : ℕ} {f : ℕ → ℕ} (hf : ∀ i < m, f i < 2 ^ d) {j : ℕ}
    (hj : j < m) : fget (orN m fun i => Nat.shiftLeft (f i) (Nat.mul d i)) j d = f j := by
  have he : (orN m fun i => Nat.shiftLeft (f i) (Nat.mul d i)) = orN m fun i => f i <<< (d * i) :=
    rfl
  rw [he, fget_eq_pg, Orb.pg_eq, ← Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, F2W.testBit_orN_fields hf]
  by_cases ht : t < d
  · have hd : 0 < d := by omega
    have e1 : (d * j + t) / d = j := by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt ht, Nat.add_zero]
    have e2 : (d * j + t) % d = t := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
    have e3 : d * j + t < d * m := by
      have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ] at this
      omega
    simp [ht, e1, e2, e3]
  · simp only [ht, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf j hj)
      (Nat.pow_le_pow_right (by decide) (by omega)))).symm

private theorem tab_facts {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {QT : ℕ → ℕ}
    {Q : ℕ → Array ℕ} {q : ℕ → Equiv.Perm (Fin n)}
    (hQ : ∀ j < 6, Rep n (Q j) (q j) ∧ Orb.PRep n w (QT j) (q j)) {y : ℕ} (hy : y < 64) :
    Rep n (psiTArrG n Q y) (gprod q y 6) ∧
      psiTArrG n Q y = unpack n w (psiAt n w (psiTab n w QT) y) := by
  obtain ⟨h1, h2⟩ := rep_psiT (fun j hj => (hQ j hj).1) y 6 le_rfl
  have hQT : ∀ j < 6, Orb.PRep n w (QT j) (q j) := fun j hj => (hQ j hj).2
  have hP : Orb.PRep n w (psiAt n w (psiTab n w QT) y) (gprod q y 6) := by
    have e : psiAt n w (psiTab n w QT) y = foldQT n w QT y := by
      unfold psiAt psiTab
      refine fget_orN' (d := Nat.mul n w) (f := foldQT n w QT) (fun i _ => ?_) hy
      rw [foldQT_eq]
      exact lt_of_shr (prep_fq hn hw hQT i 6 le_rfl).2
    rw [e, foldQT_eq]
    exact (prep_fq hn hw hQT y 6 le_rfl).1
  exact ⟨h1, arr_eq_of_rep h2 (unpack_size _ _ _) h1 (Orb.rep_unpack hP)⟩

private theorem comm_gprod {n : ℕ} {q : ℕ → Equiv.Perm (Fin n)}
    (hc : ∀ i < 6, ∀ j < 6, q i * q j = q j * q i) {k : ℕ} (hk : k < 6) (y : ℕ) :
    ∀ m ≤ 6, Commute (q k) (gprod q y m)
  | 0, _ => Commute.one_right _
  | m + 1, hm => by
    rw [gprod_succ]
    refine (comm_gprod hc hk y m (by omega)).mul_right ?_
    split
    · exact hc k hk m (by omega)
    · exact Commute.one_right _

private theorem gprod_xor {n : ℕ} {q : ℕ → Equiv.Perm (Fin n)} (hi : ∀ j < 6, q j * q j = 1)
    (hc : ∀ i < 6, ∀ j < 6, q i * q j = q j * q i) (y y' : ℕ) :
    ∀ m ≤ 6, gprod q (y ^^^ y') m = gprod q y m * gprod q y' m
  | 0, _ => by simp [gprod]
  | m + 1, hm => by
    rw [gprod_succ, gprod_succ, gprod_succ, gprod_xor hi hc y y' m (by omega), Nat.testBit_xor]
    have hqq := hi m (by omega)
    have hxor : (if (y.testBit m ^^ y'.testBit m) = true then q m else 1) =
        (if y.testBit m = true then q m else 1) * (if y'.testBit m = true then q m else 1) := by
      cases y.testBit m <;> cases y'.testBit m <;> simp [hqq]
    have hcm : Commute (if y.testBit m = true then q m else 1) (gprod q y' m) := by
      split
      · exact comm_gprod hc (by omega) y' m (by omega)
      · exact Commute.one_left _
    rw [hxor]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, hcm.eq]

private theorem testBit_orN_pw2 {m z : ℕ} {a : ℕ → ℕ}
    (h : (orN m fun y => pw2 (a y)).testBit z = true) : ∃ y < m, a y = z := by
  induction m with
  | zero => simp [F2W.orN_zero] at h
  | succ m ih =>
    simp only [F2W.orN_succ, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · refine ⟨m, Nat.lt_succ_self m, ?_⟩
      rw [pw2_eq, Nat.testBit_two_pow] at h
      exact of_decide_eq_true h
    · obtain ⟨y, hy, e⟩ := ih h
      exact ⟨y, by omega, e⟩

private theorem lenW_eq' : ∀ D : List (List Int), CFSG.KS.Mathieu.lenW D = D.length
  | [] => rfl
  | _ :: D => congrArg Nat.succ (lenW_eq' D)

private theorem aut_core {n w k nb : ℕ} {S : Array (Array ℕ)} {B : Array ℕ} {D : List (List ℤ)}
    {sz : List ℕ} {T : ℕ → Array ℕ} {X : ℕ → Array ℕ → Bool} {PA PAI LA TA TAI : ℕ → ℕ}
    {kSA BPA NSA CHA : ℕ} {QT : ℕ → ℕ} {Q : ℕ → Array ℕ} {extra : ℕ → ℕ → Bool}
    (hA : ChainOK n w PA PAI LA TA TAI kSA k nb BPA NSA CHA D S B)
    (hs : (List.range nb).map (fun i => rcnt (LA i)) = sz)
    (hT : ∀ y < 64, T y = psiTArrG n Q y)
    (hQ0 : ∀ j < 6, Q j = unpack n w (QT j))
    (hX : ∀ y < 64, ∀ P, permOK n w (mask w) (n * w) P P = true → extra y P = true →
      X y (unpack n w P) = true)
    (h : autPsiOK n w QT LA TAI BPA nb extra = true) :
    autCheckG n k S B D sz T X = true := by
  obtain ⟨hb, hh, hl, hNS, hsch⟩ := hA
  have hb' := hb
  obtain ⟨hn0, hw, hn16, -, -, hBs, hBt⟩ := hb'
  have hh' := hh
  unfold headK at hh'
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh'
  obtain ⟨-, -, -, hlen, hperm, -, -, hbase⟩ := hh'
  have hn : n < 16777216 := by omega
  have h32 : n < 2 ^ 32 := by omega
  have hkS : k + D.length = kSA := by
    have := Nat.eq_of_beq_eq_true hlen
    rw [lenW_eq' D] at this
    exact (Nat.add_comm _ _).trans this
  unfold autPsiOK at h
  simp only [ctAndB_eq, Bool.and_eq_true, Orb.strictB_eq] at h
  obtain ⟨hqc, hrow, hreg, horb⟩ := h
  unfold qtCommOK at hqc
  simp only [ctAndB_eq, Bool.and_eq_true, ctAllN_iff] at hqc
  obtain ⟨hsq, hcm⟩ := hqc
  obtain ⟨q, hq⟩ : ∃ q : ℕ → Equiv.Perm (Fin n), ∀ j, q j = permOfArr n (unpack n w (QT j)) :=
    ⟨_, fun _ => rfl⟩
  have hQ : ∀ j < 6, Rep n (Q j) (q j) ∧ Orb.PRep n w (QT j) (q j) := fun j hj => by
    have h1 := hsq j hj
    unfold Prim.sqIdK at h1
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h1
    obtain ⟨-, -, -, hlt⟩ := PF.canon_facts h1.1
    have hii : isInvA n (unpack n w (QT j)) (unpack n w (QT j)) = true := by
      unfold isInvA
      rw [allLt_iff]
      intro i hi
      rw [Orb.unpack_get hi, Orb.unpack_get (hlt i hi), ← PF.pg_pcomp h32 hi,
        Nat.eq_of_beq_eq_true h1.2, PF.pg_pidn hn hw hi]
      simp [hlt i hi]
    have hr := (rep_permOfArr hii).1
    rw [hQ0 j hj, hq j]
    exact ⟨hr, Orb.prep_of_rep hr⟩
  have hinv : ∀ j < 6, q j * q j = 1 := fun j hj => by
    have h1 := hsq j hj
    unfold Prim.sqIdK at h1
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h1
    have hP := Orb.prep_pcomp h32 (hQ j hj).2 (hQ j hj).2
    rw [Nat.eq_of_beq_eq_true h1.2] at hP
    exact prep_unique hP (Orb.prep_pidn hn hw)
  have hcomm : ∀ i < 6, ∀ j < 6, q i * q j = q j * q i := fun i hi j hj => by
    have h1 := hcm i hi j hj
    unfold Prim.commK at h1
    rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true] at h1
    have hP := Orb.prep_pcomp h32 (hQ i hi).2 (hQ j hj).2
    rw [Nat.eq_of_beq_eq_true h1.2.2] at hP
    exact prep_unique hP (Orb.prep_pcomp h32 (hQ j hj).2 (hQ i hi).2)
  have hTy : ∀ y < 64, T y = unpack n w (psiAt n w (psiTab n w QT) y) := fun y hy =>
    (hT y hy).trans (tab_facts hn hw hQ hy).2
  have hRy : ∀ y < 64, Rep n (T y) (gprod q y 6) := fun y hy => by
    rw [hT y hy]
    exact (tab_facts hn hw hQ hy).1
  rw [ctAllN_iff] at hrow
  unfold baseRegOK at hreg
  rw [ctAllN_iff] at hreg
  unfold psiOrbitOK at horb
  rw [Orb.strictB_eq, ctAllN_iff] at horb
  unfold autCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [wordsOf_eq, hkS]
    exact rawChainK_sound hb hh hl hNS hsch
  · rw [rawOrbitSizesK_sound hb hperm hl, hs]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro y hy
    have hr := hrow y hy
    unfold psiRowOK at hr
    simp only [Orb.strictB_eq, ctAndB_eq, Bool.and_eq_true] at hr
    obtain ⟨hpP, hsP, heP⟩ := hr
    simp only [Bool.and_eq_true]
    refine ⟨⟨isInvA_of_rep (hRy y hy) (rep_invCand (hRy y hy)), ?_⟩, ?_⟩
    · rw [hTy y hy]
      exact siftK_sound hb hperm hl rfl (range_of_permOK hpP) hsP
    · rw [hTy y hy]
      exact hX y hy _ hpP heP
  · rw [allLt_iff]
    intro y hy
    rw [allLt_iff]
    intro y' hy'
    have hxy : y ^^^ y' < 64 := Nat.xor_lt_two_pow (n := 6) hy hy'
    exact (eqA_iff (hRy _ hxy) (rep_compA (hRy y hy) (hRy y' hy'))).2
      (gprod_xor hinv hcomm y y' 6 le_rfl)
  · rw [Array.all_eq_true]
    intro i hi
    rw [hBs] at hi
    have hBi : B[i] = pg w (mask w) BPA i := by
      rw [← getElem!_pos B i (by omega), hBt i hi]
    have hbn : pg w (mask w) BPA i < n := by
      have := Orb.allN_iff.1 hbase i hi
      rwa [Nat.blt_eq] at this
    have hr := hreg i hi
    rw [Orb.strictB_eq, ctAllN_iff] at hr
    rw [hBi, allLt_iff]
    intro y hy
    have h1 := hr y hy
    rw [ctNotB_eq, Bool.not_eq_true'] at h1
    have h1' : Nat.beq (pg w (mask w) (psiAt n w (psiTab n w QT) (y + 1)) (pg w (mask w) BPA i))
        (pg w (mask w) BPA i) = false := h1
    rw [hTy (y + 1) (by omega), Orb.unpack_get hbn]
    exact bne_iff_ne.2 (Nat.ne_of_beq_eq_false h1')
  · rw [allLt_iff]
    intro z hz
    have h1 := horb z hz
    rw [ctOrB_eq, Bool.or_eq_true] at h1
    rw [Bool.or_eq_true]
    rcases h1 with h1 | h1
    · rw [F2W.bit_eq] at h1
      obtain ⟨y, hy, hyz⟩ := testBit_orN_pw2 h1
      right
      rw [List.any_eq_true]
      refine ⟨y, List.mem_range.2 hy, ?_⟩
      rw [hTy y hy, Orb.unpack_get hn0, hyz]
      exact beq_self_eq_true _
    · rw [ctAnyN_iff] at h1
      obtain ⟨y, hy, hyz⟩ := h1
      have hyz' : pg w (mask w) (psiAt n w (psiTab n w QT) (y + 1)) z = z :=
        Nat.eq_of_beq_eq_true hyz
      have hne : ¬ (allLt 63 fun y => (T (y + 1))[z]! != z) = true := by
        intro hc
        have := allLt_iff.1 hc y hy
        rw [hTy (y + 1) (Nat.succ_lt_succ hy), Orb.unpack_get hz, hyz'] at this
        exact absurd this (by simp)
      left
      simp [hne]

private theorem pg_land {P i : ℕ} (hi : i < 120) :
    pg 9 (mask 9) P i = pg 9 (mask 9) (Nat.land P (maskN 1080)) i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [PF.testBit_pgM, PF.testBit_pgM]
  by_cases hk : k < 9
  · have e : Nat.land P (maskN 1080) = P &&& (2 ^ 1080 - 1) := by
      rw [← F2W.maskN_eq]
      rfl
    have h1 : 9 * i + k < 1080 := by omega
    rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [hk, h1]
  · simp [hk]

theorem autP_sound {S OS : Array (Array ℕ)} {B OB : Array ℕ} {D OD qw : List (List ℤ)}
    {sz : List ℕ} {T ψ : ℕ → Array ℕ} {PA PAI LA TA TAI PO POI LO TO TOI PSI : Nat → Nat}
    {kSA kSO BPA BPO NSA NSO CHA CHO : Nat}
    (hA : ChainOK 360 9 PA PAI LA TA TAI kSA 10 7 BPA NSA CHA D S B)
    (hO : ChainOK 360 9 PO POI LO TO TOI kSO 8 7 BPO NSO CHO OD OS OB)
    (hs : (List.range 7).map (fun i => rcnt (LA i)) = sz)
    (hT : ∀ y < 64, T y = psiTArrG 360 (fun j => wordA 360 OS (rawInvs 360 OS) (qw.getD j [])) y)
    (hψ : ∀ y < 64, (ψ y).toList = (List.range 120).map fun i => fget (PSI y) i 9)
    (hl : allN 6 (fun j => lettersK kSO (qw.getD j [])) = true)
    (h : autPsiOK 360 9 (fun j => wordK 360 9 (mask 9) (pidn 360 9) PO POI (qw.getD j [])) LA TAI BPA 7
      (fun y P => andB (siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) LO TOI BPO 7 0 P)
        (Nat.beq (Nat.land P (maskN 1080)) (PSI y))) = true) :
    autCheckG 360 10 S B D sz T
      (fun y g => siftA 360 (rawLevels 360 OS OB) OB 0 g && eqA 120 (OmegaEight.copy0Arr g) (ψ y)) =
      true := by
  obtain ⟨hbO, hhO, hlO, -, -⟩ := hO
  have hbO' := hbO
  obtain ⟨-, hwO, -, hOS, hOSj, -, -⟩ := hbO'
  have hhO' := hhO
  unfold headK at hhO'
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hhO'
  obtain ⟨-, -, -, -, hpermO, -, -, -⟩ := hhO'
  have hrep : ∀ h < kSO, Rep 360 (unpack 360 9 (PO h)) (permOfArr 360 (unpack 360 9 (PO h))) ∧
      Rep 360 (unpack 360 9 (POI h)) (permOfArr 360 (unpack 360 9 (PO h)))⁻¹ := fun h hh =>
    rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 hpermO h hh))
  have hS' : ∀ h < kSO, Rep 360 OS[h]! (permOfArr 360 (unpack 360 9 (PO h))) := fun h hh => by
    rw [hOSj h hh]
    exact (hrep h hh).1
  have hSi : ∀ h < kSO,
      Rep 360 (rawInvs 360 OS)[h]! (permOfArr 360 (unpack 360 9 (PO h)))⁻¹ := fun h hh => by
    rw [Orb.rawInvs_get (by omega)]
    exact rep_invCand (hS' h hh)
  rw [ctAllN_iff] at hl
  refine aut_core hA hs hT (fun j hj => ?_) (fun y hy P hP he => ?_) h
  · obtain ⟨hP, hlo⟩ := Orb.prep_wordK (gs := fun h => permOfArr 360 (unpack 360 9 (PO h)))
      (j := kSO) (by decide) hwO (fun h hh => Orb.prep_of_rep (hrep h hh).1)
      (fun h hh => Orb.prep_of_rep (hrep h hh).2) _ (hl j hj)
    exact arr_eq_of_rep (wordA_size' _ _ _ _) (unpack_size _ _ _)
      (rep_wordA (gs := fun h => permOfArr 360 (unpack 360 9 (PO h))) hS' hSi _ hlo)
      (Orb.rep_unpack hP)
  · rw [ctAndB_eq, Bool.and_eq_true] at he
    simp only [Bool.and_eq_true]
    refine ⟨siftK_sound hbO hpermO hlO rfl (range_of_permOK hP) he.1, ?_⟩
    rw [unpack_of_toList (hψ y hy), ← Nat.eq_of_beq_eq_true he.2]
    unfold eqA
    rw [allLt_iff]
    intro i hi
    rw [beq_iff_eq, OmegaEight.copy0Arr, getElem!_ofFn_nat _ hi, Orb.unpack_get (by omega),
      Orb.unpack_get hi]
    exact pg_land hi

theorem autM_sound {S : Array (Array ℕ)} {B : Array ℕ} {D : List (List ℤ)} {sz : List ℕ}
    {T ψ : ℕ → Array ℕ} {PA PAI LA TA TAI PSI : Nat → Nat} {kSA BPA NSA CHA : Nat}
    (hA : ChainOK 136 8 PA PAI LA TA TAI kSA 11 7 BPA NSA CHA D S B)
    (hs : (List.range 7).map (fun i => rcnt (LA i)) = sz)
    (hT : ∀ y < 64, T y = psiTArrG 136 (fun j => ψ (2 ^ j)) y)
    (hψ : ∀ y < 64, (ψ y).toList = (List.range 136).map fun i => fget (PSI y) i 8)
    (h : autPsiOK 136 8 (fun j => PSI (pw2 j)) LA TAI BPA 7 (fun y P => Nat.beq P (PSI y)) = true) :
    autCheckG 136 11 S B D sz T (fun y g => eqA 136 g (ψ y)) = true := by
  refine aut_core hA hs hT (fun j hj => ?_) (fun y hy P _ he => ?_) h
  · have h64 : 2 ^ j < 64 := Nat.pow_lt_pow_right (by decide) hj
    rw [pw2_eq]
    exact unpack_of_toList (hψ _ h64)
  · rw [Nat.eq_of_beq_eq_true he, ← unpack_of_toList (hψ y hy)]
    exact eqA_self _

end CFSG.KC.O8

end
