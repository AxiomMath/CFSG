module

public import CFSG.Certificates.Kernel.VecKOrbit
public import CFSG.Sporadic.HS.CertSpec
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native
open scoped Matrix

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem notB_eq (a : Bool) : notB a = !a := by
  cases a <;> rfl

private theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.one_shiftLeft]

private theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · subst h
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

private theorem allL_iff {α : Type} {f : α → Bool} : ∀ L : List α, allL f L = true ↔ ∀ x ∈ L, f x = true
  | [] => by simp [allL]
  | a :: L => by
    change andB (f a) (allL f L) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, allL_iff L]
    simp

private theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    change getL x L i = _
    rw [getL_eq x L i]
    rfl

private theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenL L) = _
    rw [lenL_eq L]
    rfl

private theorem eqL_sound : ∀ L M : List Nat, eqL L M = true → L = M
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | a :: L, b :: M, h => by
    have h' : andB (Nat.beq a b) (eqL L M) = true := h
    rw [andB_eq, Bool.and_eq_true] at h'
    rw [Nat.eq_of_beq_eq_true h'.1, eqL_sound L M h'.2]

private theorem getL_array (A : Array Nat) {i : Nat} (hi : i < A.size) : getL 0 A.toList i = A[i]! := by
  rw [getL_eq, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some, Array.getElem_toList,
    getElem!_pos A i hi]

private def matF (d N : Nat) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  CFSG.Sporadic.SmallF2.rowsMatrix d (unpackR d N)

private theorem toVecD_vmF (d N v : Nat) :
    CFSG.Sporadic.SmallF2.toVecD d (vmF d N v) = CFSG.Sporadic.SmallF2.toVecD d v ᵥ* matF d N := by
  rw [← CFSG.KC.F2W.vecMulN_unpackR, CFSG.Sporadic.SmallF2.toVecD_vecMulN]
  rfl

private theorem matF_mul (d A B : Nat) : matF d (mulF d A B) = matF d A * matF d B := by
  unfold matF
  rw [← CFSG.KC.F2W.mulRows_unpackR, CFSG.Sporadic.SmallF2.rowsMatrix_mulRows]

theorem unpackR_idF (d : Nat) : unpackR d (idF d) = CFSG.Sporadic.SmallF2.Native.idRows d := by
  unfold unpackR CFSG.Sporadic.SmallF2.Native.idRows
  congr 1
  funext i
  rw [← CFSG.KC.F2W.rowF_eq]
  have hf : ∀ j < d, pw2 j < 2 ^ d := fun j hj => by
    rw [pw2_eq]
    exact Nat.pow_lt_pow_right (by omega) hj
  exact CFSG.KC.F2W.rowF_orN d (f := pw2) hf i.isLt

private theorem matF_id (d : Nat) : matF d (idF d) = 1 := by
  unfold matF
  rw [unpackR_idF, CFSG.Sporadic.SmallF2.rowsMatrix_idRows]

theorem powK_succ (d M e : Nat) : powK d M (e + 1) = mulF d (powK d M e) M := by
  change strictN (powK d M e) (fun a => mulF d a M) = _
  exact strictN_eq _ _

theorem powRows_unpackR (d M : Nat) : ∀ e, powRows d (unpackR d M) e = unpackR d (powK d M e)
  | 0 => (unpackR_idF d).symm
  | e + 1 => by
    change mulRows d (powRows d (unpackR d M) e) (unpackR d M) = _
    rw [powRows_unpackR d M e, CFSG.KC.F2W.mulRows_unpackR, ← powK_succ]

private theorem vmF_ext {d x y : Nat} (hx : x < 2 ^ d) (hy : y < 2 ^ d)
    (h : CFSG.Sporadic.SmallF2.toVecD d x = CFSG.Sporadic.SmallF2.toVecD d y) : x = y :=
  CFSG.Sporadic.SmallF2.toVecD_injective hx hy h

theorem vmF_mulF (d A B v : Nat) : vmF d (mulF d A B) v = vmF d B (vmF d A v) := by
  apply vmF_ext (CFSG.KC.F2W.vmF_lt _ _ _) (CFSG.KC.F2W.vmF_lt _ _ _)
  rw [toVecD_vmF, toVecD_vmF, toVecD_vmF, matF_mul, Matrix.vecMul_vecMul]

theorem vmF_idF {d v : Nat} (hv : v < 2 ^ d) : vmF d (idF d) v = v := by
  apply vmF_ext (CFSG.KC.F2W.vmF_lt _ _ _) hv
  rw [toVecD_vmF, matF_id, Matrix.vecMul_one]

theorem vmF_powK {d v : Nat} (M : Nat) (hv : v < 2 ^ d) : ∀ e, vmF d (powK d M e) v = (vmF d M)^[e] v
  | 0 => vmF_idF hv
  | e + 1 => by
    rw [powK_succ, vmF_mulF, vmF_powK M hv e, Function.iterate_succ_apply']

theorem vmF_inv {d N X v : Nat} (h : Nat.beq (mulF d N X) (idF d) = true) (hv : v < 2 ^ d) :
    vmF d X (vmF d N v) = v := by
  rw [← vmF_mulF, Nat.eq_of_beq_eq_true h, vmF_idF hv]

structure VPts (d n : Nat) (p : Nat → Nat) : Prop where
  n_lt : n < 2 ^ 30
  lt : ∀ h < n, p h < 2 ^ d
  inj : ∀ i < n, ∀ j < n, p i = p j → i = j

@[expose] def Realizes (d n : Nat) (p : Nat → Nat) (T : Table) (N : Nat) : Prop :=
  T.size = n ∧ ∀ h < n, ap T h < n ∧ p (ap T h) = vmF d N (p h)

theorem Realizes.ap_eq {d n : Nat} {p : Nat → Nat} {T : Table} {N : Nat} (hP : VPts d n p)
    (hT : Realizes d n p T N) {f : Nat → Nat} (hf : ∀ h < n, f h < n ∧ p (f h) = vmF d N (p h)) :
    ∀ h < n, ap T h = f h := fun h hh =>
  hP.inj _ (hT.2 h hh).1 _ (hf h hh).1 (by rw [(hT.2 h hh).2, (hf h hh).2])

theorem real_id {d n : Nat} {p : Nat → Nat} (hP : VPts d n p) : Realizes d n p (idT n) (idF d) := by
  obtain ⟨hs, hv⟩ := CFSG.KS.TW.idT_TR (n := n) (by have := hP.n_lt; omega)
  exact ⟨hs, fun h hh => ⟨by rw [(hv h hh).1]; exact hh, by rw [(hv h hh).1, vmF_idF (hP.lt h hh)]⟩⟩

private theorem ap_compT {n : Nat} (P Q : Table) {i : Nat} (hi : i < n) :
    ap (compT n P Q) i = ap P (ap Q i) := by
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem real_comp {d n : Nat} {p : Nat → Nat} {P Q : Table} {NP NQ : Nat}
    (hP : Realizes d n p P NP) (hQ : Realizes d n p Q NQ) :
    Realizes d n p (compT n P Q) (mulF d NQ NP) := by
  refine ⟨by simp [compT], fun h hh => ?_⟩
  rw [ap_compT P Q hh]
  obtain ⟨q1, q2⟩ := hQ.2 h hh
  obtain ⟨p1, p2⟩ := hP.2 _ q1
  exact ⟨p1, by rw [p2, q2, vmF_mulF]⟩

theorem real_pow {d n : Nat} {p : Nat → Nat} (hP : VPts d n p) {T : Table} {N : Nat}
    (hT : Realizes d n p T N) : ∀ e, Realizes d n p (powT n e T) (powK d N e)
  | 0 => real_id hP
  | e + 1 => by
    change Realizes d n p (compT n T (powT n e T)) (powK d N (e + 1))
    rw [powK_succ]
    exact real_comp hT (real_pow hP hT e)

theorem perm_inv {n : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < n)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) :
    ∃ g : Nat → Nat, ∀ i < n, g i < n ∧ f (g i) = i ∧ g (f i) = i := by
  let F : Fin n → Fin n := fun i => ⟨f i.val, hf i.val i.isLt⟩
  have hF : Function.Injective F := fun i j e =>
    Fin.ext (hinj i.val i.isLt j.val j.isLt (congrArg Fin.val e))
  have hb : Function.Bijective F := Finite.injective_iff_bijective.1 hF
  let e := Equiv.ofBijective F hb
  refine ⟨fun i => if h : i < n then (e.symm ⟨i, h⟩).val else 0, fun i hi => ?_⟩
  refine ⟨by simp only [hi, dite_true]; exact (e.symm ⟨i, hi⟩).isLt, ?_, ?_⟩
  · simp only [hi, dite_true]
    have := e.apply_symm_apply ⟨i, hi⟩
    exact congrArg Fin.val this
  · have hfi := hf i hi
    simp only [hfi, dite_true]
    have : e.symm ⟨f i, hfi⟩ = ⟨i, hi⟩ := e.symm_apply_apply ⟨i, hi⟩
    rw [this]

theorem real_inv {d n : Nat} {p : Nat → Nat} (hP : VPts d n p) {T : Table} {N X : Nat}
    (hT : Realizes d n p T N) (hX : ∀ v < 2 ^ d, vmF d X (vmF d N v) = v) :
    Realizes d n p (invT n T) X ∧ invOK n T (invT n T) = true := by
  have hn : n < 2 ^ 32 := by have := hP.n_lt; omega
  have hinj : ∀ i < n, ∀ j < n, ap T i = ap T j → i = j := fun i hi j hj e => by
    apply hP.inj i hi j hj
    rw [← hX _ (hP.lt i hi), ← hX _ (hP.lt j hj), ← (hT.2 i hi).2, ← (hT.2 j hj).2, e]
  obtain ⟨g, hg⟩ := perm_inv (fun i hi => (hT.2 i hi).1) hinj
  have hTR : CFSG.KS.TW.TR n T (ap T) := ⟨hT.1, fun i hi => ⟨rfl, (hT.2 i hi).1⟩⟩
  have hR := CFSG.KS.TW.invT_TR hn hTR hg
  refine ⟨⟨hR.1, fun h hh => ?_⟩, CFSG.KS.TW.invOK_of hTR hR fun i hi => (hg i hi).2.2⟩
  obtain ⟨g1, g2, -⟩ := hg h hh
  rw [(hR.2 h hh).1]
  refine ⟨g1, ?_⟩
  calc p (g h) = vmF d X (vmF d N (p (g h))) := (hX _ (hP.lt _ g1)).symm
    _ = vmF d X (p h) := by rw [← (hT.2 _ g1).2, g2]

private theorem ap_tab {n : Nat} {f : Nat → Nat} (hn : n < 2 ^ 32) (hf : ∀ i < n, f i < n) {i : Nat}
    (hi : i < n) : ap ((List.range n).map fun h => UInt32.ofNat (f h)).toArray i = f i := by
  unfold ap
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by have := hf i hi; omega)

private theorem pts_get {p : Nat → Nat} {m i : Nat} (hi : i < m) :
    ((List.range m).map p).toArray[i]! = p i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem vpts_of {D : VecData} {NA NB : Nat} {P AT BT S IP SP : Nat → Nat}
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) : VPts D.d D.n (lk P 32) := by
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, pw2_eq] at hn
  exact ⟨hn.2, fun h hh => (orbAt_iff.1 (horb h hh)).1, P_inj_of_sort hsort⟩

theorem orbit_real (D : VecData) {csA csB : List Char} {MA MB NA NB : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) :
    Realizes D.d D.n (lk P 32) (D.orbit ()).alpha NA ∧
      Realizes D.d D.n (lk P 32) (D.orbit ()).beta NB := by
  have hO := orbit_eq D hA hB hseed hn hP0 horb hbfs hsort
  have hP := vpts_of hn horb hsort
  have hn32 : D.n < 2 ^ 32 := by have := hP.n_lt; omega
  rw [hO]
  dsimp only
  refine ⟨⟨by simp, fun h hh => ?_⟩, ⟨by simp, fun h hh => ?_⟩⟩
  · obtain ⟨-, h2, -, h4, -⟩ := orbAt_iff.1 (horb h hh)
    rw [ap_tab hn32 (fun j hj => (orbAt_iff.1 (horb j hj)).2.1) hh]
    exact ⟨h2, h4⟩
  · obtain ⟨-, -, h3, -, h5⟩ := orbAt_iff.1 (horb h hh)
    rw [ap_tab hn32 (fun j hj => (orbAt_iff.1 (horb j hj)).2.2.1) hh]
    exact ⟨h3, h5⟩

theorem genT_real (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) (z : Int) :
    Realizes D.d D.n (lk P 32) (genT D.n (D.orbit ()) z) (letN NA NAi NB NBi z) := by
  have hP := vpts_of hn horb hsort
  obtain ⟨ha, hb⟩ := orbit_real D hA hB hseed hn hP0 horb hbfs hsort
  have hai := (real_inv hP ha fun v hv => vmF_inv hAi hv).1
  have hbi := (real_inv hP hb fun v hv => vmF_inv hBi hv).1
  unfold genT
  rcases z with k | k
  · rcases k with _ | _ | _ | k
    · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
      exact hbi
    · rw [ite_eq_left (by decide)]
      exact ha
    · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
      exact hb
    · have e1 : Int.ofNat (k + 3) ≠ 1 := by simp only [Int.ofNat_eq_natCast]; omega
      have e2 : Int.ofNat (k + 3) ≠ -1 := by simp only [Int.ofNat_eq_natCast]; omega
      have e3 : Int.ofNat (k + 3) ≠ 2 := by simp only [Int.ofNat_eq_natCast]; omega
      rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right e3]
      exact hbi
  · rcases k with _ | k
    · rw [ite_eq_right (by decide), ite_eq_left (by decide)]
      exact hai
    · have e1 : Int.negSucc (k + 1) ≠ 1 := by omega
      have e2 : Int.negSucc (k + 1) ≠ -1 := by omega
      have e3 : Int.negSucc (k + 1) ≠ 2 := by omega
      rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right e3]
      exact hbi

private theorem ap_map {A G : Table} {i : Nat} (hi : i < A.size) :
    ap (A.map fun t => G[t.toNat]!) i = ap G (ap A i) := by
  unfold ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, ← getElem!_pos A i hi]

theorem wordT_real' {d n : Nat} {p : Nat → Nat} (hP : VPts d n p) {gens : Int → Table}
    {NA NAi NB NBi : Nat} (hg : ∀ z, Realizes d n p (gens z) (letN NA NAi NB NBi z)) :
    ∀ w, Realizes d n p (wordT n gens w) (wordN d NA NAi NB NBi w)
  | [] => by
    unfold wordT
    exact real_id hP
  | z :: w => by
    have e1 : wordT n gens (z :: w) = (wordT n gens w).map fun t => (gens z)[t.toNat]! := by
      unfold wordT
      rfl
    have e2 : wordN d NA NAi NB NBi (z :: w) = mulF d (wordN d NA NAi NB NBi w) (letN NA NAi NB NBi z) :=
      strictN_eq _ _
    rw [e1, e2]
    have hw := wordT_real' hP hg w
    refine ⟨by simp [hw.1], fun h hh => ?_⟩
    rw [ap_map (by rw [hw.1]; exact hh)]
    obtain ⟨q1, q2⟩ := hw.2 h hh
    obtain ⟨p1, p2⟩ := (hg z).2 _ q1
    exact ⟨p1, by rw [p2, q2, vmF_mulF]⟩

theorem wordT_real (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) (w : List Int) :
    Realizes D.d D.n (lk P 32) (wordT D.n (genT D.n (D.orbit ())) w) (wordN D.d NA NAi NB NBi w) :=
  wordT_real' (vpts_of hn horb hsort)
    (genT_real D hA hB hseed hAi hBi hn hP0 horb hbfs hsort) w

private theorem getL_rep (x : Nat) : ∀ m r : Nat,
    getL x (Nat.rec (motive := fun _ => List Nat) List.nil (fun _ ih => List.cons x ih) m) r = x
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | m + 1, r + 1 => getL_rep x m r

private theorem len_rep (x : Nat) : ∀ m : Nat,
    (Nat.rec (motive := fun _ => List Nat) List.nil (fun _ ih => List.cons x ih) m).length = m
  | 0 => rfl
  | m + 1 => by
    change (List.cons x _).length = m + 1
    rw [List.length_cons, len_rep x m]

private theorem regs0_get (D : VecData) (O : VOrbit) {r : Nat} (hr : r < D.nregs) :
    (regs0 D O)[r]! = if r = 0 then wordT D.n (genT D.n O) D.w0
      else if r = 1 then wordT D.n (genT D.n O) D.w1 else idT D.n := by
  unfold regs0
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]

private noncomputable def runN (d : Nat) (prog : List Instr) (st : List Nat × List Nat × Bool) :
    List Nat × List Nat × Bool :=
  List.rec (motive := fun _ => List Nat × List Nat × Bool → List Nat × List Nat × Bool)
    (fun st => st) (fun ins _ ih st => ih (stepN d ins st)) prog st

private theorem setL_length : ∀ (R : List Nat) (k x : Nat), (setL R k x).length = R.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: R, k + 1, x => by
    change (a :: setL R k x).length = _
    rw [List.length_cons, setL_length R k x, List.length_cons]

private theorem getL_setL (y : Nat) : ∀ (R : List Nat) (k x r : Nat), k < R.length →
    getL y (setL R k x) r = if r = k then x else getL y R r
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, 0, _ => rfl
  | _ :: _, 0, _, _ + 1, _ => rfl
  | _ :: _, _ + 1, _, 0, _ => rfl
  | a :: R, k + 1, x, r + 1, h => by
    change getL y (setL R k x) r = _
    rw [getL_setL y R k x r (by simpa using h)]
    by_cases e : r = k
    · simp [e]
    · have : r + 1 ≠ k + 1 := by omega
      rw [ite_eq_right e, ite_eq_right this]
      rfl

private theorem set!_get {A : Array Table} {k r : Nat} {x : Table} (hk : k < A.size) (hr : r < A.size) :
    (A.set! k x)[r]! = if r = k then x else A[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds]
  by_cases e : r = k
  · subst e
    simp
  · rw [ite_eq_right (Ne.symm e), ite_eq_right e, getElem!_pos A r hr]

private def SInv (d n nr : Nat) (p : Nat → Nat) (s : Array Table × Bool)
    (t : List Nat × List Nat × Bool) : Prop :=
  s.1.size = nr ∧ t.1.length = nr ∧
    (t.2.2 = true → s.2 = true ∧ ∀ r < nr, Realizes d n p s.1[r]! (getL (idF d) t.1 r))

private theorem step_sim {d n nr : Nat} {p : Nat → Nat} (hP : VPts d n p) {ins : Instr}
    (hins : instrLtK nr ins = true) {s : Array Table × Bool} {t : List Nat × List Nat × Bool}
    (H : SInv d n nr p s t) : SInv d n nr p (stepT n s ins) (stepN d ins t) := by
  obtain ⟨Rs, ok⟩ := s
  obtain ⟨Rl, V, okN⟩ := t
  obtain ⟨hs, hl, hr⟩ := H
  dsimp only at hs hl hr
  cases ins with
  | mu i j k =>
    have hik : i < nr ∧ j < nr ∧ k < nr := by
      have h : andB (Nat.blt i nr) (andB (Nat.blt j nr) (Nat.blt k nr)) = true := hins
      simpa only [andB_eq, Bool.and_eq_true, Nat.blt_eq] using h
    change SInv d n nr p (Rs.set! k (compT n Rs[i]! Rs[j]!), ok)
      (setL Rl k (mulF d (getL (idF d) Rl j) (getL (idF d) Rl i)), V, okN)
    refine ⟨by simp [hs], by rw [setL_length, hl], fun hok => ?_⟩
    obtain ⟨hok', hR⟩ := hr hok
    refine ⟨hok', fun r hr' => ?_⟩
    dsimp only
    rw [set!_get (by omega) (by omega), getL_setL _ _ _ _ _ (by omega)]
    by_cases e : r = k
    · rw [ite_eq_left e, ite_eq_left e]
      exact real_comp (hR i hik.1) (hR j hik.2.1)
    · rw [ite_eq_right e, ite_eq_right e]
      exact hR r hr'
  | pwr e i k =>
    have hik : i < nr ∧ k < nr := by
      have h : andB (Nat.blt i nr) (Nat.blt k nr) = true := hins
      simpa only [andB_eq, Bool.and_eq_true, Nat.blt_eq] using h
    change SInv d n nr p (Rs.set! k (powT n e Rs[i]!), ok)
      (setL Rl k (powK d (getL (idF d) Rl i) e), V, okN)
    refine ⟨by simp [hs], by rw [setL_length, hl], fun hok => ?_⟩
    obtain ⟨hok', hR⟩ := hr hok
    refine ⟨hok', fun r hr' => ?_⟩
    dsimp only
    rw [set!_get (by omega) (by omega), getL_setL _ _ _ _ _ (by omega)]
    by_cases e' : r = k
    · rw [ite_eq_left e', ite_eq_left e']
      exact real_pow hP (hR i hik.1) e
    · rw [ite_eq_right e', ite_eq_right e']
      exact hR r hr'
  | iv i k =>
    have hik : i < nr ∧ k < nr := by
      have h : andB (Nat.blt i nr) (Nat.blt k nr) = true := hins
      simpa only [andB_eq, Bool.and_eq_true, Nat.blt_eq] using h
    cases V with
    | nil =>
      change SInv d n nr p (Rs.set! k (invT n Rs[i]!), ok && invOK n Rs[i]! (invT n Rs[i]!))
        (Rl, [], false)
      exact ⟨by simp [hs], hl, fun h => absurd h Bool.false_ne_true⟩
    | cons x V' =>
      change SInv d n nr p (Rs.set! k (invT n Rs[i]!), ok && invOK n Rs[i]! (invT n Rs[i]!))
        (setL Rl k x, V', andB okN (Nat.beq (mulF d (getL (idF d) Rl i) x) (idF d)))
      refine ⟨by simp [hs], by rw [setL_length, hl], fun hok => ?_⟩
      rw [andB_eq, Bool.and_eq_true] at hok
      obtain ⟨hok', hR⟩ := hr hok.1
      obtain ⟨hinv, hiok⟩ := real_inv hP (hR i hik.1) fun v hv => vmF_inv hok.2 hv
      refine ⟨by rw [hok', hiok]; rfl, fun r hr' => ?_⟩
      dsimp only
      rw [set!_get (by omega) (by omega), getL_setL _ _ _ _ _ (by omega)]
      by_cases e : r = k
      · rw [ite_eq_left e, ite_eq_left e]
        exact hinv
      · rw [ite_eq_right e, ite_eq_right e]
        exact hR r hr'

private theorem run_sim {d n nr : Nat} {p : Nat → Nat} (hP : VPts d n p) :
    ∀ (prog : List Instr) (s : Array Table × Bool) (t : List Nat × List Nat × Bool),
      (∀ ins ∈ prog, instrLtK nr ins = true) → SInv d n nr p s t →
      SInv d n nr p (prog.foldl (stepT n) s) (runN d prog t)
  | [], _, _, _, H => H
  | ins :: prog, s, t, hp, H => by
    rw [List.foldl_cons]
    exact run_sim hP prog _ (stepN d ins t) (fun i hi => hp i (List.mem_cons_of_mem ins hi))
      (step_sim hP (hp ins List.mem_cons_self) H)

theorem slp_real (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi : Nat}
    {P AT BT FO S IP SP : Nat → Nat} {R V : List Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hregs : andB (Nat.ble (nat_lit 2) D.nregs) (andB (allL (instrLtK D.nregs) D.prog)
      (allL (fun s => Nat.blt s D.nregs) D.sel.toList)) = true)
    (hslp : slpOK D.d D.prog (regs0N D.d D.nregs (wordN D.d NA NAi NB NBi D.w0)
      (wordN D.d NA NAi NB NBi D.w1)) V R = true) :
    (runSLP D.n D.prog (regs0 D (D.orbit ()))).2 = true ∧
      (runSLP D.n D.prog (regs0 D (D.orbit ()))).1.size = D.nregs ∧
      ∀ r < D.nregs, Realizes D.d D.n (lk P 32) (runSLP D.n D.prog (regs0 D (D.orbit ()))).1[r]!
        (getL (idF D.d) R r) := by
  have hP := vpts_of hn horb hsort
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, allL_iff] at hregs
  obtain ⟨hnr', hprog, -⟩ := hregs
  have hnr : 2 ≤ D.nregs := hnr'
  have hW := wordT_real D hA hB hseed hAi hBi hn hP0 horb hbfs hsort
  have H0 : SInv D.d D.n D.nregs (lk P 32) (regs0 D (D.orbit ()), true)
      (regs0N D.d D.nregs (wordN D.d NA NAi NB NBi D.w0) (wordN D.d NA NAi NB NBi D.w1), V, true) := by
    refine ⟨by simp [regs0], ?_, fun _ => ⟨rfl, fun r hr => ?_⟩⟩
    · change (List.cons _ (List.cons _ _)).length = _
      rw [List.length_cons, List.length_cons, len_rep]
      have e : Nat.sub D.nregs (nat_lit 2) = D.nregs - 2 := rfl
      rw [e]
      omega
    · dsimp only
      rw [regs0_get D _ hr]
      rcases r with _ | _ | r
      · exact hW D.w0
      · exact hW D.w1
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        change Realizes _ _ _ _ (getL (idF D.d) (Nat.rec (motive := fun _ => List Nat) List.nil
          (fun _ ih => List.cons (idF D.d) ih) (Nat.sub D.nregs 2)) r)
        rw [getL_rep]
        exact real_id hP
  have Hf := run_sim hP D.prog _ _ hprog H0
  change Prod.rec (motive := fun _ => Bool) (fun R' rest => Prod.rec (motive := fun _ => Bool)
    (fun _ ok => andB ok (eqL R' R)) rest) (runN D.d D.prog _) = true at hslp
  generalize runN D.d D.prog _ = F at hslp Hf
  obtain ⟨Rf, Vf, okf⟩ := F
  have hs : andB okf (eqL Rf R) = true := hslp
  rw [andB_eq, Bool.and_eq_true] at hs
  obtain ⟨hs1, -, hs3⟩ := Hf
  obtain ⟨hok, hR⟩ := hs3 hs.1
  rw [eqL_sound Rf R hs.2] at hR
  exact ⟨hok, hs1, hR⟩

private theorem instrLt_of {r : Nat} : ∀ ins : Instr, instrLtK r ins = true → instrLt r ins = true
  | .mu i j k, h => by
    have h' : andB (Nat.blt i r) (andB (Nat.blt j r) (Nat.blt k r)) = true := h
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    simp [instrLt, h']
  | .pwr e i k, h => by
    have h' : andB (Nat.blt i r) (Nat.blt k r) = true := h
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    simp [instrLt, h']
  | .iv i k, h => by
    have h' : andB (Nat.blt i r) (Nat.blt k r) = true := h
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    simp [instrLt, h']

theorem slpChecks_ok (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi : Nat}
    {P AT BT FO S IP SP : Nat → Nat} {R V : List Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hregs : andB (Nat.ble (nat_lit 2) D.nregs) (andB (allL (instrLtK D.nregs) D.prog)
      (allL (fun s => Nat.blt s D.nregs) D.sel.toList)) = true)
    (hslp : slpOK D.d D.prog (regs0N D.d D.nregs (wordN D.d NA NAi NB NBi D.w0)
      (wordN D.d NA NAi NB NBi D.w1)) V R = true) :
    (decide (2 ≤ D.nregs) && D.prog.all (instrLt D.nregs) &&
      (runSLP D.n D.prog (regs0 D (D.orbit ()))).2 && D.sel.all (· < D.nregs)) = true := by
  have hok := (slp_real D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hslp).1
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, allL_iff, allL_iff] at hregs
  obtain ⟨hnr, hprog, hsel⟩ := hregs
  simp only [Bool.and_eq_true, decide_eq_true_eq, hok, and_true]
  refine ⟨⟨hnr, List.all_eq_true.2 fun ins hins => instrLt_of ins (hprog ins hins)⟩, ?_⟩
  rw [Array.all_eq_true]
  intro i hi
  have := hsel D.sel[i] (by simp)
  simpa using this

private noncomputable def letRec (d : Nat) (R LM : List Nat) (sel : List Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih j => strictB (getL (nat_lit 0) LM (Nat.mul (nat_lit 2) j)) fun x =>
      andB (Nat.beq x (getL (idF d) R s))
        (andB (Nat.beq (mulF d x (getL (nat_lit 0) LM (Nat.succ (Nat.mul (nat_lit 2) j)))) (idF d))
          (ih (Nat.succ j)))) sel j

private theorem letRec_spec {d : Nat} {R LM : List Nat} : ∀ (sel : List Nat) (j : Nat),
    letRec d R LM sel j = true → ∀ t (ht : t < sel.length),
      getL 0 LM (2 * (j + t)) = getL (idF d) R sel[t] ∧
        Nat.beq (mulF d (getL 0 LM (2 * (j + t))) (getL 0 LM (2 * (j + t) + 1))) (idF d) = true
  | [], _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | s :: sel, j, h, t, ht => by
    have h' : strictB (getL (nat_lit 0) LM (Nat.mul (nat_lit 2) j)) (fun x =>
      andB (Nat.beq x (getL (idF d) R s))
        (andB (Nat.beq (mulF d x (getL (nat_lit 0) LM (Nat.succ (Nat.mul (nat_lit 2) j)))) (idF d))
          (letRec d R LM sel (Nat.succ j)))) = true := h
    rw [strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    rcases t with _ | t
    · exact ⟨Nat.eq_of_beq_eq_true h1, h2⟩
    · have := letRec_spec sel (j + 1) h3 t (by simpa using ht)
      have e : j + 1 + t = j + (t + 1) := by omega
      rw [e] at this
      exact this

private theorem lettersOf_get (n : Nat) (sel : Array Nat) (Rs : Array Table) {l : Nat}
    (hl : l < 2 * sel.size) : (lettersOf n sel Rs)[l]! =
      if l % 2 = 0 then Rs[sel[l / 2]!]! else invT n Rs[sel[l / 2]!]! := by
  unfold lettersOf
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]

theorem letters_real (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi kL : Nat}
    {P AT BT FO S IP SP : Nat → Nat} {R V LM : List Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hregs : andB (Nat.ble (nat_lit 2) D.nregs) (andB (allL (instrLtK D.nregs) D.prog)
      (allL (fun s => Nat.blt s D.nregs) D.sel.toList)) = true)
    (hslp : slpOK D.d D.prog (regs0N D.d D.nregs (wordN D.d NA NAi NB NBi D.w0)
      (wordN D.d NA NAi NB NBi D.w1)) V R = true)
    (hkL : Nat.beq kL (Nat.mul (nat_lit 2) D.sel.size) = true)
    (hlet : lettersK D.d R D.sel.toList LM = true) :
    (lettersOf D.n D.sel (runSLP D.n D.prog (regs0 D (D.orbit ()))).1).size = kL ∧
      ∀ l < kL, Realizes D.d D.n (lk P 32)
        (lettersOf D.n D.sel (runSLP D.n D.prog (regs0 D (D.orbit ()))).1)[l]! (getL 0 LM l) := by
  have hP := vpts_of hn horb hsort
  obtain ⟨-, hsz, hR⟩ := slp_real D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hslp
  have hk : kL = 2 * D.sel.size := Nat.eq_of_beq_eq_true hkL
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, allL_iff] at hregs
  have hsel := (allL_iff _).1 hregs.2.2
  have hlet' : andB (Nat.beq (lenL LM) (Nat.mul 2 (lenL D.sel.toList)))
      (letRec D.d R LM D.sel.toList 0) = true := hlet
  rw [andB_eq, Bool.and_eq_true] at hlet'
  have hspec := letRec_spec D.sel.toList 0 hlet'.2
  generalize (runSLP D.n D.prog (regs0 D (D.orbit ()))).1 = Rs at hsz hR
  refine ⟨by simp [lettersOf, hk], fun l hl => ?_⟩
  rw [lettersOf_get _ _ _ (by omega)]
  have hj : l / 2 < D.sel.size := by omega
  have hjl : l / 2 < D.sel.toList.length := by simpa using hj
  have hs : D.sel[l / 2]! = D.sel.toList[l / 2] := by
    rw [getElem!_pos D.sel _ hj, Array.getElem_toList]
  have hslt : D.sel[l / 2]! < D.nregs := by
    rw [hs]
    have := hsel _ (List.getElem_mem hjl)
    simpa using this
  obtain ⟨e1, e2⟩ := hspec (l / 2) hjl
  rw [Nat.zero_add] at e1 e2
  have hX := hR _ hslt
  rw [hs, ← e1] at hX
  by_cases hp : l % 2 = 0
  · rw [ite_eq_left hp]
    have e : 2 * (l / 2) = l := by omega
    rw [e] at hX
    rw [hs]
    exact hX
  · rw [ite_eq_right hp, hs]
    have e : 2 * (l / 2) + 1 = l := by omega
    rw [e] at e2
    exact (real_inv hP hX fun v hv => vmF_inv e2 hv).1

theorem letAt_iff {d n N : Nat} {P T : Nat → Nat} {h : Nat} :
    letAt d n N P T h = true ↔ lk T 32 h < n ∧ lk P 32 (lk T 32 h) = vmF d N (lk P 32 h) := by
  unfold letAt
  simp only [strictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]

theorem letters_eq (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi kL : Nat}
    {P AT BT FO S IP SP : Nat → Nat} {R V LM : List Nat} {LT : Nat → Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hregs : andB (Nat.ble (nat_lit 2) D.nregs) (andB (allL (instrLtK D.nregs) D.prog)
      (allL (fun s => Nat.blt s D.nregs) D.sel.toList)) = true)
    (hslp : slpOK D.d D.prog (regs0N D.d D.nregs (wordN D.d NA NAi NB NBi D.w0)
      (wordN D.d NA NAi NB NBi D.w1)) V R = true)
    (hkL : Nat.beq kL (Nat.mul (nat_lit 2) D.sel.size) = true)
    (hlet : lettersK D.d R D.sel.toList LM = true)
    (hLT : ∀ j < kL, ∀ h < D.n, letAt D.d D.n (getL (nat_lit 0) LM j) P (LT j) h = true) :
    (lettersOf D.n D.sel (runSLP D.n D.prog (regs0 D (D.orbit ()))).1).size = kL ∧
      ∀ l < kL, (lettersOf D.n D.sel (runSLP D.n D.prog (regs0 D (D.orbit ()))).1)[l]!.size = D.n ∧
        ∀ x < D.n, ap (lettersOf D.n D.sel (runSLP D.n D.prog (regs0 D (D.orbit ()))).1)[l]! x =
          lk (LT l) 32 x := by
  have hP := vpts_of hn horb hsort
  obtain ⟨hs, hL⟩ := letters_real D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hslp hkL hlet
  refine ⟨hs, fun l hl => ⟨(hL l hl).1, fun x hx => ?_⟩⟩
  exact (hL l hl).ap_eq hP (fun h hh => letAt_iff.1 (hLT l hl h hh)) x hx

private theorem fix_eq {d n : Nat} {P : Nat → Nat} (hP : VPts d n (lk P 32)) {Q : Array Nat}
    (hQ : ∀ t < Q.size, Q[t]! < n) {T : Table} {M : Nat} (hT : Realizes d n (lk P 32) T M) :
    tupleEq (apT T Q) Q = fixQ d M Q.size P (getL 0 Q.toList) := by
  apply Bool.eq_iff_iff.2
  rw [CFSG.KS.TW.tupleEq_iff, CFSG.KS.TW.apT_map, Array.size_map]
  unfold fixQ
  rw [allN_iff]
  simp only [strictB_eq, Nat.beq_eq, true_and]
  refine forall_congr' fun t => forall_congr' fun ht => ?_
  rw [getL_array Q ht, getElem!_pos _ t (by simpa using ht), Array.getElem_map,
    ← getElem!_pos Q t ht]
  have hq := hQ t ht
  obtain ⟨h1, h2⟩ := hT.2 _ hq
  constructor
  · intro e
    rw [← h2, e]
  · intro e
    exact hP.inj _ h1 _ hq (by rw [h2, e])

private theorem ord_of {d n : Nat} {P : Nat → Nat} (hP : VPts d n (lk P 32)) {Q : Array Nat}
    (hQ : ∀ t < Q.size, Q[t]! < n) {T : Table} {M : Nat} (hT : Realizes d n (lk P 32) T M)
    (pe : Nat × Nat) (h : ordK d M Q.size P (getL 0 Q.toList) pe.1 pe.2 = true) :
    ordOK n Q T pe = true := by
  unfold ordK at h
  rw [andB_eq, andB_eq, notB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold ordOK
  rw [fix_eq hP hQ (real_pow hP hT _), fix_eq hP hQ (real_pow hP hT _)]
  have h2' : fixQ d (powK d M (pe.1 ^ pe.2)) Q.size P (getL 0 Q.toList) = true := h2
  have h3' : fixQ d (powK d M (pe.1 ^ (pe.2 - 1))) Q.size P (getL 0 Q.toList) = false := h3
  rw [h2', h3']
  simp [h1]

theorem ordChecks_ok (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hregs : andB (Nat.ble (nat_lit 2) D.nregs) (andB (allL (instrLtK D.nregs) D.prog)
      (allL (fun s => Nat.blt s D.nregs) D.sel.toList)) = true)
    (hchain : andB (Nat.beq D.base.size D.orbSizes.length) (andB (Nat.beq D.qb.size D.base.size)
      (andB (allL (fun s => Nat.blt (nat_lit 0) s) D.orbSizes)
      (andB (allN D.basis.size fun t => Nat.blt (getL (nat_lit 0) D.basis.toList t) D.n)
      (allN D.base.size fun i => strictB (getL (nat_lit 0) D.qb.toList i) fun x =>
        andB (Nat.blt x D.basis.size)
          (Nat.beq (getL (nat_lit 0) D.basis.toList x) (getL (nat_lit 0) D.base.toList i)))))) = true)
    (hord : andB (ordK D.d (wordN D.d NA NAi NB NBi D.w0) D.basis.size P (getL (nat_lit 0) D.basis.toList)
        D.ord0.1 D.ord0.2)
      (andB (ordK D.d (wordN D.d NA NAi NB NBi D.w1) D.basis.size P (getL (nat_lit 0) D.basis.toList)
        D.ord1.1 D.ord1.2)
      (ordK D.d (mulF D.d (wordN D.d NA NAi NB NBi D.w1) (wordN D.d NA NAi NB NBi D.w0)) D.basis.size P
        (getL (nat_lit 0) D.basis.toList) D.ord01.1 D.ord01.2)) = true) :
    ordChecks D (regs0 D (D.orbit ())) = true := by
  have hP := vpts_of hn horb hsort
  have hW := wordT_real D hA hB hseed hAi hBi hn hP0 horb hbfs hsort
  rw [andB_eq, Bool.and_eq_true, Nat.ble_eq] at hregs
  have hnr : 2 ≤ D.nregs := hregs.1
  rw [andB_eq, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hchain
  have hQ : ∀ t < D.basis.size, D.basis[t]! < D.n := fun t ht => by
    have := allN_iff.1 hchain.2.2.2.1 t ht
    rw [Nat.blt_eq, getL_array _ ht] at this
    exact this
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hord
  obtain ⟨o0, o1, o01⟩ := hord
  have r0 : (regs0 D (D.orbit ()))[0]! = wordT D.n (genT D.n (D.orbit ())) D.w0 := by
    rw [regs0_get D (r := 0) _ (by omega), ite_eq_left rfl]
  have r1 : (regs0 D (D.orbit ()))[1]! = wordT D.n (genT D.n (D.orbit ())) D.w1 := by
    rw [regs0_get D (r := 1) _ (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  unfold ordChecks
  rw [r0, r1, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨ord_of hP hQ (hW D.w0) D.ord0 o0, ord_of hP hQ (hW D.w1) D.ord1 o1⟩,
    ord_of hP hQ (real_comp (hW D.w0) (hW D.w1)) D.ord01 o01⟩

theorem baseFacts (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi BI BM : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hchain : andB (Nat.beq D.base.size D.orbSizes.length) (andB (Nat.beq D.qb.size D.base.size)
      (andB (allL (fun s => Nat.blt (nat_lit 0) s) D.orbSizes)
      (andB (allN D.basis.size fun t => Nat.blt (getL (nat_lit 0) D.basis.toList t) D.n)
      (allN D.base.size fun i => strictB (getL (nat_lit 0) D.qb.toList i) fun x =>
        andB (Nat.blt x D.basis.size)
          (Nat.beq (getL (nat_lit 0) D.basis.toList x) (getL (nat_lit 0) D.base.toList i)))))) = true)
    (hbasis : andB (Nat.beq D.basis.size D.d) (andB (packB D.d D.basisInv.toList BI)
      (basisK D.d BI BM P (getL (nat_lit 0) D.basis.toList))) = true) :
    CFSG.Sporadic.SmallF2.BaseFacts D := by
  have hP := vpts_of hn horb hsort
  have hO := orbit_eq D hA hB hseed hn hP0 horb hbfs hsort
  have hok := orbit_ok D hA hB hseed hn hP0 horb hbfs hsort
  obtain ⟨ha, hb⟩ := orbit_real D hA hB hseed hn hP0 horb hbfs hsort
  have hs := hseed
  unfold seedK at hs
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hs
  obtain ⟨hd0, hd64, heA, heB, hbA, hbB, -, -, hpA, hpB⟩ := hs
  rw [andB_eq, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hchain
  have hQ : ∀ t < D.basis.size, D.basis[t]! < D.n := fun t ht => by
    have := allN_iff.1 hchain.2.2.2.1 t ht
    rw [Nat.blt_eq, getL_array _ ht] at this
    exact this
  unfold basisK at hbasis
  rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Nat.beq_eq, allN_iff] at hbasis
  obtain ⟨hbs, hpk, hrow, hmul⟩ := hbasis
  have hinv : D.basisInv = unpackR D.d BI := by
    rw [← packB_sound hpk, Array.toArray_toList]
  have hmat : (D.basis.map fun i => (D.orbit ()).pts[i]!) = unpackR D.d BM := by
    rw [hO]
    dsimp only
    apply Array.ext (by simp [unpackR, hbs])
    intro i h1 _
    have hi : i < D.basis.size := by simpa using h1
    have hrw := Nat.eq_of_beq_eq_true (hrow i (by omega))
    rw [Array.getElem_map, ← getElem!_pos D.basis i hi, pts_get (hQ i hi), ← getL_array _ hi, ← hrw]
    simp only [unpackR, Array.getElem_ofFn]
    rw [← CFSG.KC.F2W.rowF_eq]
    rfl
  refine ⟨hd0, hd64, heA, heB, ?_, ?_, hok, hP.n_lt, ?_, ?_, hbs, hQ, ?_⟩
  · change powRows D.d (rowsOfPayload D.d D.seedA) D.expA = _
    rw [hA, bind_sound hbA, powRows_unpackR, hpA, unpackR_idF]
  · change powRows D.d (rowsOfPayload D.d D.seedB) D.expB = _
    rw [hB, bind_sound hbB, powRows_unpackR, hpB, unpackR_idF]
  · exact (real_inv hP ha fun v hv => vmF_inv hAi hv).2
  · exact (real_inv hP hb fun v hv => vmF_inv hBi hv).2
  · change mulRows D.d D.basisInv (D.basis.map fun i => (D.orbit ()).pts[i]!) = _
    rw [hinv, hmat, CFSG.KC.F2W.mulRows_unpackR, Nat.eq_of_beq_eq_true hmul, unpackR_idF]

theorem baseChecks_ok (D : VecData) {csA csB : List Char} {MA MB NA NB NAi NBi BI BM : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hchain : andB (Nat.beq D.base.size D.orbSizes.length) (andB (Nat.beq D.qb.size D.base.size)
      (andB (allL (fun s => Nat.blt (nat_lit 0) s) D.orbSizes)
      (andB (allN D.basis.size fun t => Nat.blt (getL (nat_lit 0) D.basis.toList t) D.n)
      (allN D.base.size fun i => strictB (getL (nat_lit 0) D.qb.toList i) fun x =>
        andB (Nat.blt x D.basis.size)
          (Nat.beq (getL (nat_lit 0) D.basis.toList x) (getL (nat_lit 0) D.base.toList i)))))) = true)
    (hbasis : andB (Nat.beq D.basis.size D.d) (andB (packB D.d D.basisInv.toList BI)
      (basisK D.d BI BM P (getL (nat_lit 0) D.basis.toList))) = true) :
    baseChecks D (D.orbit ()) = true := by
  have F := baseFacts D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hchain hbasis
  unfold baseChecks
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨F.d_pos, F.d_lt⟩, F.expA_pos⟩, F.expB_pos⟩, F.powA⟩, F.powB⟩, F.orbit⟩, F.n_lt⟩,
    F.invA⟩, F.invB⟩, F.basis_size⟩, ?_⟩, F.basis_inv⟩
  rw [Array.all_eq_true]
  intro i hi
  have := F.basis_lt i hi
  rw [getElem!_pos D.basis i hi] at this
  simpa using this

end CFSG.KC.VecK

end
