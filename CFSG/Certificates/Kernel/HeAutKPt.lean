module

public import CFSG.Certificates.Kernel.HeAutKSound
import CFSG.Certificates.Kernel.HeAutKLoops
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.BfsPin
open CFSG.KLie.CT (anyN andB orB notB)

@[expose] noncomputable def allPtH (k : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) k

@[expose] noncomputable def commPtH (n w a b : Nat) : Bool :=
  strictB a fun a => strictB b fun b => allPtH n fun p =>
    Nat.beq (pg w (mask w) a (pg w (mask w) b p)) (pg w (mask w) b (pg w (mask w) a p))

@[expose] noncomputable def commZPt (n w z a b : Nat) : Bool :=
  strictB a fun a => strictB b fun b =>
    orB (allPtH n fun p =>
        Nat.beq (pg w (mask w) a (pg w (mask w) b p)) (pg w (mask w) b (pg w (mask w) a p)))
      (allPtH n fun p => Nat.beq (pg w (mask w) a (pg w (mask w) b p))
        (pg w (mask w) b (pg w (mask w) a (pg w (mask w) z p))))

@[expose] noncomputable def filterRH (N : Nat) (p : Nat → Bool) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc)) (p r)) N []

@[expose] noncomputable def setYPt (n w N : Nat) (T : Nat → Nat) (FZ z x : Nat) : List Nat :=
  filterRH N fun r => andB (bitK FZ r) (commZPt n w z x (T r))

@[expose] noncomputable def goodQPt (n w N : Nat) (T : Nat → Nat) (FZ z x : Nat) : Bool :=
  strictB (setYPt n w N T FZ z x).length fun c => orB (Nat.blt c (nat_lit 128))
    (andB (Nat.beq c (nat_lit 128)) ((setYPt n w N T FZ z x).any fun a =>
      (setYPt n w N T FZ z x).any fun b => notB (commZ n w z (T a) (T b))))

@[expose] noncomputable def uqAtPt (n w NX : Nat) (TX : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (FZ z i : Nat) : Bool :=
  andB (bitK FZ i) (strictB (TX i) fun x =>
    andB (notB (inL NQ TQ x)) (notB (goodQPt n w NX TX FZ z x)))

@[expose] noncomputable def ueAtPt (n w NX : Nat) (TX : Nat → Nat) (NE : Nat) (TE : Nat → Nat)
    (NF : Nat) (TF : Nat → Nat) (F1 i : Nat) : Bool :=
  orB (notB (bitK F1 i)) (strictB (TX i) fun x => orB (Nat.beq x (pidn n w))
    (orB (inL NE TE x) (orB (inL NF TF x)
      (Nat.blt (cntR (fun j => andB (bitK F1 j) (commPtH n w x (TX j))) (nat_lit 0) NX)
        (nat_lit 64)))))

theorem strictB_self (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem allPtH_iff (k : Nat) (f : Nat → Bool) : allPtH k f = true ↔ ∀ p < k, f p = true := by
  induction k with
  | zero => exact ⟨fun _ p hp => absurd hp (Nat.not_lt_zero p), fun _ => rfl⟩
  | succ i ih =>
    change Bool.rec (motive := fun _ => Bool) false (allPtH i f) (f i) = true ↔ _
    cases hf : f i
    · exact ⟨fun h => absurd h Bool.false_ne_true,
        fun h => absurd (h i (Nat.lt_succ_self i)) (by simp [hf])⟩
    · refine ⟨fun h p hp => ?_, fun h => ih.2 fun p hp => h p (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact ih.1 h p hp
      · exact hf

theorem beq_iff_pts {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    Nat.beq p q = true ↔ ∀ i < n, pg w (mask w) p i = pg w (mask w) q i := by
  rw [Nat.beq_eq]
  refine ⟨fun h i _ => by rw [h], fun h => ?_⟩
  obtain ⟨-, hw, hp0, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq0, -⟩ := CFSG.KS.PF.canon_facts hq
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp0 hq0 h

theorem commPtH_eq {n w a b : Nat} (ha : canonK n w (mask w) (n * w) a = true)
    (hb : canonK n w (mask w) (n * w) b = true) : commPtH n w a b = HexaK.comm n w a b := by
  have hn := (CFSG.KS.PF.canon_facts ha).1
  unfold commPtH HexaK.comm
  simp only [strictB_self, mul]
  rw [Bool.eq_iff_iff, allPtH_iff, beq_iff_pts (canonK_pcomp ha hb) (canonK_pcomp hb ha)]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [Nat.beq_eq, CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pcomp (by omega) hi]

theorem commZPt_eq {n w z a b : Nat} (hz : canonK n w (mask w) (n * w) z = true)
    (ha : canonK n w (mask w) (n * w) a = true)
    (hb : canonK n w (mask w) (n * w) b = true) : commZPt n w z a b = commZ n w z a b := by
  obtain ⟨hn, -, -, hzl⟩ := CFSG.KS.PF.canon_facts hz
  unfold commZPt commZ
  simp only [strictB_self]
  have e1 : (allPtH n fun p => Nat.beq (pg w (mask w) a (pg w (mask w) b p))
      (pg w (mask w) b (pg w (mask w) a p))) = Nat.beq (mul n w a b) (mul n w b a) := by
    simp only [mul]
    rw [Bool.eq_iff_iff, allPtH_iff, beq_iff_pts (canonK_pcomp ha hb) (canonK_pcomp hb ha)]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [Nat.beq_eq, CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pcomp (by omega) hi]
  have e2 : (allPtH n fun p => Nat.beq (pg w (mask w) a (pg w (mask w) b p))
      (pg w (mask w) b (pg w (mask w) a (pg w (mask w) z p)))) =
      Nat.beq (mul n w a b) (mul n w (mul n w b a) z) := by
    simp only [mul]
    rw [Bool.eq_iff_iff, allPtH_iff, beq_iff_pts (canonK_pcomp ha hb) (canonK_pcomp (canonK_pcomp hb ha) hz)]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [Nat.beq_eq, CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pcomp (by omega) hi,
      CFSG.KS.PF.pg_pcomp (by omega) (hzl i hi)]
  rw [e1, e2]

theorem filterRH_congr {N : Nat} {p q : Nat → Bool} (h : ∀ r < N, p r = q r) :
    filterRH N p = filterRH N q := by
  suffices H : ∀ M, M ≤ N → ∀ acc : List Nat,
      Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
        (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc)) (p r)) M acc =
      Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
        (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc)) (q r)) M acc
    from H N (Nat.le_refl N) []
  intro M
  induction M with
  | zero => exact fun _ _ => rfl
  | succ r ih =>
    intro hM acc
    change Bool.rec (motive := fun _ => List Nat) _ _ (p r) = Bool.rec (motive := fun _ => List Nat) _ _ (q r)
    rw [h r (by omega), ih (by omega), ih (by omega)]

theorem cntR_congrH {f g : Nat → Bool} {lo : Nat} : ∀ {len : Nat},
    (∀ k < len, f (lo + k) = g (lo + k)) → cntR f lo len = cntR g lo len
  | 0, _ => rfl
  | len + 1, h => by
    rw [cntR_succ, cntR_succ, h len (Nat.lt_succ_self len),
      cntR_congrH (f := f) (g := g) (lo := lo) (len := len) fun k hk => h k (Nat.lt_succ_of_lt hk)]

theorem cntR_congrH0 {f g : Nat → Bool} {len : Nat} (h : ∀ k < len, f k = g k) :
    cntR f 0 len = cntR g 0 len :=
  cntR_congrH fun k hk => by
    rw [Nat.zero_add]
    exact h k hk

theorem allR_congr0 {f g : Nat → Bool} {len : Nat} (h : ∀ k < len, f k = g k) :
    allR f 0 len = allR g 0 len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    change andB (allR f 0 len) (f (0 + len)) = andB (allR g 0 len) (g (0 + len))
    rw [ih fun k hk => h k (by omega), Nat.zero_add, h len (Nat.lt_succ_self len)]

theorem uqAtPt_eq {n w NX NQ FZ z i : Nat} {TX TQ : Nat → Nat} (hX : ∀ j < NX, PP n w (TX j))
    (hz : PP n w z) (hi : i < NX) :
    uqAtPt n w NX TX NQ TQ FZ z i = uqAt n w NX TX NQ TQ FZ z i := by
  have hY : setYPt n w NX TX FZ z (TX i) = setYK n w NX TX FZ z (TX i) :=
    filterRH_congr (p := fun r => andB (bitK FZ r) (commZPt n w z (TX i) (TX r)))
      (q := fun r => andB (bitK FZ r) (commZ n w z (TX i) (TX r)))
      fun r hr => by simp only [commZPt_eq hz.1 (hX i hi).1 (hX r hr).1]
  unfold uqAtPt uqAt
  simp only [strictB_self]
  unfold goodQPt goodQK
  rw [hY]

theorem ueAtPt_eq {n w NX NE NF F1 i : Nat} {TX TE TF : Nat → Nat} (hX : ∀ j < NX, PP n w (TX j))
    (hi : i < NX) : ueAtPt n w NX TX NE TE NF TF F1 i = ueAt n w NX TX NE TE NF TF F1 i := by
  have hc : cntR (fun j => andB (bitK F1 j) (commPtH n w (TX i) (TX j))) 0 NX =
      cntR (fun j => andB (bitK F1 j) (HexaK.comm n w (TX i) (TX j))) 0 NX :=
    cntR_congrH0 fun k hk => by simp only [commPtH_eq (hX i hi).1 (hX k hk).1]
  unfold ueAtPt ueAt
  simp only [strictB_self]
  rw [hc]

end CFSG.KC.HeAutK

end
