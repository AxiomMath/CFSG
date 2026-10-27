module

public import CFSG.Certificates.Kernel.VecKAssemble

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem allN_spec {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    obtain ⟨h1, h2⟩ := andB_true h
    intro i hi
    rcases Nat.lt_or_ge i n with hl | hl
    · exact ih h2 i hl
    · have : i = n := by omega
      subst this
      exact h1

theorem allS_cover {S ns n : Nat} {f : Nat → Bool}
    (hS : ∀ s < ns, allS (Nat.mul s S) (sliceN n S s) f = true)
    (hn : n ≤ ns * S) : ∀ h < n, f h = true := by
  intro h hh
  have hS0 : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · subst h0; omega
    · exact h0
  have hs : h / S < ns := by
    rw [Nat.div_lt_iff_lt_mul hS0]
    omega
  have hlen : h % S < sliceN n S (h / S) := by
    have hd := Nat.div_add_mod h S
    have hm := Nat.mod_lt h hS0
    unfold sliceN
    cases hb : Nat.ble (Nat.mul (Nat.succ (h / S)) S) n
    · simp only [Nat.sub_eq, Nat.mul_eq]
      have hd' : h / S * S + h % S = h := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod h S
      omega
    · exact hm
  have := allN_spec (hS (h / S) hs) (h % S) hlen
  have e : Nat.add (Nat.mul (h / S) S) (h % S) = h := by
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod h S
  rwa [e] at this

theorem vecK_sound (D : VecData) (c : Nat) {csA csB : List Char}
    {MA MB NA NB NAi NBi BI BM kL : Nat} {P AT BT FO S IP SP : Nat → Nat} {R V LM : List Nat}
    {LT Ot IX Op Ol : Nat → Nat → Nat} {STs SPs SLs : List (Nat → Nat)} {LB PS : Nat → Nat}
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
    (hkL32 : Nat.blt kL (pw2 (nat_lit 32)) = true)
    (hlet : lettersK D.d R D.sel.toList LM = true)
    (hLT : ∀ j < kL, ∀ h < D.n, letAt D.d D.n (getL (nat_lit 0) LM j) P (LT j) h = true)
    (hchain : andB (Nat.beq D.base.size D.orbSizes.length) (andB (Nat.beq D.qb.size D.base.size)
      (andB (allL (fun s => Nat.blt (nat_lit 0) s) D.orbSizes)
      (andB (allN D.basis.size fun t => Nat.blt (getL (nat_lit 0) D.basis.toList t) D.n)
      (allN D.base.size fun i => strictB (getL (nat_lit 0) D.qb.toList i) fun x =>
        andB (Nat.blt x D.basis.size)
          (Nat.beq (getL (nat_lit 0) D.basis.toList x) (getL (nat_lit 0) D.base.toList i)))))) = true)
    (htree : ∀ i < D.base.size, ∀ t < getL (nat_lit 0) D.orbSizes i,
      treeAt D.n kL (getL (nat_lit 0) D.orbSizes i) i (getL (nat_lit 0) D.base.toList i) LT
        (getL (nat_lit 0) D.base.toList) (Ot i) (IX i) (Op i) (Ol i) t = true)
    (hsub0 : andB (Nat.blt (nat_lit 0) D.base.size) (andB (Nat.beq (getL (nat_lit 0) D.base.toList 0) 0)
      (andB (Nat.blt (nat_lit 0) D.subReps.size) (andB (Nat.beq (getL (nat_lit 0) D.subReps.toList 0) 0)
      (andB (Nat.beq D.subSizes.length D.subReps.size)
        (allL (fun s => Nat.blt (nat_lit 0) s) D.subSizes))))) = true)
    (hsub : ∀ j < D.subReps.size, ∀ t < getL (nat_lit 0) D.subSizes j,
      subAt D.n kL (getL (nat_lit 0) D.subSizes j) j (getL (nat_lit 0) D.subReps.toList j) LT
        (getL (nat_lit 0) D.base.toList) (getF STs j) LB PS (getF SPs j) (getF SLs j) t = true)
    (hlab : ∀ p < D.n, labAt D.subReps.size D.subSizes STs LB PS p = true)
    (hord : andB (ordK D.d (wordN D.d NA NAi NB NBi D.w0) D.basis.size P (getL (nat_lit 0) D.basis.toList)
        D.ord0.1 D.ord0.2)
      (andB (ordK D.d (wordN D.d NA NAi NB NBi D.w1) D.basis.size P (getL (nat_lit 0) D.basis.toList)
        D.ord1.1 D.ord1.2)
      (ordK D.d (mulF D.d (wordN D.d NA NAi NB NBi D.w1) (wordN D.d NA NAi NB NBi D.w0)) D.basis.size P
        (getL (nat_lit 0) D.basis.toList) D.ord01.1 D.ord01.2)) = true)
    (hbasis : andB (Nat.beq D.basis.size D.d) (andB (packB D.d D.basisInv.toList BI)
      (basisK D.d BI BM P (getL (nat_lit 0) D.basis.toList))) = true)
    (hcard : Nat.card (J D) ≤ D.orbSizes.prod) :
    vecCert D c = true :=
  vecCert_of_kernel D c hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hslp hkL hkL32 hlet hLT hchain
    htree hsub0 hsub hlab hord hbasis hcard

end CFSG.KC.VecK

end
