module

public import CFSG.Certificates.Kernel.Th.S.BigS

public section

open CFSG.KC.Th CFSG.KC.Th.BigS

local notation "ℕ" => Nat

namespace CFSG.KC.Th.Spec.SylowPc

private theorem pcStrictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem pc_andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

private theorem pc_boolRec_ne_zero {a v : ℕ} {g : Bool} (ha : a = 0)
    (h : Bool.rec (motive := fun _ => ℕ) a v g ≠ 0) : g = true := by
  cases g with
  | false => exact absurd ha h
  | true => rfl

private theorem pc_land (S : ℕ) : Nat.land (S - 1) 255 = (S - 1) % 256 :=
  Nat.and_two_pow_sub_one_eq_mod (S - 1) 8

private theorem pc_shr (S : ℕ) : Nat.shiftRight (S - 1) 8 = (S - 1) / 256 :=
  Nat.shiftRight_eq_div_pow (S - 1) 8

private theorem pc_shl (x : ℕ) : Nat.shiftLeft x 8 = 256 * x := by
  change x <<< 8 = 256 * x
  rw [Nat.shiftLeft_eq]
  exact Nat.mul_comm x 256

private theorem pc_beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

private theorem pc_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact (h (by simpa using hb)).elim

private theorem pc_blt_true {a b : ℕ} (h : a < b) : Nat.blt a b = true := by
  simpa using h

private theorem pc_blt_false {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b with
  | false => rfl
  | true => exact (h (by simpa using hb)).elim

private noncomputable def pcGuard (RB PW : ℕ → ℕ) (c rm ONE PR n p pb : ℕ) (S x : ℕ) : Bool :=
  andB (Nat.blt 0 S) (andB (Nat.blt (Nat.land (S - 1) 255) n)
    (andB (Nat.blt (Nat.shiftRight (S - 1) 8) n)
      (pcRelOK RB PW c rm ONE PR n p pb (Nat.land (S - 1) 255) (Nat.shiftRight (S - 1) 8) x)))

private noncomputable def pcRaw (RB PW : ℕ → ℕ) (c rm ONE PR n p pb : ℕ) (S x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0
    (Bool.rec (motive := fun _ => ℕ) (S + 256)
      (Bool.rec (motive := fun _ => ℕ) (1 + n)
        (1 + (Nat.succ (Nat.land (S - 1) 255) + Nat.shiftLeft (Nat.succ (Nat.land (S - 1) 255)) 8))
        (Nat.blt (Nat.succ (Nat.land (S - 1) 255)) n))
      (Nat.beq (Nat.succ (Nat.shiftRight (S - 1) 8)) n))
    (pcGuard RB PW c rm ONE PR n p pb S x)

private noncomputable def pcInner (RB PW : ℕ → ℕ) (c rm ONE PR n p pb : ℕ) :
    ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih J S => CFSG.KC.Loop.strictN
      (pcRaw RB PW c rm ONE PR n p pb S (bitsN J 0 (Nat.mul n pb)))
      (ih (Nat.shiftRight J (Nat.mul n pb))))

private theorem pcInner_succ (RB PW : ℕ → ℕ) (c rm ONE PR n p pb k J S : ℕ) :
    pcInner RB PW c rm ONE PR n p pb (k + 1) J S =
      pcInner RB PW c rm ONE PR n p pb k (Nat.shiftRight J (Nat.mul n pb))
        (pcRaw RB PW c rm ONE PR n p pb S (bitsN J 0 (Nat.mul n pb))) := by
  have e : pcInner RB PW c rm ONE PR n p pb (k + 1) J S =
      CFSG.KC.Loop.strictN (pcRaw RB PW c rm ONE PR n p pb S (bitsN J 0 (Nat.mul n pb)))
        (pcInner RB PW c rm ONE PR n p pb k (Nat.shiftRight J (Nat.mul n pb))) := rfl
  rw [e, pcStrictN_eq]

private noncomputable def pcInstrs (w : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, J => bitsN J 0 w :: pcInstrs w k (Nat.shiftRight J w)

private theorem pcInner_eq (RB PW : ℕ → ℕ) (c rm ONE PR n p pb : ℕ) :
    ∀ k J S : ℕ, pcInner RB PW c rm ONE PR n p pb k J S =
      (pcInstrs (Nat.mul n pb) k J).foldl (pcRaw RB PW c rm ONE PR n p pb) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    rw [pcInner_succ, pcInner_eq RB PW c rm ONE PR n p pb k, pcInstrs, List.foldl_cons]

private noncomputable def pcProg (w : ℕ) : List ℕ → List ℕ
  | [] => []
  | C :: Cs => pcInstrs w (Nat.land C 255) (Nat.shiftRight C 8) ++ pcProg w Cs

private theorem pcRunPc_cons (RB PW : ℕ → ℕ) (c rm ONE PR n p pb C : ℕ) (Cs : List ℕ)
    (S : ℕ) :
    runPc RB PW c rm ONE PR n p pb (C :: Cs) S =
      runPc RB PW c rm ONE PR n p pb Cs
        (pcInner RB PW c rm ONE PR n p pb (Nat.land C 255) (Nat.shiftRight C 8) S) := by
  have e : runPc RB PW c rm ONE PR n p pb (C :: Cs) S =
      CFSG.KC.Loop.strictN
        (pcInner RB PW c rm ONE PR n p pb (Nat.land C 255) (Nat.shiftRight C 8) S)
        (runPc RB PW c rm ONE PR n p pb Cs) := rfl
  rw [e, pcStrictN_eq]

private theorem pcRunPc_eq (RB PW : ℕ → ℕ) (c rm ONE PR n p pb : ℕ) :
    ∀ (Cs : List ℕ) (S : ℕ), runPc RB PW c rm ONE PR n p pb Cs S =
      (pcProg (Nat.mul n pb) Cs).foldl (pcRaw RB PW c rm ONE PR n p pb) S
  | [], _ => rfl
  | C :: Cs, S => by
    rw [pcRunPc_cons, pcRunPc_eq RB PW c rm ONE PR n p pb Cs, pcInner_eq, pcProg,
      List.foldl_append]

private abbrev pcInv (RB PW : ℕ → ℕ) (c rm ONE PR n p pb : ℕ) (S : ℕ) : Prop :=
  S ≠ 0 ∧ ∀ i j : ℕ, i ≤ j → j < n →
    ((S - 1) % 256 < i ∨ ((S - 1) % 256 = i ∧ (S - 1) / 256 ≤ j)) →
    ∃ x, pcRelOK RB PW c rm ONE PR n p pb i j x = true

private theorem pcGuard_iff (RB PW : ℕ → ℕ) (c rm ONE PR n p pb S x : ℕ) :
    pcGuard RB PW c rm ONE PR n p pb S x = true ↔
      (0 < S ∧ (S - 1) % 256 < n ∧ (S - 1) / 256 < n ∧
        pcRelOK RB PW c rm ONE PR n p pb ((S - 1) % 256) ((S - 1) / 256) x = true) := by
  unfold pcGuard
  simp only [pc_andB_eq_true, Nat.blt_eq, pc_land, pc_shr]

private theorem pc_ne_zero {RB PW : ℕ → ℕ} {c rm ONE PR n p pb S x : ℕ}
    (h : pcRaw RB PW c rm ONE PR n p pb S x ≠ 0) :
    pcGuard RB PW c rm ONE PR n p pb S x = true := by
  unfold pcRaw at h
  exact pc_boolRec_ne_zero rfl h

private theorem pcRaw_v1 {RB PW : ℕ → ℕ} {c rm ONE PR n p pb S x : ℕ} (h0 : 0 < S)
    (ha : (S - 1) % 256 < n) (hb : (S - 1) / 256 < n)
    (hr : pcRelOK RB PW c rm ONE PR n p pb ((S - 1) % 256) ((S - 1) / 256) x = true)
    (hbn : (S - 1) / 256 + 1 ≠ n) :
    pcRaw RB PW c rm ONE PR n p pb S x = S + 256 := by
  have hg := (pcGuard_iff RB PW c rm ONE PR n p pb S x).2 ⟨h0, ha, hb, hr⟩
  have hbe : Nat.beq (Nat.succ (Nat.shiftRight (S - 1) 8)) n = false :=
    pc_beq_false (by rw [pc_shr]; omega)
  unfold pcRaw
  rw [hg, hbe]

private theorem pcRaw_v2 {RB PW : ℕ → ℕ} {c rm ONE PR n p pb S x : ℕ} (h0 : 0 < S)
    (ha : (S - 1) % 256 < n) (hb : (S - 1) / 256 < n)
    (hr : pcRelOK RB PW c rm ONE PR n p pb ((S - 1) % 256) ((S - 1) / 256) x = true)
    (hbn : (S - 1) / 256 + 1 = n) (hab : ¬ (S - 1) % 256 + 1 < n) :
    pcRaw RB PW c rm ONE PR n p pb S x = 1 + n := by
  have hg := (pcGuard_iff RB PW c rm ONE PR n p pb S x).2 ⟨h0, ha, hb, hr⟩
  have hbe : Nat.beq (Nat.succ (Nat.shiftRight (S - 1) 8)) n = true :=
    pc_beq_true (by rw [pc_shr]; omega)
  have hlt : Nat.blt (Nat.succ (Nat.land (S - 1) 255)) n = false :=
    pc_blt_false (by rw [pc_land]; omega)
  unfold pcRaw
  rw [hg, hbe, hlt]

private theorem pcRaw_v3 {RB PW : ℕ → ℕ} {c rm ONE PR n p pb S x : ℕ} (h0 : 0 < S)
    (ha : (S - 1) % 256 < n) (hb : (S - 1) / 256 < n)
    (hr : pcRelOK RB PW c rm ONE PR n p pb ((S - 1) % 256) ((S - 1) / 256) x = true)
    (hbn : (S - 1) / 256 + 1 = n) (hab : (S - 1) % 256 + 1 < n) :
    pcRaw RB PW c rm ONE PR n p pb S x =
      1 + ((S - 1) % 256 + 1) + 256 * ((S - 1) % 256 + 1) := by
  have hg := (pcGuard_iff RB PW c rm ONE PR n p pb S x).2 ⟨h0, ha, hb, hr⟩
  have hbe : Nat.beq (Nat.succ (Nat.shiftRight (S - 1) 8)) n = true :=
    pc_beq_true (by rw [pc_shr]; omega)
  have hlt : Nat.blt (Nat.succ (Nat.land (S - 1) 255)) n = true :=
    pc_blt_true (by rw [pc_land]; omega)
  unfold pcRaw
  rw [hg, hbe, hlt]
  show 1 + (Nat.succ (Nat.land (S - 1) 255) + Nat.shiftLeft (Nat.succ (Nat.land (S - 1) 255)) 8) = _
  rw [pc_land, pc_shl]
  omega

private theorem pc_inv_of_foldl (RB PW : ℕ → ℕ) (c rm ONE PR n p pb : ℕ) (hn : n < 256) :
    ∀ (L : List ℕ) (S : ℕ), L.foldl (pcRaw RB PW c rm ONE PR n p pb) S = n + 1 →
      pcInv RB PW c rm ONE PR n p pb S
  | [], S, h => by
    have hS : S = n + 1 := h
    subst hS
    refine ⟨by omega, fun i j hij hj hp => ?_⟩
    exfalso
    omega
  | e :: L, S, h => by
    have h' : L.foldl (pcRaw RB PW c rm ONE PR n p pb)
        (pcRaw RB PW c rm ONE PR n p pb S e) = n + 1 := by
      rw [List.foldl_cons] at h
      exact h
    obtain ⟨hS0, hS⟩ := pc_inv_of_foldl RB PW c rm ONE PR n p pb hn L _ h'
    obtain ⟨h0, ha, hb, hr⟩ := (pcGuard_iff RB PW c rm ONE PR n p pb S e).1 (pc_ne_zero hS0)
    refine ⟨by omega, fun i j hij hj hp => ?_⟩
    by_cases hbn : (S - 1) / 256 + 1 = n
    · by_cases hab : (S - 1) % 256 + 1 < n
      · rw [pcRaw_v3 h0 ha hb hr hbn hab] at hS
        by_cases hpair : (S - 1) % 256 = i ∧ (S - 1) / 256 = j
        · obtain ⟨e1, e2⟩ := hpair
          subst e1
          subst e2
          exact ⟨_, hr⟩
        · apply hS i j hij hj
          omega
      · by_cases hpair : (S - 1) % 256 = i ∧ (S - 1) / 256 = j
        · obtain ⟨e1, e2⟩ := hpair
          subst e1
          subst e2
          exact ⟨_, hr⟩
        · exfalso
          omega
    · rw [pcRaw_v1 h0 ha hb hr hbn] at hS
      by_cases hpair : (S - 1) % 256 = i ∧ (S - 1) / 256 = j
      · obtain ⟨e1, e2⟩ := hpair
        subst e1
        subst e2
        exact ⟨_, hr⟩
      · apply hS i j hij hj
        omega

theorem runPc_pairs {RB PW : ℕ → ℕ} {c rm ONE PR n p pb : ℕ} {Cs : List ℕ} (hn : n < 256)
    (h : runPc RB PW c rm ONE PR n p pb Cs 1 = n + 1) :
    ∀ i j, i ≤ j → j < n → ∃ x, pcRelOK RB PW c rm ONE PR n p pb i j x = true := by
  rw [pcRunPc_eq] at h
  obtain ⟨_, hI⟩ := pc_inv_of_foldl RB PW c rm ONE PR n p pb hn _ 1 h
  intro i j hij hj
  exact hI i j hij hj (by omega)

end CFSG.KC.Th.Spec.SylowPc

end
