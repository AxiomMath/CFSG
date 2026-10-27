module

public import CFSG.Permutation.FinPackPow

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6PermK

open Equiv CFSG.Permutation.FinPack

theorem hn5 : (5 : ℕ) ≤ 16 := by norm_num

@[expose] def impB (b y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true y b

@[expose] def andK (b y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y b

@[expose] def orK (b y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true b

theorem impT {b y : Bool} (h : impB b y = true) (hb : b = true) : y = true := by
  subst hb
  exact h

theorem andE {b y : Bool} (h : andK b y = true) : b = true ∧ y = true := by
  cases b
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem orF {b y : Bool} (h : orK b y = true) (hb : b = false) : y = true := by
  subst hb
  exact h

@[expose] noncomputable def swK (i j : ℕ) : ℕ :=
  encF (fun k => Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) k i (Nat.beq k j))
    j (Nat.beq k i)) 5

@[expose] noncomputable def concA (s r a : ℕ) : Bool :=
  impB (Nat.beq (mulK 5 a s) (mulK 5 s a))
    (andK (Nat.beq (powK 5 274960 (mulK 5 (mulK 5 (mulK 5 a r) (invPK 5 a)) (invPK 5 r)) 3) 274960)
      (impB (Nat.beq (mulK 5 a r) (mulK 5 r a))
        (andK (Nat.beq (powK 5 274960 a 12) 274960)
          (impB (Nat.beq (powK 5 274960 a 4) 274960)
            (orK (Nat.beq a 274960) (Nat.beq a s))))))

@[expose] noncomputable def QA (s r : ℕ) : Bool :=
  impB (Nat.beq (powK 5 274960 r 3) 274960)
    (orK (Nat.beq r 274960)
      (impB (Nat.beq (mulK 5 r s) (mulK 5 s r)) (walkK 5 (concA s r) 5 0 0 0)))

@[expose] noncomputable def rowA (i j : ℕ) : Bool :=
  orK (Nat.beq i j) (walkK 5 (QA (swK i j)) 5 0 0 0)

@[expose] noncomputable def colA (i : ℕ) : Bool := allLtK (rowA i) 5

theorem checkA : allLtK colA 5 = true := by decide +kernel

@[expose] noncomputable def cmK (c p : ℕ) : Bool := Nat.beq (mulK 5 p c) (mulK 5 c p)

@[expose] noncomputable def QC (c : ℕ) : Bool :=
  impB (Nat.beq (powK 5 274960 c 3) 274960)
    (orK (Nat.beq c 274960) (Nat.beq (cntK 5 (cmK c) 5 0 0 0) 6))

theorem checkC : walkK 5 QC 5 0 0 0 = true := by decide +kernel

@[expose] noncomputable def QQ (c p q : ℕ) : Bool :=
  impB (cmK c q) (Nat.beq (mulK 5 p q) (mulK 5 q p))

@[expose] noncomputable def QP (c p : ℕ) : Bool := impB (cmK c p) (walkK 5 (QQ c p) 5 0 0 0)

@[expose] noncomputable def QD (c : ℕ) : Bool :=
  impB (Nat.beq (powK 5 274960 c 3) 274960)
    (orK (Nat.beq c 274960) (walkK 5 (QP c) 5 0 0 0))

theorem checkD : walkK 5 QD 5 0 0 0 = true := by decide +kernel

theorem hE : enc (1 : Perm (Fin 5)) = 274960 := by decide +kernel

theorem beq1 (σ : Perm (Fin 5)) : Nat.beq (enc σ) 274960 = true ↔ σ = 1 := by
  rw [← hE]
  exact beq_enc_iff hn5

theorem ne1 {σ : Perm (Fin 5)} (h : σ ≠ 1) : Nat.beq (enc σ) 274960 = false := by
  rw [← hE]
  exact beq_enc_false hn5 h

theorem pw_enc (σ : Perm (Fin 5)) (k : ℕ) : powK 5 274960 (enc σ) k = enc (σ ^ k) :=
  (enc_pow hn5 hE σ k).symm

theorem mul_enc (σ τ : Perm (Fin 5)) : mulK 5 (enc σ) (enc τ) = enc (σ * τ) :=
  (enc_mul hn5 σ τ).symm

theorem inv_enc (σ : Perm (Fin 5)) : invPK 5 (enc σ) = enc σ⁻¹ :=
  (enc_inv hn5 σ).symm

theorem powE {σ : Perm (Fin 5)} {k : ℕ} (h : σ ^ k = 1) :
    Nat.beq (powK 5 274960 (enc σ) k) 274960 = true := by
  rw [pw_enc, h, hE]
  try exact Nat.beq_refl _

theorem swK_eq (i j : Fin 5) : swK i j = enc (Equiv.swap i j) := by
  unfold swK enc
  refine encF_congr fun k hk => ?_
  try dsimp only
  rw [dif_pos hk, Equiv.swap_apply_def]
  by_cases h1 : (⟨k, hk⟩ : Fin 5) = i
  · have e1 : Nat.beq k i = true := by
      rw [Nat.beq_eq]
      exact congrArg Fin.val h1
    rw [if_pos h1, e1]
    try rfl
  · have e1 : Nat.beq k i = false :=
      Bool.eq_false_iff.2 fun e => h1 (Fin.ext (Nat.eq_of_beq_eq_true e))
    rw [if_neg h1, e1]
    by_cases h2 : (⟨k, hk⟩ : Fin 5) = j
    · have e2 : Nat.beq k j = true := by
        rw [Nat.beq_eq]
        exact congrArg Fin.val h2
      rw [if_pos h2, e2]
      try rfl
    · have e2 : Nat.beq k j = false :=
        Bool.eq_false_iff.2 fun e => h2 (Fin.ext (Nat.eq_of_beq_eq_true e))
      rw [if_neg h2, e2]
      try rfl

theorem factA (i j : Fin 5) (hij : i ≠ j) (ρ a : Perm (Fin 5)) (h3 : ρ ^ 3 = 1) (h1 : ρ ≠ 1)
    (hc : ρ * Equiv.swap i j = Equiv.swap i j * ρ) (ha : a * Equiv.swap i j = Equiv.swap i j * a) :
    (a * ρ * a⁻¹ * ρ⁻¹) ^ 3 = 1 ∧ (a * ρ = ρ * a → a ^ 12 = 1 ∧
      (a ^ 4 = 1 → a = 1 ∨ a = Equiv.swap i j)) := by
  have Hi : allLtK (rowA i) 5 = true := allLtK_iff.1 checkA i i.isLt
  have Hj : rowA i j = true := allLtK_iff.1 Hi j j.isLt
  have hb : Nat.beq (i : ℕ) (j : ℕ) = false :=
    Bool.eq_false_iff.2 fun e => hij (Fin.ext (Nat.eq_of_beq_eq_true e))
  unfold rowA at Hj
  have Hw := orF Hj hb
  rw [swK_eq] at Hw
  have H2 := walkK_sound Hw ρ
  unfold QA at H2
  have H3 := impT (orF (impT H2 (powE h3)) (ne1 h1)) ((comm_enc_iff hn5).2 hc)
  have H4 := walkK_sound H3 a
  unfold concA at H4
  obtain ⟨hx, H5⟩ := andE (impT H4 ((comm_enc_iff hn5).2 ha))
  rw [inv_enc, inv_enc, mul_enc, mul_enc, mul_enc, pw_enc, beq1] at hx
  refine ⟨hx, fun har => ?_⟩
  obtain ⟨h12, H6⟩ := andE (impT H5 ((comm_enc_iff hn5).2 har))
  rw [pw_enc, beq1] at h12
  refine ⟨h12, fun h4 => ?_⟩
  have H7 := impT H6 (powE h4)
  cases h0 : Nat.beq (enc a) 274960
  · exact Or.inr ((beq_enc_iff hn5).1 (orF H7 h0))
  · exact Or.inl ((beq1 a).1 h0)

theorem cent3_card (c : Perm (Fin 5)) (h3 : c ^ 3 = 1) (h1 : c ≠ 1) :
    (Finset.univ.filter (fun p : Perm (Fin 5) => p * c = c * p)).card = 6 := by
  have H : QC (enc c) = true := walkK_sound checkC c
  unfold QC at H
  have H2 := orF (impT H (powE h3)) (ne1 h1)
  rw [← card_filter_eq_cntK] at H2
  rw [Finset.filter_congr (q := fun p : Perm (Fin 5) => cmK (enc c) (enc p) = true)
    (fun p _ => (comm_enc_iff hn5).symm)]
  exact Nat.eq_of_beq_eq_true H2

theorem cent3_comm (c : Perm (Fin 5)) (h3 : c ^ 3 = 1) (h1 : c ≠ 1) (p q : Perm (Fin 5))
    (hp : p * c = c * p) (hq : q * c = c * q) : p * q = q * p := by
  have H : QD (enc c) = true := walkK_sound checkD c
  unfold QD at H
  have Hp := walkK_sound (orF (impT H (powE h3)) (ne1 h1)) p
  unfold QP at Hp
  have Hq := walkK_sound (impT Hp ((comm_enc_iff hn5).2 hp)) q
  unfold QQ at Hq
  exact (comm_enc_iff hn5).1 (impT Hq ((comm_enc_iff hn5).2 hq))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6PermK
