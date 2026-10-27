module

public import Certificates.Data.Kernel.Spor.Fi24Orb
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound

public section

namespace CFSG.KC.Fi24OrbS

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb

@[expose] def ForP (FD S : ℕ → ℕ) (TG : ℕ → ℕ → ℕ) (n s0 r1 r : ℕ) : Prop :=
  (fComp (FD r) = 1 ∨ (fComp (FD r) = 2 ∧ fPos (FD r) < 31671 ∧ S (fPos (FD r)) = r)) ∧
  ((fDep (FD r) = 0 ∧ ((r = s0 ∧ fComp (FD r) = 2) ∨ (r = r1 ∧ fComp (FD r) = 1))) ∨
    (1 ≤ fPar (FD r) ∧ fPar (FD r) < n ∧ fDep (FD (fPar (FD r))) + 1 = fDep (FD r) ∧
      fComp (FD (fPar (FD r))) = fComp (FD r) ∧ fLab (FD r) < 10 ∧ fLab (FD r) ≠ 8 ∧
      tk TG (fLab (FD r)) (fPar (FD r)) = r))

@[expose] def BindP (OL NM NI VT : ℕ → ℕ) (TG : ℕ → ℕ → ℕ) (AW : List ℕ) (n k : ℕ) : Prop :=
  NM k < n ∧ NI (NM k) = k ∧
  oA (OL k) < n ∧ oA (OL (oA (OL k))) = k ∧ NM (oA (OL k)) = walk TG AW (NM k) ∧
  oB (OL k) < n ∧ oB (OL (oB (OL (oB (OL k))))) = k ∧ NM (oB (OL k)) = vt7 VT (NM k) ∧
  (k = 0 ∨ (oPar (OL k) < k ∧ ((oLab (OL k) = 1 ∧ oA (OL (oPar (OL k))) = k) ∨
    (oLab (OL k) = 2 ∧ oB (OL (oPar (OL k))) = k))))

private theorem andB_t {a b : Bool} :
    CFSG.KC.Fi24Orb.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [CFSG.KC.Fi24Orb.andB]

private theorem orB_t {a b : Bool} :
    CFSG.KC.Fi24Orb.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [CFSG.KC.Fi24Orb.orB]

private theorem letB_t (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by
  cases v <;> rfl

private theorem brec_t {α : Sort*} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = if c = true then b else a := by
  cases c <;> rfl

private theorem h0L_t {k : ℕ} : h0L k = true ↔ k < 10 ∧ k ≠ 8 := by
  unfold h0L
  simp only [andB_t, Nat.blt_eq, brec_t, Nat.beq_eq]
  by_cases h : k = 8 <;> simp [h]

theorem forOK_spec {FD S : ℕ → ℕ} {TG : ℕ → ℕ → ℕ} {n s0 r1 lo : ℕ}
    (h : forOK FD S TG n s0 r1 lo = true) :
    ∀ t < 1024, 1 ≤ lo + t → lo + t < n → ForP FD S TG n s0 r1 (lo + t) := by
  intro t ht h1 hn
  have h2 := Fi24FixS.allBelow_spec h (by decide) t ht
  have e : Nat.add lo t = lo + t := rfl
  unfold ForP
  simp only [letB_t, e, brec_t, andB_t, Nat.ble_eq, Nat.blt_eq, if_pos (And.intro h1 hn)] at h2
  unfold forStep at h2
  simp only [letB_t, andB_t, orB_t, brec_t, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq, h0L_t] at h2
  refine ⟨h2.1, ?_⟩
  by_cases hd : fDep (FD (lo + t)) = 0
  · rw [if_pos hd] at h2
    simp only [orB_t, andB_t, Nat.beq_eq] at h2
    exact Or.inl ⟨hd, h2.2⟩
  · rw [if_neg hd] at h2
    simp only [andB_t, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq, h0L_t] at h2
    obtain ⟨a, b, c, d, ⟨e1, e2⟩, f⟩ := h2.2
    exact Or.inr ⟨a, b, c, d, e1, e2, f⟩

theorem inSOK_spec {FD S : ℕ → ℕ} {m lo : ℕ} (h : inSOK FD S m lo = true) :
    ∀ t < 4096, lo + t < m → fComp (FD (S (lo + t))) = 2 := by
  intro t ht hm
  have h2 := Fi24FixS.allBelow_spec h (by decide) t ht
  have e : Nat.add lo t = lo + t := rfl
  simp only [letB_t, e, brec_t, Nat.blt_eq, if_pos hm, Nat.beq_eq] at h2
  exact h2

theorem vtOK_spec {VT : ℕ → ℕ} {TG : ℕ → ℕ → ℕ} {VW : List ℕ} {n lo : ℕ}
    (h : vtOK VT TG VW n lo = true) : ∀ t < 512, lo + t < n → walk TG VW (lo + t) = VT (lo + t) := by
  intro t ht hm
  have h2 := Fi24FixS.allBelow_spec h (by decide) t ht
  have e : Nat.add lo t = lo + t := rfl
  simp only [letB_t, e, brec_t, Nat.blt_eq, if_pos hm, Nat.beq_eq] at h2
  exact h2

theorem bindOK_spec {OL NM NI VT : ℕ → ℕ} {TG : ℕ → ℕ → ℕ} {AW : List ℕ} {n lo : ℕ}
    (h : bindOK OL NM NI VT TG AW n lo = true) :
    ∀ t < 512, lo + t < n → BindP OL NM NI VT TG AW n (lo + t) := by
  intro t ht hm
  have h2 := Fi24FixS.allBelow_spec h (by decide) t ht
  have e : Nat.add lo t = lo + t := rfl
  simp only [letB_t, e, brec_t, Nat.blt_eq, if_pos hm] at h2
  unfold bindStep treeStep at h2
  simp only [letB_t, andB_t, orB_t, Nat.blt_eq, Nat.beq_eq] at h2
  unfold BindP
  obtain ⟨a1, a2, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩, d⟩ := h2
  refine ⟨a1, a2, b1, b2, b3, c1, c2, c3, ?_⟩
  rcases d with d | ⟨d1, d2⟩
  · exact Or.inl d
  · refine Or.inr ⟨d1, ?_⟩
    rcases d2 with ⟨d3, d4⟩ | ⟨d3, d4⟩
    · exact Or.inl ⟨d3, d4⟩
    · exact Or.inr ⟨d3, d4⟩

private theorem testBit_row253 (P o j : ℕ) (hj : j < 253) :
    (Nat.land (Nat.shiftRight P o) M253).testBit j = P.testBit (o + j) := by
  have e : M253 = 2 ^ 253 - 1 := by
    change 1 <<< 253 - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  change ((P >>> o) &&& M253).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, e, Nat.testBit_two_pow_sub_one]
  simp [hj]

theorem agreeOK_spec {Y C : ℕ} (h : agreeOK Y C = true) : ∀ i < 253, ∀ j < 253,
    Y.testBit (781 * i + j) = C.testBit (253 * i + j) ∧
      Y.testBit (609961 + (781 * i + j)) = C.testBit (64009 + (253 * i + j)) := by
  intro i hi j hj
  have h2 := Fi24FixS.allBelow_spec h (by decide) i hi
  unfold agreeRow at h2
  rw [andB_t, Nat.beq_eq, Nat.beq_eq] at h2
  have e1 := congrArg (fun x => x.testBit j) h2.1
  have e2 := congrArg (fun x => x.testBit j) h2.2
  simp only [testBit_row253 _ _ _ hj] at e1 e2
  have f1 : Nat.add 609961 (Nat.mul 781 i) + j = 609961 + (781 * i + j) := by
    change 609961 + 781 * i + j = _
    omega
  have f2 : Nat.add 64009 (Nat.mul 253 i) + j = 64009 + (253 * i + j) := by
    change 64009 + 253 * i + j = _
    omega
  rw [f1, f2] at e2
  exact ⟨e1, e2⟩

theorem slpOK_spec {mul : ℕ → ℕ → ℕ} {vld : ℕ → Bool} {RS IJ : ℕ → ℕ} {n lo : ℕ}
    (h : slpOK mul vld RS IJ n lo = true) : ∀ t < 16, lo + t < n →
      vld (RS (lo + t)) = true ∧
        (2 ≤ lo + t → ∃ i < lo + t, ∃ j < lo + t, mul (RS i) (RS j) = RS (lo + t)) := by
  intro t ht hm
  have h2 := Fi24FixS.allBelow_spec h (by decide) t ht
  have e : Nat.add lo t = lo + t := rfl
  simp only [letB_t, e, brec_t, Nat.blt_eq, if_pos hm] at h2
  unfold slpStep at h2
  simp only [andB_t, orB_t, letB_t, Nat.blt_eq, Nat.beq_eq] at h2
  refine ⟨h2.1, fun h2le => ?_⟩
  rcases h2.2 with h3 | ⟨hi, hj, hm⟩
  · omega
  · exact ⟨_, hi, _, hj, hm⟩

theorem strictN_eqO (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem vt7_eq (VT : ℕ → ℕ) (r : ℕ) : vt7 VT r = VT (VT (VT (VT (VT (VT (VT r)))))) := by
  simp only [vt7, strictN_eqO]

end CFSG.KC.Fi24OrbS

end
