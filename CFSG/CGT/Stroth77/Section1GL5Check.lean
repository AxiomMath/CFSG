module

public import Certificates.Data.CFSGNative.Stroth15.GL5
import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.CGT.Stroth77.GL5

theorem r0_lt (c : Nat) : r0 c < 32 := Nat.mod_lt _ (by decide)
theorem r1_lt (c : Nat) : r1 c < 32 := Nat.mod_lt _ (by decide)
theorem r2_lt (c : Nat) : r2 c < 32 := Nat.mod_lt _ (by decide)
theorem r3_lt (c : Nat) : r3 c < 32 := Nat.mod_lt _ (by decide)
theorem r4_lt (c : Nat) : r4 c < 32 := Nat.mod_lt _ (by decide)

section Rows

variable {a b c d e : Nat} (ha : a < 32) (hb : b < 32) (hc : c < 32) (hd : d < 32) (he : e < 32)
include ha hb hc hd he

theorem r0_ofRows : r0 (ofRows a b c d e) = a := by unfold r0 ofRows; omega
theorem r1_ofRows : r1 (ofRows a b c d e) = b := by unfold r1 ofRows; omega
theorem r2_ofRows : r2 (ofRows a b c d e) = c := by unfold r2 ofRows; omega
theorem r3_ofRows : r3 (ofRows a b c d e) = d := by unfold r3 ofRows; omega
theorem r4_ofRows : r4 (ofRows a b c d e) = e := by unfold r4 ofRows; omega
theorem ofRows_lt : ofRows a b c d e < N := by unfold ofRows N; omega

end Rows

theorem ofRows_rows {c : Nat} (hc : c < N) : ofRows (r0 c) (r1 c) (r2 c) (r3 c) (r4 c) = c := by
  unfold ofRows r0 r1 r2 r3 r4
  unfold N at hc
  omega

theorem code_ext {c c' : Nat} (hc : c < N) (hc' : c' < N) (h0 : r0 c = r0 c') (h1 : r1 c = r1 c')
    (h2 : r2 c = r2 c') (h3 : r3 c = r3 c') (h4 : r4 c = r4 c') : c = c' := by
  rw [← ofRows_rows hc, ← ofRows_rows hc', h0, h1, h2, h3, h4]

theorem ite_lt_32 (p : Prop) [Decidable p] {m : Nat} (hm : m < 32) : (if p then m else 0) < 32 := by
  split <;> omega

theorem xor_lt_32 {m n : Nat} (hm : m < 32) (hn : n < 32) : m ^^^ n < 32 :=
  Nat.xor_lt_two_pow (n := 5) hm hn

theorem vm5_lt (v : Nat) {m0 m1 m2 m3 m4 : Nat} (h0 : m0 < 32) (h1 : m1 < 32) (h2 : m2 < 32)
    (h3 : m3 < 32) (h4 : m4 < 32) : vm5 v m0 m1 m2 m3 m4 < 32 := by
  unfold vm5
  exact xor_lt_32 (xor_lt_32 (xor_lt_32 (xor_lt_32 (ite_lt_32 _ h0) (ite_lt_32 _ h1))
    (ite_lt_32 _ h2)) (ite_lt_32 _ h3)) (ite_lt_32 _ h4)

theorem vm_lt (v c : Nat) : vm v c < 32 :=
  vm5_lt v (r0_lt c) (r1_lt c) (r2_lt c) (r3_lt c) (r4_lt c)

theorem mulC_eq (a b : Nat) : mulC a b = ofRows (vm (r0 b) a) (vm (r1 b) a) (vm (r2 b) a)
    (vm (r3 b) a) (vm (r4 b) a) := rfl

theorem mulC_lt (a b : Nat) : mulC a b < N := by
  rw [mulC_eq]
  exact ofRows_lt (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _)

theorem r0_mulC (a b : Nat) : r0 (mulC a b) = vm (r0 b) a := by
  rw [mulC_eq]; exact r0_ofRows (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _)
theorem r1_mulC (a b : Nat) : r1 (mulC a b) = vm (r1 b) a := by
  rw [mulC_eq]; exact r1_ofRows (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _)
theorem r2_mulC (a b : Nat) : r2 (mulC a b) = vm (r2 b) a := by
  rw [mulC_eq]; exact r2_ofRows (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _)
theorem r3_mulC (a b : Nat) : r3 (mulC a b) = vm (r3 b) a := by
  rw [mulC_eq]; exact r3_ofRows (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _)
theorem r4_mulC (a b : Nat) : r4 (mulC a b) = vm (r4 b) a := by
  rw [mulC_eq]; exact r4_ofRows (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _) (vm_lt _ _)

theorem powC_lt (h : Nat) : ∀ k, powC h k < N
  | 0 => by unfold powC idC N; omega
  | k + 1 => mulC_lt _ _

theorem span5_iff (a b c d e : Nat) :
    span5 a b c d e = true ↔ ∀ v, 0 < v → v < 32 → vm5 v a b c d e ≠ 0 := by
  constructor
  · intro h v hv0 hv32
    simp only [span5, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    interval_cases v <;> simp [vm5, Nat.testBit] <;> tauto
  · intro h
    have k : ∀ v, 0 < v → v < 32 → vm5 v a b c d e ≠ 0 := h
    simp only [span5, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
      ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
      ?_⟩, ?_⟩
    · simpa [vm5, Nat.testBit] using k 1 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 2 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 3 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 4 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 5 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 6 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 7 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 8 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 9 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 10 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 11 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 12 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 13 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 14 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 15 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 16 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 17 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 18 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 19 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 20 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 21 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 22 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 23 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 24 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 25 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 26 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 27 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 28 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 29 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 30 (by omega) (by omega)
    · simpa [vm5, Nat.testBit] using k 31 (by omega) (by omega)

theorem nonsing_iff (c : Nat) : nonsing c = true ↔ ∀ v, 0 < v → v < 32 → vm v c ≠ 0 :=
  span5_iff _ _ _ _ _

inductive Wd where
  | gen (i : Nat)
  | var
  | mul (a b : Wd)
  | pow (a : Wd) (k : Nat)

@[expose] def Wd.evalC (g : Nat) : Wd → Nat
  | .gen i => genC i
  | .var => g
  | .mul a b => mulC (a.evalC g) (b.evalC g)
  | .pow a k => powC (a.evalC g) k

@[expose] def Wd.subst : Wd → Wd → Wd
  | .gen i, _ => .gen i
  | .var, τ => τ
  | .mul a b, τ => .mul (a.subst τ) (b.subst τ)
  | .pow a k, τ => .pow (a.subst τ) k

theorem Wd.evalC_subst (g : Nat) (τ : Wd) :
    ∀ ω : Wd, (ω.subst τ).evalC g = ω.evalC (τ.evalC g)
  | .gen _ => rfl
  | .var => rfl
  | .mul a b => by simp only [Wd.subst, Wd.evalC, Wd.evalC_subst g τ a, Wd.evalC_subst g τ b]
  | .pow a k => by simp only [Wd.subst, Wd.evalC, Wd.evalC_subst g τ a]

@[expose] def Wd.ofList : List Nat → Wd
  | [] => .gen 4
  | i :: l => .mul (.gen i) (Wd.ofList l)

theorem Wd.evalC_ofList (g : Nat) : ∀ l : List Nat, (Wd.ofList l).evalC g = evalList l
  | [] => rfl
  | i :: l => by simp only [Wd.ofList, Wd.evalC, evalList, Wd.evalC_ofList g l]

@[expose] def x0W (i : Nat) : Wd := Wd.ofList (x0Words.getD i [])

theorem x0_eq (i g : Nat) : x0 (x0Codes ()) i = (x0W i).evalC g := by
  rw [x0W, Wd.evalC_ofList, x0, x0Codes, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getD_eq_getD_getElem?]
  cases x0Words[i]? <;> rfl

@[expose] def Cert.word0 (c : Cert) : Wd := .mul (x0W c.z) (.pow (.mul (x0W c.x) .var) c.k)

theorem ok0_sound {r : Nat} {c : Cert} (h : ok0 (x0Codes ()) r c = true) :
    good (c.word0.evalC r) = true := by
  rw [ok0, x0_eq c.z r, x0_eq c.x r] at h
  exact h

theorem okRep_sound {reps : Array Nat} {certs : Array Cert} {i : Nat}
    (h : okRep (x0Codes ()) reps certs i = true) :
    ∃ ω : Wd, good (ω.evalC (reps.getD i 0)) = true := by
  unfold okRep at h
  dsimp only at h
  split_ifs at h with h0 h1
  · exact ⟨_, ok0_sound h⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨-, -⟩, hr⟩, hok⟩ := h
    set c := certs.getD i default
    set τ : Wd := .mul (.mul (x0W c.a) (.pow (.mul (x0W c.x) .var) c.k)) (x0W c.b) with hτ
    refine ⟨(certs.getD c.d default).word0.subst τ, ?_⟩
    rw [Wd.evalC_subst]
    have : τ.evalC (reps.getD i 0) = reps.getD c.d 0 := by
      rw [← hr, hτ]
      simp only [Wd.evalC, ← x0_eq]
    rw [this]
    exact ok0_sound hok

theorem gl12_sound (h : glCheck () = true) {c : Nat} (hc : c < N) (hns : nonsing c = true)
    (huv : mulC c uvC = mulC uvC c) :
    (mulC c tC = mulC tC c → powC c 64 = idC) ∧ (normD c = true → normV c = true) := by
  unfold glCheck glCheckWith at h
  simp only [Bool.and_eq_true, Nat.allLTTR_eq_true] at h
  have hc' := h.2 c hc
  rw [hns, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc'
  have h12 := hc'.1
  unfold checkG12 at h12
  simp only [huv, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at h12
  refine ⟨fun ht => ?_, fun hD => ?_⟩
  · rcases h12.1 with h' | h'
    · exact absurd ht h'
    · exact h'
  · rcases h12.2 with h' | h'
    · rw [hD] at h'; exact absurd h' (by decide)
    · exact h'

theorem gl3_sound (h : glCheck () = true) {c : Nat} (hc : c < N) (hns : nonsing c = true)
    (hst : stabW4 c = false) : ∃ ω : Wd, good (ω.evalC c) = true := by
  unfold glCheck at h
  set D := buildData () with hD
  unfold glCheckWith at h
  simp only [Bool.and_eq_true, Nat.allLTTR_eq_true, beq_iff_eq] at h
  obtain ⟨hX, hall⟩ := h
  have hc' := hall c hc
  rw [hns, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc'
  have h3 := hc'.2
  unfold checkG3 at h3
  rw [hst, Bool.false_or] at h3
  dsimp only at h3
  split at h3
  · rename_i i xm j _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    obtain ⟨⟨hi, hoki⟩, hr⟩ := h3
    have hoki' : okRep (x0Codes ()) D.sc.reps D.certs i = true := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hi]
        at hoki
      rw [← hX]
      exact hoki
    obtain ⟨ω, hω⟩ := okRep_sound hoki'
    set a := (D.P.getD (D.I.getD xm 0) #[]).getD (keyArg D.T D.M c).2 0
    set b := D.I.getD j 0
    refine ⟨ω.subst (.mul (.mul (x0W a) .var) (x0W b)), ?_⟩
    rw [Wd.evalC_subst]
    have : (Wd.mul (.mul (x0W a) .var) (x0W b)).evalC c = D.sc.reps.getD i 0 := by
      rw [← hr, hX]
      simp only [Wd.evalC, ← x0_eq]
    rw [this]
    exact hω
  · exact absurd h3 (by decide)

end CFSG.CGT.Stroth77.GL5
