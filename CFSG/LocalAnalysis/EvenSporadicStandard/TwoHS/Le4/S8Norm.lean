module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

@[expose] def allBits : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (allBits k).flatMap fun l => [0 :: l, 1 :: l]

theorem mem_allBits : ∀ {l : List ℕ}, (∀ x ∈ l, x < 2) → l ∈ allBits l.length
  | [], _ => by simp [allBits]
  | x :: l, hl => by
    simp only [List.length_cons, allBits, List.mem_flatMap]
    refine ⟨l, mem_allBits fun y hy => hl y (List.mem_cons_of_mem _ hy), ?_⟩
    obtain rfl | rfl : x = 0 ∨ x = 1 := by have := hl x List.mem_cons_self; omega
    · simp
    · simp

@[expose] def R4.ofList (l : List ℕ) : R4 :=
  ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
    l.getD 7 0, l.getD 8 0, l.getD 9 0, l.getD 10 0, l.getD 11 0, l.getD 12 0, l.getD 13 0,
    l.getD 14 0, l.getD 15 0⟩

@[expose] def bitsR : List R4 := (allBits 16).map R4.ofList

@[expose] def R4.wf2 (a : R4) : Prop :=
  a.a00 < 2 ∧ a.a01 < 2 ∧ a.a02 < 2 ∧ a.a03 < 2 ∧ a.a10 < 2 ∧ a.a11 < 2 ∧ a.a12 < 2 ∧
    a.a13 < 2 ∧ a.a20 < 2 ∧ a.a21 < 2 ∧ a.a22 < 2 ∧ a.a23 < 2 ∧ a.a30 < 2 ∧ a.a31 < 2 ∧
    a.a32 < 2 ∧ a.a33 < 2

@[expose] def R4.hi (a : R4) : R4 :=
  ⟨a.a00 / 2, a.a01 / 2, a.a02 / 2, a.a03 / 2, a.a10 / 2, a.a11 / 2, a.a12 / 2, a.a13 / 2,
   a.a20 / 2, a.a21 / 2, a.a22 / 2, a.a23 / 2, a.a30 / 2, a.a31 / 2, a.a32 / 2, a.a33 / 2⟩

@[expose] def lift2 (b x : R4) : R4 :=
  ⟨b.a00 + 2 * x.a00, b.a01 + 2 * x.a01, b.a02 + 2 * x.a02, b.a03 + 2 * x.a03,
   b.a10 + 2 * x.a10, b.a11 + 2 * x.a11, b.a12 + 2 * x.a12, b.a13 + 2 * x.a13,
   b.a20 + 2 * x.a20, b.a21 + 2 * x.a21, b.a22 + 2 * x.a22, b.a23 + 2 * x.a23,
   b.a30 + 2 * x.a30, b.a31 + 2 * x.a31, b.a32 + 2 * x.a32, b.a33 + 2 * x.a33⟩

theorem mem_bitsR {b : R4} (hb : b.wf2) : b ∈ bitsR := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hb
  refine List.mem_map.2 ⟨[b.a00, b.a01, b.a02, b.a03, b.a10, b.a11, b.a12, b.a13, b.a20, b.a21,
    b.a22, b.a23, b.a30, b.a31, b.a32, b.a33], mem_allBits ?_, rfl⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem mod2_wf2 (a : R4) : a.mod2.wf2 := by
  simp only [R4.wf2, R4.mod2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem hi_wf2 {a : R4} (ha : a.wf) : (R4.hi a).wf2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := ha
  simp only [R4.wf2, R4.hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem lift2_mod2_hi (a : R4) : lift2 a.mod2 (R4.hi a) = a := by
  cases a
  simp only [lift2, R4.mod2, R4.hi, R4.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem mod2_dot (x0 x1 x2 x3 y0 y1 y2 y3 : ℕ) :
    ((x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) % 4) % 2 =
      (((x0 % 2) * (y0 % 2) + (x1 % 2) * (y1 % 2) + (x2 % 2) * (y2 % 2) +
        (x3 % 2) * (y3 % 2)) % 4) % 2 := by
  have h0 := Nat.mul_mod x0 y0 2
  have h1 := Nat.mul_mod x1 y1 2
  have h2 := Nat.mul_mod x2 y2 2
  have h3 := Nat.mul_mod x3 y3 2
  omega

theorem mod2_rmul (a b : R4) : (rmul a b).mod2 = (rmul a.mod2 b.mod2).mod2 := by
  simp only [R4.mod2, rmul, R4.mk.injEq]
  exact ⟨mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _,
    mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _,
    mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _,
    mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _,
    mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _, mod2_dot _ _ _ _ _ _ _ _,
    mod2_dot _ _ _ _ _ _ _ _⟩

theorem mod2_one : R4.one.mod2 = R4.one := rfl

@[expose] def Norm1R (a : R4) : Prop := ∀ s ∈ shatR, ∃ s' ∈ shatR, rmul a s = rmul s' a

@[expose] def Norm2R (a : R4) : Prop := ∀ s' ∈ shatR, ∃ s ∈ shatR, rmul a s = rmul s' a

@[expose] def ConclR (a : R4) : Prop :=
  rmv a tRV = tRV ∨ (rmv a tRV = zpRV ∧ a ∈ candR)

@[expose] def shat2R : List R4 := shatR.map R4.mod2

@[expose] def NormB2 (b : R4) : Bool :=
  shat2R.all (fun s => shat2R.any fun s' => (rmul b s).mod2 == (rmul s' b).mod2) &&
  shat2R.all (fun s' => shat2R.any fun s => (rmul b s).mod2 == (rmul s' b).mod2)

@[expose] def normR2 : List R4 := bitsR.filter NormB2

@[expose] def survR : List R4 :=
  normR2.filter fun b => normR2.any fun b' => (rmul b b').mod2 == R4.one

@[expose] def compatR (b : R4) : List (R4 × List R4) :=
  shatR.map fun s =>
    (s, shatR.filter fun s' => decide ((rmul b s.mod2).mod2 = (rmul s'.mod2 b).mod2))

@[expose] def Norm1T (T : List (R4 × List R4)) (a : R4) : Prop :=
  ∀ p ∈ T, ∃ s' ∈ p.2, rmul a p.1 = rmul s' a

@[expose] def norm1B (T : List (R4 × List R4)) (a : R4) : Bool :=
  T.all fun p => p.2.any fun s' => rmul a p.1 == rmul s' a

@[expose] def norm2B (a : R4) : Bool :=
  shatR.all fun s' => shatR.any fun s => rmul a s == rmul s' a

@[expose] def nCaseB (T : List (R4 × List R4)) (a : R4) : Bool :=
  rmv a tRV == tRV || !(norm1B T a && norm2B a) || (rmv a tRV == zpRV && decide (a ∈ candR))

@[expose] def NRawB (b : R4) (T : List (R4 × List R4)) : Prop :=
  ∀ x ∈ bitsR, nCaseB T (lift2 b x) = true

instance (b : R4) (T : List (R4 × List R4)) : Decidable (NRawB b T) := by
  unfold NRawB; infer_instance

@[expose] def NRaw : Prop := ∀ b ∈ survR, NRawB b (compatR b)

instance : Decidable NRaw := by unfold NRaw; infer_instance

@[expose] def normR : Bool := decide NRaw

theorem norm1B_iff {T : List (R4 × List R4)} {a : R4} : norm1B T a = true ↔ Norm1T T a := by
  simp [norm1B, Norm1T, List.all_eq_true, List.any_eq_true, beq_iff_eq]

theorem norm2B_iff {a : R4} : norm2B a = true ↔ Norm2R a := by
  simp [norm2B, Norm2R, List.all_eq_true, List.any_eq_true, beq_iff_eq]

theorem norm1T_of_norm1R {a : R4} (h : Norm1R a) : Norm1T (compatR a.mod2) a := by
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
  obtain ⟨s', hs', hss⟩ := h s hs
  refine ⟨s', List.mem_filter.2 ⟨hs', decide_eq_true ?_⟩, hss⟩
  rw [← mod2_rmul, ← mod2_rmul, hss]

theorem normB2_of_norm {a : R4} (h1 : Norm1R a) (h2 : Norm2R a) : NormB2 a.mod2 = true := by
  simp only [NormB2, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq]
  refine ⟨fun s hs => ?_, fun s' hs' => ?_⟩
  · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
    obtain ⟨s', hs', hss⟩ := h1 s0 hs0
    refine ⟨s'.mod2, List.mem_map.2 ⟨s', hs', rfl⟩, ?_⟩
    rw [← mod2_rmul, ← mod2_rmul, hss]
  · obtain ⟨s0', hs0', rfl⟩ := List.mem_map.1 hs'
    obtain ⟨s, hs, hss⟩ := h2 s0' hs0'
    refine ⟨s.mod2, List.mem_map.2 ⟨s, hs, rfl⟩, ?_⟩
    rw [← mod2_rmul, ← mod2_rmul, hss]

theorem nCaseB_sound {T : List (R4 × List R4)} {a : R4} (h : nCaseB T a = true) :
    rmv a tRV = tRV ∨ ¬ (Norm1T T a ∧ Norm2R a) ∨ (rmv a tRV = zpRV ∧ a ∈ candR) := by
  unfold nCaseB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ?_)
    rintro ⟨n1, n2⟩
    rw [← norm1B_iff] at n1
    rw [← norm2B_iff] at n2
    simp [n1, n2] at h
  · exact Or.inr (Or.inr h)

theorem concl_of_raw {A : M4} (h : ConclR (toR4 A)) : Concl A := by
  have hv : ∀ v : RV, A *ᵥ ofRV v = ofRV (rmv (toR4 A) v) := by
    intro v
    rw [ofRV_rmv, ofR4_toR4]
  have ht : ofRV tRV = tVec := ofRV_toRV _
  have hz : ofRV zpRV = zpVec := ofRV_toRV _
  rcases h with h | ⟨h, h2⟩
  · left
    rw [← ht, hv, h]
  · refine Or.inr ⟨by rw [← ht, hv, h, hz], ?_⟩
    obtain ⟨C, hC, hCA⟩ := List.mem_map.1 h2
    rw [← ofR4_toR4 A, ← hCA, ofR4_toR4]
    exact hC

theorem norm1R_of_norm1 {A : M4} (hN : Norm1 A) : Norm1R (toR4 A) := by
  intro s hs
  obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hs
  obtain ⟨S', hS', hSS⟩ := hN S hS
  refine ⟨toR4 S', List.mem_map.2 ⟨S', hS', rfl⟩, ?_⟩
  apply ofR4_inj (wf_rmul _ _) (wf_rmul _ _)
  rw [ofR4_rmul, ofR4_rmul, ofR4_toR4, ofR4_toR4, ofR4_toR4]
  exact hSS

theorem norm2R_of_norm2 {A : M4} (hN : Norm2 A) : Norm2R (toR4 A) := by
  intro s' hs'
  obtain ⟨S', hS', rfl⟩ := List.mem_map.1 hs'
  obtain ⟨S, hS, hSS⟩ := hN S' hS'
  refine ⟨toR4 S, List.mem_map.2 ⟨S, hS, rfl⟩, ?_⟩
  apply ofR4_inj (wf_rmul _ _) (wf_rmul _ _)
  rw [ofR4_rmul, ofR4_rmul, ofR4_toR4, ofR4_toR4, ofR4_toR4]
  exact hSS

theorem norm1_inv {A A' : M4} (h : A * A' = 1) (h' : A' * A = 1) (hN2 : Norm2 A) :
    Norm1 A' := by
  intro s hs
  obtain ⟨s0, hs0, hss⟩ := hN2 s hs
  refine ⟨s0, hs0, ?_⟩
  calc A' * s = A' * s * (A * A') := by rw [h, mul_one]
    _ = A' * (s * A) * A' := by simp only [mul_assoc]
    _ = A' * (A * s0) * A' := by rw [hss]
    _ = (A' * A) * s0 * A' := by simp only [mul_assoc]
    _ = s0 * A' := by rw [h', one_mul]

theorem norm2_inv {A A' : M4} (h : A * A' = 1) (h' : A' * A = 1) (hN1 : Norm1 A) :
    Norm2 A' := by
  intro s' hs'
  obtain ⟨s1, hs1, hss⟩ := hN1 s' hs'
  refine ⟨s1, hs1, ?_⟩
  calc A' * s1 = (A' * s1) * (A * A') := by rw [h, mul_one]
    _ = A' * (s1 * A) * A' := by simp only [mul_assoc]
    _ = A' * (A * s') * A' := by rw [hss]
    _ = (A' * A) * s' * A' := by simp only [mul_assoc]
    _ = s' * A' := by rw [h', one_mul]

theorem normComplete_of_raw (h : NRaw) : NormComplete := by
  intro A ⟨A', hAA', hA'A⟩ hN1 hN2
  have hwa : (toR4 A).wf := wf_toR4 A
  have hinv : rmul (toR4 A) (toR4 A') = R4.one := by
    apply ofR4_inj (wf_rmul _ _) wf_one
    rw [ofR4_rmul, ofR4_toR4, ofR4_toR4, hAA', ofR4_one]
  have hn1 := norm1R_of_norm1 hN1
  have hn2 := norm2R_of_norm2 hN2
  have hn1' := norm1R_of_norm1 (norm1_inv hAA' hA'A hN2)
  have hn2' := norm2R_of_norm2 (norm2_inv hAA' hA'A hN1)
  have hb : (toR4 A).mod2 ∈ survR := by
    refine List.mem_filter.2
      ⟨List.mem_filter.2 ⟨mem_bitsR (mod2_wf2 _), normB2_of_norm hn1 hn2⟩, ?_⟩
    simp only [List.any_eq_true, beq_iff_eq]
    refine ⟨(toR4 A').mod2, List.mem_filter.2 ⟨mem_bitsR (mod2_wf2 _), normB2_of_norm hn1' hn2'⟩,
      ?_⟩
    rw [← mod2_rmul, hinv, mod2_one]
  have key := h _ hb (R4.hi (toR4 A)) (mem_bitsR (hi_wf2 hwa))
  rw [lift2_mod2_hi] at key
  refine concl_of_raw ?_
  rcases nCaseB_sound key with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd ⟨norm1T_of_norm1R hn1, hn2⟩ h1
  · exact Or.inr h1

end CFSG.EvenSporadicStandard.TwoHS
