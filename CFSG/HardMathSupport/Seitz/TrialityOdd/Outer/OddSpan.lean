module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddForm
public import CFSG.RankThree.PartOne.SEITZ8.D4Span
public import CFSG.RankThree.PartOne.SEITZ8.D4Entry
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddComm

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ8

variable {K : Type} [Field K]

@[expose] def PMOne (ε : K) : Prop := ε = 1 ∨ ε = -1

theorem PMOne.mul {a b : K} (ha : PMOne a) (hb : PMOne b) : PMOne (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [PMOne]

theorem PMOne.mem (k : Subfield K) {a : K} (ha : PMOne a) : a ∈ k := by
  rcases ha with rfl | rfl
  · exact k.one_mem
  · exact k.neg_mem k.one_mem

theorem PMOne.sq {a : K} (ha : PMOne a) : a * a = 1 := by
  rcases ha with rfl | rfl <;> simp

theorem pmone_wtRoot (γ : Fin d4.rank → ℤ) : PMOne ((wtRoot γ : ℤ) : K) := by
  unfold wtRoot PMOne
  rcases neg_one_pow_eq_or ℤ ((∑ j, γ j).natAbs + 1) with h | h <;> rw [h] <;> simp

theorem weylElement_smul_rv_odd (i : Fin d4.rank) {p p' : ℕ} (hp : p < 24)
    (h : reflect d4 i (d4Root p) = d4Root p') :
    ∃ ε : K, PMOne ε ∧ (weylElement d4 K i : adjointGroup d4 K) • (rv p : RootModule d4 K) =
      ε • rv p' := by
  have hα : IsRoot d4 (d4Root p) := isRoot_d4 hp
  have hw := weylElt_rootVec (R := K) i (1 : Kˣ) hα
  refine ⟨(-1) ^ stringDown d4 i (d4Root p), ?_, ?_⟩
  · unfold PMOne
    rcases neg_one_pow_eq_or K (stringDown d4 i (d4Root p)) with h | h <;> rw [h] <;> simp
  · show (weylElt d4 K i 1 : Module.End K (RootModule d4 K)) (rootVec d4 K (d4Root p)) = _
    rw [hw, h]
    simp

@[expose] def RvMove (m : adjointGroup d4 K) (p q : ℕ) : Prop :=
  ∃ ε : K, PMOne ε ∧ m • (rv p : RootModule d4 K) = ε • rv q

theorem RvMove.comp {a b : adjointGroup d4 K} {p q s : ℕ} (ha : RvMove a p q)
    (hb : RvMove b q s) : RvMove (b * a) p s := by
  obtain ⟨ε₁, h₁, ha⟩ := ha
  obtain ⟨ε₂, h₂, hb⟩ := hb
  exact ⟨ε₁ * ε₂, h₁.mul h₂, by rw [mul_smul, ha, smul_smul_comm', hb, smul_smul]⟩

theorem weylElement_rvMove (i : Fin d4.rank) {p p' : ℕ} (hp : p < 24)
    (h : reflect d4 i (d4Root p) = d4Root p') : RvMove (weylElement d4 K i : adjointGroup d4 K) p p' :=
  weylElement_smul_rv_odd i hp h

theorem reach_long_odd {σ : K →+* K} {k : Subfield K} {R : Subgroup (adjointGroup d4 K)}
    (h : SpanHyp σ k R) :
    ∀ p ∈ longPos, ∃ m ∈ R, RvMove m 22 p := by
  obtain ⟨c1, c2, c3, a1, a2, a3, b1, b2, b3⟩ := reflect_facts
  have s0 := weylElement_rvMove (K := K) (nd 2) (p := 22) (by decide) c1
  have s1 := weylElement_rvMove (K := K) (nd 2) (p := 2) (by decide) c2
  have s2 := weylElement_rvMove (K := K) (nd 2) (p := 21) (by decide) c3
  have s3 : RvMove (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) :
        adjointGroup d4 K) 19 2 := by
    have t3 := weylElement_rvMove (K := K) (nd 3) (p := 19) (by decide) a1
    have t1 := weylElement_rvMove (K := K) (nd 1) (p := 12) (by decide) a2
    have t0 := weylElement_rvMove (K := K) (nd 0) (p := 5) (by decide) a3
    have := (t3.comp t1).comp t0
    rw [← mul_assoc] at this
    exact this
  have s4 : RvMove (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) :
        adjointGroup d4 K) 8 21 := by
    have t3 := weylElement_rvMove (K := K) (nd 3) (p := 8) (by decide) b1
    have t1 := weylElement_rvMove (K := K) (nd 1) (p := 16) (by decide) b2
    have t0 := weylElement_rvMove (K := K) (nd 0) (p := 20) (by decide) b3
    have := (t3.comp t1).comp t0
    rw [← mul_assoc] at this
    exact this
  set a := weylElement d4 K (nd 2) with ha
  set b := weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) with hb
  intro p hp
  simp only [longPos, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨b * a, R.mul_mem h.n1 h.n0, s0.comp s3⟩
  · exact ⟨a * (b * a), R.mul_mem h.n0 (R.mul_mem h.n1 h.n0), (s0.comp s3).comp s1⟩
  · exact ⟨a, h.n0, s0⟩
  · exact ⟨b * (a * (b * a)), R.mul_mem h.n1 (R.mul_mem h.n0 (R.mul_mem h.n1 h.n0)),
      ((s0.comp s3).comp s1).comp s4⟩
  · exact ⟨1, R.one_mem, 1, Or.inl rfl, by rw [one_smul, one_smul]⟩
  · exact ⟨a * (b * (a * (b * a))),
      R.mul_mem h.n0 (R.mul_mem h.n1 (R.mul_mem h.n0 (R.mul_mem h.n1 h.n0))),
      (((s0.comp s3).comp s1).comp s4).comp s2⟩

section Cartan

variable {σ : K →+* K} {k : Subfield K} {R : Subgroup (adjointGroup d4 K)}

theorem xe_smul_outer_neg (i : Fin d4.rank) {p : ℕ} (hp : d4Root p = Pi.single i 1)
    {q q' : ℕ} (hq : q < 24) (hq' : q' < 24)
    (h0 : bindCol (Tag.rootCertificate d4) (xg i 0) (some (rI q hq, 1)) = some (rI q hq, 1))
    (h1 : bindCol (Tag.rootCertificate d4) (xg i 1) (some (rI q hq, 1)) = some (Sum.inl i, 1))
    (h2 : bindCol (Tag.rootCertificate d4) (xg i 2) (some (rI q hq, 1)) = some (rI q' hq', 1))
    (h3 : bindCol (Tag.rootCertificate d4) (xg i 3) (some (rI q hq, 1)) = none) :
    (xe p (1 : K) : adjointGroup d4 K) • (rv q : RootModule d4 K) =
      rv q + hVec d4 K i + rv q' := by
  rw [xe_smul_simple i hp, rv_eq_single q hq,
    xOp_single_eq (xOp d4 K) (xCoeff d4 K) xg (fun i c => xOp_eq_sum_xCoeff i c)
      (fun i k b => xCoeff_toLabel (Tag.rootCertificate_check d4) K
        (Tag.stringData_check d4) i k b) i (rI q hq) _ _ _ _ h0 h1 h2 h3]
  simp only [toVec_none, add_zero, toVec_some, Int.cast_one, one_smul]
  rw [rv_eq_single q' hq']
  rfl

theorem xe_smul_outer_fix (i : Fin d4.rank) {p : ℕ} (hp : d4Root p = Pi.single i 1)
    {q : ℕ} (hq : q < 24)
    (h0 : bindCol (Tag.rootCertificate d4) (xg i 0) (some (rI q hq, 1)) = some (rI q hq, 1))
    (h1 : bindCol (Tag.rootCertificate d4) (xg i 1) (some (rI q hq, 1)) = none)
    (h2 : bindCol (Tag.rootCertificate d4) (xg i 2) (some (rI q hq, 1)) = none)
    (h3 : bindCol (Tag.rootCertificate d4) (xg i 3) (some (rI q hq, 1)) = none) :
    (xe p (1 : K) : adjointGroup d4 K) • (rv q : RootModule d4 K) = rv q := by
  rw [xe_smul_simple i hp, rv_eq_single q hq,
    xOp_single_eq (xOp d4 K) (xCoeff d4 K) xg (fun i c => xOp_eq_sum_xCoeff i c)
      (fun i k b => xCoeff_toLabel (Tag.rootCertificate_check d4) K
        (Tag.stringData_check d4) i k b) i (rI q hq) _ _ _ _ h0 h1 h2 h3]
  simp only [toVec_none, add_zero, toVec_some, Int.cast_one, one_smul]

@[expose] def NegCols (i : Fin d4.rank) (q q' : ℕ) (hq : q < 24) (hq' : q' < 24) : Prop :=
  bindCol (Tag.rootCertificate d4) (xg i 0) (some (rI q hq, 1)) = some (rI q hq, 1) ∧
  bindCol (Tag.rootCertificate d4) (xg i 1) (some (rI q hq, 1)) = some (Sum.inl i, 1) ∧
  bindCol (Tag.rootCertificate d4) (xg i 2) (some (rI q hq, 1)) = some (rI q' hq', 1) ∧
  bindCol (Tag.rootCertificate d4) (xg i 3) (some (rI q hq, 1)) = none

@[expose] def FixCols (i : Fin d4.rank) (q : ℕ) (hq : q < 24) : Prop :=
  bindCol (Tag.rootCertificate d4) (xg i 0) (some (rI q hq, 1)) = some (rI q hq, 1) ∧
  bindCol (Tag.rootCertificate d4) (xg i 1) (some (rI q hq, 1)) = none ∧
  bindCol (Tag.rootCertificate d4) (xg i 2) (some (rI q hq, 1)) = none ∧
  bindCol (Tag.rootCertificate d4) (xg i 3) (some (rI q hq, 1)) = none

theorem negCols_0 : NegCols (nd 0) 4 0 (by decide) (by decide) := by
  unfold NegCols; decide +kernel

theorem negCols_1 : NegCols (nd 1) 6 1 (by decide) (by decide) := by
  unfold NegCols; decide +kernel

theorem negCols_3 : NegCols (nd 3) 10 3 (by decide) (by decide) := by
  unfold NegCols; decide +kernel

theorem fixCols_1_4 : FixCols (nd 1) 4 (by decide) := by unfold FixCols; decide +kernel
theorem fixCols_3_4 : FixCols (nd 3) 4 (by decide) := by unfold FixCols; decide +kernel
theorem fixCols_0_6 : FixCols (nd 0) 6 (by decide) := by unfold FixCols; decide +kernel
theorem fixCols_3_6 : FixCols (nd 3) 6 (by decide) := by unfold FixCols; decide +kernel
theorem fixCols_0_10 : FixCols (nd 0) 10 (by decide) := by unfold FixCols; decide +kernel
theorem fixCols_1_10 : FixCols (nd 1) 10 (by decide) := by unfold FixCols; decide +kernel

end Cartan

section Rat

variable {σ : K →+* K} {k : Subfield K} {R : Subgroup (adjointGroup d4 K)}

theorem hVec_outer_mem_span (h : SpanHyp σ k R) {i : Fin d4.rank}
    (hi : i = nd 0 ∨ i = nd 1 ∨ i = nd 3) :
    hVec d4 K i ∈ Submodule.span k (longOrbit R) := by
  have hP : (xe 0 (1 : K) * xe 1 (1 : K) * xe 3 (1 : K) : adjointGroup d4 K) ∈ R := by
    have := h.A 1 k.one_mem
    rwa [map_one, map_one] at this
  have hlt : ∀ q : ℕ, q < 24 → rv q ∈ Submodule.span k (longOrbit R) := fun q hq =>
    rv_mem_span h hq
  rcases hi with rfl | rfl | rfl
  · obtain ⟨a0, a1, a2, a3⟩ := negCols_0
    obtain ⟨b0, b1, b2, b3⟩ := fixCols_3_4
    obtain ⟨c0, c1, c2, c3⟩ := fixCols_1_4
    have e : (xe 0 (1 : K) * xe 1 (1 : K) * xe 3 (1 : K) : adjointGroup d4 K) •
        (rv 4 : RootModule d4 K) = rv 4 + hVec d4 K (nd 0) + rv 0 := by
      rw [mul_smul, mul_smul, xe_smul_outer_fix (nd 3) d4Root_simple_3 (by decide) b0 b1 b2 b3,
        xe_smul_outer_fix (nd 1) d4Root_simple_1 (by decide) c0 c1 c2 c3,
        xe_smul_outer_neg (nd 0) d4Root_simple_0 (by decide) (by decide) a0 a1 a2 a3]
    have hm := smul_mem_span k hP (hlt 4 (by decide))
    rw [e] at hm
    have := Submodule.sub_mem _ (Submodule.sub_mem _ hm (hlt 4 (by decide))) (hlt 0 (by decide))
    rwa [show rv 4 + hVec d4 K (nd 0) + rv 0 - rv 4 - rv 0 = hVec d4 K (nd 0) by abel] at this
  · obtain ⟨a0, a1, a2, a3⟩ := negCols_1
    obtain ⟨b0, b1, b2, b3⟩ := fixCols_3_6
    obtain ⟨c0, c1, c2, c3⟩ := fixCols_0_6
    have hP' : (xe 1 (1 : K) * xe 0 (1 : K) * xe 3 (1 : K) : adjointGroup d4 K) ∈ R := by
      rwa [show (xe 1 (1 : K) * xe 0 (1 : K) : adjointGroup d4 K) = xe 0 1 * xe 1 1 from
        endO_1_0 1 1]
    have e : (xe 1 (1 : K) * xe 0 (1 : K) * xe 3 (1 : K) : adjointGroup d4 K) •
        (rv 6 : RootModule d4 K) = rv 6 + hVec d4 K (nd 1) + rv 1 := by
      rw [mul_smul, mul_smul, xe_smul_outer_fix (nd 3) d4Root_simple_3 (by decide) b0 b1 b2 b3,
        xe_smul_outer_fix (nd 0) d4Root_simple_0 (by decide) c0 c1 c2 c3,
        xe_smul_outer_neg (nd 1) d4Root_simple_1 (by decide) (by decide) a0 a1 a2 a3]
    have hm := smul_mem_span k hP' (hlt 6 (by decide))
    rw [e] at hm
    have := Submodule.sub_mem _ (Submodule.sub_mem _ hm (hlt 6 (by decide))) (hlt 1 (by decide))
    rwa [show rv 6 + hVec d4 K (nd 1) + rv 1 - rv 6 - rv 1 = hVec d4 K (nd 1) by abel] at this
  · obtain ⟨a0, a1, a2, a3⟩ := negCols_3
    obtain ⟨b0, b1, b2, b3⟩ := fixCols_1_10
    obtain ⟨c0, c1, c2, c3⟩ := fixCols_0_10
    have hP' : (xe 3 (1 : K) * xe 0 (1 : K) * xe 1 (1 : K) : adjointGroup d4 K) ∈ R := by
      have e1 : (xe 3 (1 : K) * xe 0 (1 : K) * xe 1 (1 : K) : adjointGroup d4 K) =
          xe 0 1 * xe 1 1 * xe 3 1 := by
        rw [endO_3_0 1 1, mul_assoc, endO_3_1 1 1, ← mul_assoc]
      rwa [e1]
    have e : (xe 3 (1 : K) * xe 0 (1 : K) * xe 1 (1 : K) : adjointGroup d4 K) •
        (rv 10 : RootModule d4 K) = rv 10 + hVec d4 K (nd 3) + rv 3 := by
      rw [mul_smul, mul_smul, xe_smul_outer_fix (nd 1) d4Root_simple_1 (by decide) b0 b1 b2 b3,
        xe_smul_outer_fix (nd 0) d4Root_simple_0 (by decide) c0 c1 c2 c3,
        xe_smul_outer_neg (nd 3) d4Root_simple_3 (by decide) (by decide) a0 a1 a2 a3]
    have hm := smul_mem_span k hP' (hlt 10 (by decide))
    rw [e] at hm
    have := Submodule.sub_mem _ (Submodule.sub_mem _ hm (hlt 10 (by decide))) (hlt 3 (by decide))
    rwa [show rv 10 + hVec d4 K (nd 3) + rv 3 - rv 10 - rv 3 = hVec d4 K (nd 3) by abel] at this

end Rat

end CFSG.HardMathSupport.Seitz.TrialityOdd
