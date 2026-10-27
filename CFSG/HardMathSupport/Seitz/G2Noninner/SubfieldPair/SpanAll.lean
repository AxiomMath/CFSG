module

public import CFSG.RankThree.PartOne.SEITZ6.G2Span

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6

variable {K : Type} [Field K]

@[expose] def smallTarget : Col (Tag.rootCertificate .G2) → Option GIdx
  | some (c', z) => if z ≠ 0 ∧ z.natAbs ≤ 2 then some c' else none
  | none => none

@[expose] def sumTarget : Col (Tag.rootCertificate .G2) → Col (Tag.rootCertificate .G2) →
    Option GIdx
  | some (c', z), none => if z ≠ 0 ∧ z.natAbs ≤ 2 then some c' else none
  | none, some (c', z) => if z ≠ 0 ∧ z.natAbs ≤ 2 then some c' else none
  | _, _ => none

@[expose] def moveListA (c : GIdx) : List GIdx :=
  (List.finRange (Tag.rank .G2)).flatMap fun i =>
    (sumTarget (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 1 c)
        (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 3 c)).toList ++
      (sumTarget (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 1 c)
        (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 3 c)).toList ++
      (smallTarget (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 2 c)).toList ++
      (smallTarget (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 2 c)).toList

@[expose] def reachStepA (L : List GIdx) : List GIdx := L ++ L.flatMap moveListA

@[expose] def reachNA : ℕ → List GIdx → List GIdx
  | 0, L => L
  | n + 1, L => reachNA n (reachStepA L)

@[expose] def reachAllA (n : ℕ) : Bool := gIdxList.all fun a => decide (a ∈ reachNA n longIdx)

theorem reachAllA_three : reachAllA 3 = true := by decide +kernel

theorem mem_reachNA_three (a : GIdx) : a ∈ reachNA 3 longIdx := by
  have h := reachAllA_three
  simp only [reachAllA, List.all_eq_true, decide_eq_true_eq] at h
  exact h a (mem_gIdxList a)

theorem mem_reachNA {P : GIdx → Prop} (hP : ∀ c, P c → ∀ c' ∈ moveListA c, P c') :
    ∀ (n : ℕ) (L : List GIdx), (∀ c ∈ L, P c) → ∀ c ∈ reachNA n L, P c := by
  intro n
  induction n with
  | zero => intro L hL; exact hL
  | succ n ih =>
    intro L hL
    refine ih (reachStepA L) fun c hc => ?_
    simp only [reachStepA, List.mem_append, List.mem_flatMap] at hc
    rcases hc with hc | ⟨d, hd, hc⟩
    · exact hL c hc
    · exact hP d (hL d hd) c hc

theorem mem_moveListA {c c' : GIdx} :
    c' ∈ moveListA c ↔ ∃ i : Fin (Tag.rank .G2),
      sumTarget (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 1 c)
        (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 3 c) = some c' ∨
      sumTarget (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 1 c)
        (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 3 c) = some c' ∨
      smallTarget (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 2 c) = some c' ∨
      smallTarget (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i 2 c) = some c' := by
  simp only [moveListA, List.mem_flatMap, List.mem_finRange, true_and, List.mem_append,
    Option.mem_toList]
  simp only [or_assoc]

theorem smallTarget_eq_some {u : Col (Tag.rootCertificate .G2)} {c' : GIdx}
    (h : smallTarget u = some c') : ∃ z : ℤ, u = some (c', z) ∧ z ≠ 0 ∧ z.natAbs ≤ 2 := by
  rcases u with _ | ⟨a, z⟩
  · simp [smallTarget] at h
  · simp only [smallTarget] at h
    split_ifs at h with hz
    · cases h
      exact ⟨z, rfl, hz⟩

theorem sumTarget_eq_some {u v : Col (Tag.rootCertificate .G2)} {c' : GIdx}
    (h : sumTarget u v = some c') : ∃ z : ℤ, z ≠ 0 ∧ z.natAbs ≤ 2 ∧
      ((u = some (c', z) ∧ v = none) ∨ (u = none ∧ v = some (c', z))) := by
  rcases u with _ | ⟨a, z⟩ <;> rcases v with _ | ⟨b, w⟩
  · simp [sumTarget] at h
  · simp only [sumTarget] at h
    split_ifs at h with hz
    · cases h
      exact ⟨w, hz.1, hz.2, Or.inr ⟨rfl, rfl⟩⟩
  · simp only [sumTarget] at h
    split_ifs at h with hz
    · cases h
      exact ⟨z, hz.1, hz.2, Or.inl ⟨rfl, rfl⟩⟩
  · simp [sumTarget] at h

theorem intCast_ne_zero_of_two (h2 : (2 : K) ≠ 0) {z : ℤ} (hz : z ≠ 0) (hz2 : z.natAbs ≤ 2) :
    (z : K) ≠ 0 := by
  have : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp [h2]

section Action

theorem single_mem_of_small (h2 : (2 : K) ≠ 0) (k : Subfield K)
    {W : Submodule k (RootModule .G2 K)} {c' : GIdx} {z : ℤ} (hz : z ≠ 0) (hz2 : z.natAbs ≤ 2)
    (h : toVec (Tag.rootCertificate_check .G2) K (some (c', z)) ∈ W) :
    Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c') 1 ∈ W := by
  have hzK : (z : K) ≠ 0 := intCast_ne_zero_of_two h2 hz hz2
  have hzk : (z : k) ≠ 0 := fun e => hzK (by simpa using congrArg (Subtype.val : k → K) e)
  rw [toVec_some] at h
  have := W.smul_mem ((z : k)⁻¹) h
  have e : ((z : k)⁻¹ : k) • ((z : K) • Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c')
      (1 : K)) = Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c') 1 := by
    rw [show ∀ w : RootModule .G2 K, ((z : k)⁻¹ : k) • w = (((z : k)⁻¹ : k) : K) • w from
      fun _ => rfl, smul_smul]
    have : (((z : k)⁻¹ : k) : K) * (z : K) = 1 := by
      have := inv_mul_cancel₀ hzk
      simpa using congrArg (Subtype.val : k → K) this
    rw [this, one_smul]
  rwa [e] at this

theorem quad_of_stable (h2 : (2 : K) ≠ 0) (k : Subfield K) (W : Submodule k (RootModule .G2 K))
    (X : ℕ → Module.End K (RootModule .G2 K)) (A : K → Module.End K (RootModule .G2 K))
    (hA : ∀ c, A c = ∑ m ∈ Finset.range 4, c ^ m • X m) (hX0 : X 0 = 1)
    (h1 : ∀ w ∈ W, A 1 w ∈ W) (hm1 : ∀ w ∈ W, A (-1) w ∈ W) {w : RootModule .G2 K}
    (hw : w ∈ W) : X 2 w ∈ W ∧ (X 1 w + X 3 w) ∈ W := by
  have hP : A 1 w = w + X 1 w + X 2 w + X 3 w := by
    rw [hA]
    simp [Finset.sum_range_succ, hX0]
  have hM : A (-1) w = w - X 1 w + X 2 w - X 3 w := by
    rw [hA]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, hX0,
      pow_one, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [show ((-1 : K) ^ 2) = 1 by norm_num, show ((-1 : K) ^ 3) = -1 by norm_num]
    module
  have hc2 : ((2 : k) : K) = 2 := rfl
  have h2k : (2 : k) ≠ 0 := fun e => h2 (by
    have := congrArg (fun x : k => (x : K)) e
    simpa [hc2] using this)
  have hP' := W.sub_mem (h1 w hw) hw
  have hM' := W.sub_mem (hm1 w hw) hw
  have hi : ∀ v : RootModule .G2 K, ((2 : k)⁻¹ : k) • v = (2 : K)⁻¹ • v := fun v => by
    show (((2 : k)⁻¹ : k) : K) • v = _
    rw [Subfield.coe_inv, hc2]
  refine ⟨?_, ?_⟩
  · have := W.smul_mem ((2 : k)⁻¹) (W.add_mem hP' hM')
    rw [hi] at this
    convert this using 1
    rw [hP, hM]
    match_scalars <;> field_simp <;> ring
  · have := W.smul_mem ((2 : k)⁻¹) (W.sub_mem hP' hM')
    rw [hi] at this
    convert this using 1
    rw [hP, hM]
    match_scalars <;> field_simp <;> ring

variable (k : Subfield K) {R : Subgroup (adjointGroup .G2 K)}
  (hR : ∀ p < 12, ∀ c ∈ k, xp p c ∈ R)

include hR in
theorem mem_span_moveA (h2 : (2 : K) ≠ 0) {c : GIdx}
    (hc : Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1 ∈
      Submodule.span k (longOrbit R)) :
    ∀ c' ∈ moveListA c, Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c') 1 ∈
      Submodule.span k (longOrbit R) := by
  intro c' hc'
  have hxq : ∀ i : Fin (Tag.rank .G2), ∀ w ∈ Submodule.span k (longOrbit R),
      xCoeff .G2 K i 2 w ∈ Submodule.span k (longOrbit R) ∧
        (xCoeff .G2 K i 1 w + xCoeff .G2 K i 3 w) ∈ Submodule.span k (longOrbit R) :=
    fun i w hw => quad_of_stable h2 k _ (xCoeff .G2 K i) (xOp .G2 K i)
      (fun c => xOp_eq_sum_xCoeff i c) (xCoeff_zero i)
      (fun w hw => xOp_mem_span k hR i ⟨1, k.one_mem⟩ hw)
      (fun w hw => xOp_mem_span k hR i ⟨-1, k.neg_mem k.one_mem⟩ hw) hw
  have hyq : ∀ i : Fin (Tag.rank .G2), ∀ w ∈ Submodule.span k (longOrbit R),
      yCoeff .G2 K i 2 w ∈ Submodule.span k (longOrbit R) ∧
        (yCoeff .G2 K i 1 w + yCoeff .G2 K i 3 w) ∈ Submodule.span k (longOrbit R) :=
    fun i w hw => quad_of_stable h2 k _ (yCoeff .G2 K i) (yOp .G2 K i)
      (fun c => yOp_eq_sum_yCoeff i c) (yCoeff_zero i)
      (fun w hw => yOp_mem_span k hR i ⟨1, k.one_mem⟩ hw)
      (fun w hw => yOp_mem_span k hR i ⟨-1, k.neg_mem k.one_mem⟩ hw) hw
  obtain ⟨i, h⟩ := mem_moveListA.1 hc'
  rcases h with h | h | h | h
  · obtain ⟨z, hz0, hz2, hz⟩ := sumTarget_eq_some h
    refine single_mem_of_small h2 k hz0 hz2 ?_
    have := (hxq i _ hc).2
    rw [xCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i 1 c,
      xCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i 3 c] at this
    rcases hz with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · rwa [h1, h3, toVec_none, add_zero] at this
    · rwa [h1, h3, toVec_none, zero_add] at this
  · obtain ⟨z, hz0, hz2, hz⟩ := sumTarget_eq_some h
    refine single_mem_of_small h2 k hz0 hz2 ?_
    have := (hyq i _ hc).2
    rw [yCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i 1 c,
      yCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i 3 c] at this
    rcases hz with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · rwa [h1, h3, toVec_none, add_zero] at this
    · rwa [h1, h3, toVec_none, zero_add] at this
  · obtain ⟨z, hz, hz0, hz2⟩ := smallTarget_eq_some h
    refine single_mem_of_small h2 k hz0 hz2 ?_
    have := (hxq i _ hc).1
    rwa [xCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i 2 c, hz]
      at this
  · obtain ⟨z, hz, hz0, hz2⟩ := smallTarget_eq_some h
    refine single_mem_of_small h2 k hz0 hz2 ?_
    have := (hyq i _ hc).1
    rwa [yCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i 2 c, hz]
      at this

include hR in
theorem single_mem_spanA (h2 : (2 : K) ≠ 0) (b : Label .G2) :
    Finsupp.single b 1 ∈ Submodule.span k (longOrbit R) := by
  obtain ⟨c, rfl⟩ := surjective_toLabel (Tag.rootCertificate_check .G2) b
  refine mem_reachNA (P := fun c => Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1 ∈
      Submodule.span k (longOrbit R)) (fun c hc c' hc' => mem_span_moveA k hR h2 hc c' hc')
    3 longIdx ?_ c (mem_reachNA_three c)
  intro c hc
  simp only [longIdx, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hc
  obtain ⟨m, hm, rfl⟩ := hc
  rw [single_toLabel_inr]
  refine Submodule.subset_span ⟨1, R.one_mem, m.val, ?_, by rw [one_smul]⟩
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton]
  simpa using hm

end Action

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
