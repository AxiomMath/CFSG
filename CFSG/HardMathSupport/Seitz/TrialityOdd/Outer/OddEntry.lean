module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddSpan

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ8

variable {K : Type} [Field K]

@[expose] def RatAll (k : Subfield K) (y : RootModule d4 K) : Prop := ∀ l : Label d4, y l ∈ k

section Entry

variable {σ : K →+* K} {k : Subfield K} {R : Subgroup (adjointGroup d4 K)}

theorem single_mem_span (h : SpanHyp σ k R) (b : Label d4) :
    (Finsupp.single b (1 : K) : RootModule d4 K) ∈ Submodule.span k (longOrbit R) := by
  rcases b with j | ⟨γ, hγ⟩
  · have hj : j = nd 0 ∨ j = nd 1 ∨ j = nd 2 ∨ j = nd 3 := by
      fin_cases j
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr rfl))
    have e : (Finsupp.single (Sum.inl j : Label d4) (1 : K)) = hVec d4 K j := rfl
    rw [e]
    rcases hj with rfl | rfl | rfl | rfl
    · exact hVec_outer_mem_span h (.inl rfl)
    · exact hVec_outer_mem_span h (.inr (.inl rfl))
    · exact h2_mem_span h
    · exact hVec_outer_mem_span h (.inr (.inr rfl))
  · obtain ⟨p, hp, rfl⟩ := exists_pos_of_isRoot hγ
    rw [← rootVec_eq_single K hγ]
    exact rv_mem_span h hp

theorem jFormO_mem_of_span {y : RootModule d4 K} (hy : ∀ r ∈ R, ∀ p ∈ longPos,
      jFormO K (r • (rv p : RootModule d4 K)) y ∈ k)
    {x : RootModule d4 K} (hx : x ∈ Submodule.span k (longOrbit R)) : jFormO K x y ∈ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, p, hp, rfl⟩ := hx
    exact hy r hr p hp
  | zero => simp [k.zero_mem]
  | add x z _ _ hx hz =>
    rw [map_add, LinearMap.add_apply]
    exact k.add_mem hx hz
  | smul a x _ hx =>
    have : a • x = (a : K) • x := rfl
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact k.mul_mem a.2 hx

theorem jFormO_hVec_four (i : Fin d4.rank) (y : RootModule d4 K) :
    jFormO K (hVec d4 K i) y = (cartO i (nd 0) : K) * y (Sum.inl (nd 0)) +
      (cartO i (nd 1) : K) * y (Sum.inl (nd 1)) + (cartO i (nd 2) : K) * y (Sum.inl (nd 2)) +
      (cartO i (nd 3) : K) * y (Sum.inl (nd 3)) := by
  rw [jFormO_hVec_left]
  exact Fin.sum_univ_four _

theorem cartO_values :
    cartO (nd 0) (nd 0) = -2 ∧ cartO (nd 0) (nd 1) = 0 ∧ cartO (nd 0) (nd 2) = -1 ∧
    cartO (nd 0) (nd 3) = 0 ∧ cartO (nd 1) (nd 0) = 0 ∧ cartO (nd 1) (nd 1) = -2 ∧
    cartO (nd 1) (nd 2) = -1 ∧ cartO (nd 1) (nd 3) = 0 ∧ cartO (nd 2) (nd 0) = -1 ∧
    cartO (nd 2) (nd 1) = -1 ∧ cartO (nd 2) (nd 2) = -2 ∧ cartO (nd 2) (nd 3) = -1 ∧
    cartO (nd 3) (nd 0) = 0 ∧ cartO (nd 3) (nd 1) = 0 ∧ cartO (nd 3) (nd 2) = -1 ∧
    cartO (nd 3) (nd 3) = -2 := by
  decide +kernel

theorem ratAll_of_pairing (h : SpanHyp σ k R) (h2 : (2 : K) ≠ 0) {y : RootModule d4 K}
    (hy : ∀ r ∈ R, ∀ p ∈ longPos, jFormO K (r • (rv p : RootModule d4 K)) y ∈ k) :
    RatAll k y := by
  have hJ : ∀ x ∈ Submodule.span k (longOrbit R), jFormO K x y ∈ k := fun x hx =>
    jFormO_mem_of_span hy hx
  have hu : ∀ i : Fin d4.rank, i = nd 0 ∨ i = nd 1 ∨ i = nd 2 ∨ i = nd 3 →
      jFormO K (hVec d4 K i) y ∈ k := by
    rintro i (rfl | rfl | rfl | rfl)
    · exact hJ _ (hVec_outer_mem_span h (.inl rfl))
    · exact hJ _ (hVec_outer_mem_span h (.inr (.inl rfl)))
    · exact hJ _ (h2_mem_span h)
    · exact hJ _ (hVec_outer_mem_span h (.inr (.inr rfl)))
  have u0 := hu (nd 0) (.inl rfl)
  have u1 := hu (nd 1) (.inr (.inl rfl))
  have u2 := hu (nd 2) (.inr (.inr (.inl rfl)))
  have u3 := hu (nd 3) (.inr (.inr (.inr rfl)))
  obtain ⟨c00, c01, c02, c03, c10, c11, c12, c13, c20, c21, c22, c23, c30, c31, c32, c33⟩ :=
    cartO_values
  rw [jFormO_hVec_four, c00, c01, c02, c03] at u0
  rw [jFormO_hVec_four, c10, c11, c12, c13] at u1
  rw [jFormO_hVec_four, c20, c21, c22, c23] at u2
  rw [jFormO_hVec_four, c30, c31, c32, c33] at u3
  simp only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one, zero_mul] at u0 u1 u2 u3
  set y0 := y (Sum.inl (nd 0))
  set y1 := y (Sum.inl (nd 1))
  set y2 := y (Sum.inl (nd 2))
  set y3 := y (Sum.inl (nd 3))
  have h2k : (2 : K) ∈ k := by
    rw [← one_add_one_eq_two]
    exact k.add_mem k.one_mem k.one_mem
  have hy2 : y2 ∈ k := by
    have := k.sub_mem (k.add_mem (k.add_mem u0 u1) u3) (k.mul_mem h2k u2)
    convert this using 1
    ring
  have hinv : (2 : K)⁻¹ ∈ k := k.inv_mem h2k
  have hy0 : y0 ∈ k := by
    have := k.mul_mem hinv (k.neg_mem (k.add_mem u0 hy2))
    convert this using 1
    field_simp
    ring
  have hy1 : y1 ∈ k := by
    have := k.mul_mem hinv (k.neg_mem (k.add_mem u1 hy2))
    convert this using 1
    field_simp
    ring
  have hy3 : y3 ∈ k := by
    have := k.mul_mem hinv (k.neg_mem (k.add_mem u3 hy2))
    convert this using 1
    field_simp
    ring
  rintro (j | ⟨γ, hγ⟩)
  · have hj : j = nd 0 ∨ j = nd 1 ∨ j = nd 2 ∨ j = nd 3 := by
      fin_cases j
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr rfl))
    rcases hj with rfl | rfl | rfl | rfl <;> assumption
  · obtain ⟨q, hq, hqγ⟩ := exists_pos_of_isRoot (isRoot_neg_d4 hγ)
    have hmem := hJ _ (rv_mem_span h hq)
    have e : (rv q : RootModule d4 K) = rootVec d4 K (-γ) := by rw [rv, hqγ]
    rw [e, jFormO_rootVec_left] at hmem
    have hw := pmone_wtRoot (K := K) γ
    have h1 : coordAt γ y = (wtRoot γ : K) * ((wtRoot γ : K) * coordAt γ y) := by
      rw [← mul_assoc, hw.sq, one_mul]
    rw [← coordAt_eq hγ, h1]
    exact k.mul_mem (hw.mem k) hmem

@[expose] def ratAllSub (k : Subfield K) : Submodule k (RootModule d4 K) where
  carrier := {y | RatAll k y}
  add_mem' := fun {x y} hx hy l => by rw [Finsupp.add_apply]; exact k.add_mem (hx l) (hy l)
  zero_mem' := fun l => by simp [k.zero_mem]
  smul_mem' := fun a x hx l => by
    have : a • x = (a : K) • x := rfl
    rw [this, Finsupp.smul_apply, smul_eq_mul]
    exact k.mul_mem a.2 (hx l)

theorem ratAll_of_long (h : SpanHyp σ k R) (h2 : (2 : K) ≠ 0) (g : adjointGroup d4 K)
    (hg : ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r')) :
    ∀ x ∈ Submodule.span k (longOrbit R), RatAll k (g • x) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r', hr', b, hb, rfl⟩ := hx
    refine ratAll_of_pairing h h2 fun r hr p hp => ?_
    rw [jFormO_smul_left, ← mul_smul, ← mul_smul]
    obtain ⟨p', hp', hpp'⟩ := neg_long p hp
    have hneg : d4Root p = -d4Root p' := neg_eq_iff_eq_neg.1 hpp'.symm
    rw [rv, jFormO_rootVec_left' hneg]
    exact k.mul_mem ((pmone_wtRoot (K := K) _).mem k) (hg r⁻¹ (R.inv_mem hr) r' hr' b hb p' hp')
  | zero =>
    rw [smul_zero]
    exact (ratAllSub k).zero_mem
  | add x z _ _ hx hz =>
    rw [smul_add]
    exact (ratAllSub k).add_mem hx hz
  | smul a x _ hx =>
    have : g • (a • x) = a • (g • x) := smul_smul_comm' g (a : K) x
    rw [this]
    exact (ratAllSub k).smul_mem a hx

theorem longEntries_of_hcon_odd (h : SpanHyp σ k R) (g : adjointGroup d4 K)
    (hcon : ∀ r ∈ R, ∀ r' ∈ R,
      coordAt (d4Root 23) ((r * g * r') • (rv 22 : RootModule d4 K)) ∈ k) :
    ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r') := by
  intro r hr r' hr' σ hσ τ hτ
  obtain ⟨mσ, hmσ, e1, he1, hσ7⟩ := reach_long_odd h σ hσ
  obtain ⟨τ', hτ', hττ'⟩ := neg_long τ hτ
  obtain ⟨mτ, hmτ, e2, he2, hτ7⟩ := reach_long_odd h τ' hτ'
  have h1 := hcon (mτ⁻¹ * r) (R.mul_mem (R.inv_mem hmτ) hr) (r' * mσ) (R.mul_mem hr' hmσ)
  have hneg : d4Root τ' = -d4Root τ := hττ'
  set y : RootModule d4 K := (r * g * r') • (rv σ : RootModule d4 K) with hy
  have hrvσ : (rv σ : RootModule d4 K) = e1 • (mσ • (rv 22 : RootModule d4 K)) := by
    rw [hσ7, smul_smul, he1.sq, one_smul]
  have hrvτ : (rv τ' : RootModule d4 K) = e2 • (mτ • (rv 22 : RootModule d4 K)) := by
    rw [hτ7, smul_smul, he2.sq, one_smul]
  have hw : y = e1 • ((r * g * r' * mσ) • (rv 22 : RootModule d4 K)) := by
    rw [hy, hrvσ, smul_smul_comm', mul_smul (r * g * r') mσ]
  have s1 : coordAt (d4Root τ) y = (wtRoot (d4Root τ) : K) *
      jFormO K (rv τ' : RootModule d4 K) y := by
    rw [rv, jFormO_rootVec_left' hneg, ← mul_assoc, (pmone_wtRoot (K := K) _).sq, one_mul]
  have s2 : jFormO K (rv τ' : RootModule d4 K) y =
      e2 * jFormO K (rv 22 : RootModule d4 K) (mτ⁻¹ • y) := by
    rw [hrvτ, map_smul (jFormO K) e2 (mτ • (rv 22 : RootModule d4 K)), LinearMap.smul_apply,
      smul_eq_mul, jFormO_smul_left]
  have s3 : ∀ z : RootModule d4 K, jFormO K (rv 22 : RootModule d4 K) z =
      (wtRoot (d4Root 23) : K) * coordAt (d4Root 23) z := by
    intro z
    exact jFormO_rootVec_left' (by rw [d4Root_23, neg_neg]) z
  have e : mτ⁻¹ * (r * g * r' * mσ) = mτ⁻¹ * r * g * (r' * mσ) := by group
  have h2 : coordAt (d4Root τ) y = (wtRoot (d4Root τ) : K) * (e2 * ((wtRoot (d4Root 23) : K) *
      (e1 * coordAt (d4Root 23) ((mτ⁻¹ * r * g * (r' * mσ)) • (rv 22 : RootModule d4 K))))) := by
    rw [s1, s2, s3, hw, smul_smul_comm', coordAt_smul, ← mul_smul, e]
  rw [h2]
  exact k.mul_mem ((pmone_wtRoot (K := K) _).mem k) (k.mul_mem (he2.mem k)
    (k.mul_mem ((pmone_wtRoot (K := K) _).mem k) (k.mul_mem (he1.mem k) h1)))

theorem ratAll_of_hcon (h : SpanHyp σ k R) (h2 : (2 : K) ≠ 0) (g : adjointGroup d4 K)
    (hcon : ∀ r ∈ R, ∀ r' ∈ R,
      coordAt (d4Root 23) ((r * g * r') • (rv 22 : RootModule d4 K)) ∈ k) (b : Label d4) :
    RatAll k (g • (Finsupp.single b (1 : K) : RootModule d4 K)) :=
  ratAll_of_long h h2 g (longEntries_of_hcon_odd h g hcon) _ (single_mem_span h b)

end Entry

end CFSG.HardMathSupport.Seitz.TrialityOdd
