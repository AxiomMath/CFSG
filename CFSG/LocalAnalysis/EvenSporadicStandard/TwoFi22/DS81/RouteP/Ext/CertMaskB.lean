module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.MaskDual

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu Certificates.RouteP.M24Defect

@[expose] def dz (d : ℕ → ℕ) (κ : ℕ) : ZMod 2 :=
  if (d (κ / 11)).testBit (κ % 11) then 1 else 0

private theorem list_range_toFinset (n : ℕ) : (List.range n).toFinset = Finset.range n := by
  ext a
  simp

private theorem list_sum_range (n : ℕ) (g : ℕ → ZMod 2) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  rw [← List.sum_toFinset g (List.nodup_range (n := n)), list_range_toFinset]

private theorem list_filter_map_sum {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    (l : List α) (hnd : l.Nodup) (p : α → Bool) (g : α → M) :
    ((l.filter p).map g).sum = ∑ x ∈ l.toFinset, if p x then g x else 0 := by
  rw [← List.sum_toFinset g (hnd.filter p), List.toFinset_filter, Finset.sum_filter]

private theorem ite_one_smul {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (b : Bool) (v : M) : (if b then (1 : ZMod 2) else 0) • v = if b then v else 0 := by
  cases b <;> simp

private theorem unitMask_mul_add_self (i c : ℕ) (hc : c < 11) :
    unitMask (11 * i + c) i = 2 ^ c := by
  have hdiv : (11 * i + c) / 11 = i := by omega
  have hmod : (11 * i + c) % 11 = c := by omega
  simp [unitMask, hdiv, hmod]

private theorem unitMask_mul_add_ne {b i c : ℕ} (h : b ≠ i) (hc : c < 11) :
    unitMask (11 * b + c) i = 0 := by
  have hdiv : (11 * b + c) / 11 = b := by omega
  simp [unitMask, hdiv, h]

private theorem dz_mul_add (d : ℕ → ℕ) (i c : ℕ) (hc : c < 11) :
    dz d (11 * i + c) = if (d i).testBit c then (1 : ZMod 2) else 0 := by
  have hdiv : (11 * i + c) / 11 = i := by omega
  have hmod : (11 * i + c) % 11 = c := by omega
  simp only [dz, hdiv, hmod]

theorem pair_row_eq (f : List ℕ) (d : ℕ → ℕ) :
    ((List.range 7).map fun i => bp (f[i]!) (d i)).sum =
      ∑ κ ∈ Finset.range 77, (if fbit f κ = true then (1 : ZMod 2) else 0) * dz d κ := by
  have hAB : ((List.range 7).map fun i => bp (f[i]!) (d i)).sum =
      ∑ i ∈ Finset.range 7, bp (f[i]!) (d i) := list_sum_range 7 _
  have hBC : (∑ i ∈ Finset.range 7, bp (f[i]!) (d i)) =
      ∑ i ∈ Finset.range 7, ∑ c ∈ Finset.range 11,
        (if (f[i]!).testBit c then (1 : ZMod 2) else 0) *
          (if (d i).testBit c then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bp_eq_sum]
  have hCD : (∑ i ∈ Finset.range 7, ∑ c ∈ Finset.range 11,
        (if (f[i]!).testBit c then (1 : ZMod 2) else 0) *
          (if (d i).testBit c then (1 : ZMod 2) else 0)) =
      ∑ i ∈ Finset.range 7, ∑ c ∈ Finset.range 11,
        (if fbit f (11 * i + c) = true then (1 : ZMod 2) else 0) *
          dz d (11 * i + c) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_congr rfl fun c hc => ?_
    have hi7 : i < 7 := Finset.mem_range.mp hi
    have hc11 : c < 11 := Finset.mem_range.mp hc
    have hdiv : (11 * i + c) / 11 = i := by omega
    have hmod : (11 * i + c) % 11 = c := by omega
    rw [fbit, dz, hdiv, hmod]
  have hDE : (∑ i ∈ Finset.range 7, ∑ c ∈ Finset.range 11,
        (if fbit f (11 * i + c) = true then (1 : ZMod 2) else 0) *
          dz d (11 * i + c)) =
      ∑ κ ∈ Finset.range 77, (if fbit f κ = true then (1 : ZMod 2) else 0) * dz d κ := by
    rw [show (77 : ℕ) = 7 * 11 from rfl, sum_range_mul]
  exact hAB.trans (hBC.trans (hCD.trans hDE))

theorem lamApply_sum (S : List (ℕ × ℕ)) (L : List ℕ) (i : ℕ) :
    lamApply (xorMasks (L.map fun κ => (S[κ]!).1), xorMasks (L.map fun κ => (S[κ]!).2)) i =
      xorMasks (L.map fun κ => lamApply (S[κ]!) i) := by
  induction L with
  | nil => simp [xorMasks, lamApply_zero]
  | cons κ L ih =>
    simp only [List.map_cons, xorMasks]
    rw [lamApply_xor (S[κ]!) (xorMasks (List.map (fun κ => (S[κ]!).1) L),
      xorMasks (List.map (fun κ => (S[κ]!).2) L)) i, ih]

theorem bvec_unit_sum (d : ℕ → ℕ) (i : ℕ) (hi : i < 7) :
    ∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (unitMask κ i) = bvec 11 (d i) := by
  rw [show (77 : ℕ) = 7 * 11 from rfl, sum_range_mul]
  have hsingle : (∑ b ∈ Finset.range 7, ∑ c ∈ Finset.range 11,
        dz d (11 * b + c) • bvec 11 (unitMask (11 * b + c) i)) =
      ∑ c ∈ Finset.range 11,
        dz d (11 * i + c) • bvec 11 (unitMask (11 * i + c) i) :=
    Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi) (fun b _ hbi => by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [unitMask_mul_add_ne hbi (Finset.mem_range.mp hc)]
      simp [bvec_zero])
  rw [hsingle, bvec_eq_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [dz_mul_add d i c (Finset.mem_range.mp hc),
    unitMask_mul_add_self i c (Finset.mem_range.mp hc), ite_one_smul]

theorem bezoutOK_spec {Fs : List (List ℕ)} {S : List (ℕ × ℕ)} {T : List (List ℕ)}
    (h : bezoutOK Fs S T = true) :
    Fs.length = 67 ∧ S.length = 77 ∧ T.length = 67 ∧ (∀ t ∈ T, t.length = 7) ∧
      ∀ κ < 77, ∀ i < 7,
        (lamApply S[κ]! i ^^^
          xorMasks (((List.range 67).filter fun r => fbit Fs[r]! κ).map fun r => (T[r]!)[i]!)) =
          unitMask κ i := by
  simp only [bezoutOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, _hD⟩, hE⟩, hF⟩ := h
  exact ⟨hA, hB, hC, hE, hF⟩

theorem exists_lam_of_bezout (Fs : List (List ℕ)) (S : List (ℕ × ℕ)) (T : List (List ℕ))
    (hB : bezoutOK Fs S T = true) (d : ℕ → ℕ)
    (hF : ∀ r < 67, ((List.range 7).map fun i => bp ((Fs[r]!)[i]!) (d i)).sum = 0) :
    ∃ z : ℕ × ℕ, ∀ i < 7, bvec 11 (d i) = bvec 11 (lamApply z i) := by
  have hspec := bezoutOK_spec hB
  have hid : ∀ κ < 77, ∀ i < 7, (lamApply S[κ]! i ^^^
        xorMasks (((List.range 67).filter fun r => fbit Fs[r]! κ).map
          fun r => (T[r]!)[i]!)) = unitMask κ i := hspec.2.2.2.2
  let L : List ℕ := (List.range 77).filter fun κ => (d (κ / 11)).testBit (κ % 11)
  let z : ℕ × ℕ := (xorMasks (L.map fun κ => (S[κ]!).1),
    xorMasks (L.map fun κ => (S[κ]!).2))
  refine ⟨z, fun i hi => ?_⟩
  let X : ℕ → ℕ := fun κ => xorMasks (((List.range 67).filter
    fun r => fbit Fs[r]! κ).map fun r => (T[r]!)[i]!)
  have hXeq : ∀ κ < 77, bvec 11 (lamApply (S[κ]!) i) =
      bvec 11 (unitMask κ i) + bvec 11 (X κ) := by
    intro κ hκ
    have h := congrArg (bvec 11) (hid κ hκ i hi)
    rw [bvec_xor] at h
    rw [← h]
    exact (CharTwo.add_cancel_right _ _).symm
  have hXbvec : ∀ κ, bvec 11 (X κ) =
      ∑ r ∈ Finset.range 67,
        (if fbit Fs[r]! κ = true then (1 : ZMod 2) else 0) • bvec 11 ((T[r]!)[i]!) := by
    intro κ
    show bvec 11 (xorMasks (((List.range 67).filter fun r => fbit Fs[r]! κ).map
        fun r => (T[r]!)[i]!)) =
      ∑ r ∈ Finset.range 67,
        (if fbit Fs[r]! κ = true then (1 : ZMod 2) else 0) • bvec 11 ((T[r]!)[i]!)
    rw [bvec_xorMasks, List.map_map]
    simp only [Function.comp_def]
    rw [list_filter_map_sum (List.range 67) (List.nodup_range (n := 67))
      (fun r => fbit Fs[r]! κ) (fun r => bvec 11 ((T[r]!)[i]!))]
    rw [list_range_toFinset]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Function.comp_apply, ite_one_smul]
  have hXsum : (∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (X κ)) = 0 := by
    simp_rw [hXbvec]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    simp_rw [smul_smul]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [← Finset.sum_smul]
    have hr67 : r < 67 := Finset.mem_range.mp hr
    have hscalar : (∑ κ ∈ Finset.range 77,
        dz d κ * (if fbit Fs[r]! κ = true then (1 : ZMod 2) else 0)) = 0 := by
      rw [Finset.sum_congr rfl (fun κ _ => mul_comm (dz d κ) _)]
      rw [← pair_row_eq (Fs[r]!) d, hF r hr67]
    rw [hscalar, zero_smul]
  have hz1 : lamApply z i = xorMasks (L.map fun κ => lamApply (S[κ]!) i) := by
    show lamApply (xorMasks (L.map fun κ => (S[κ]!).1),
        xorMasks (L.map fun κ => (S[κ]!).2)) i =
      xorMasks (L.map fun κ => lamApply (S[κ]!) i)
    rw [lamApply_sum]
  have hz2 : bvec 11 (xorMasks (L.map fun κ => lamApply (S[κ]!) i)) =
      ∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (lamApply (S[κ]!) i) := by
    show bvec 11 (xorMasks (((List.range 77).filter
        fun κ => (d (κ / 11)).testBit (κ % 11)).map fun κ => lamApply (S[κ]!) i)) =
      ∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (lamApply (S[κ]!) i)
    rw [bvec_xorMasks, List.map_map]
    simp only [Function.comp_def]
    rw [list_filter_map_sum (List.range 77) (List.nodup_range (n := 77))
      (fun κ => (d (κ / 11)).testBit (κ % 11)) (fun κ => bvec 11 (lamApply (S[κ]!) i))]
    rw [list_range_toFinset]
    refine Finset.sum_congr rfl fun κ _ => ?_
    simp only [Function.comp_apply, dz, ite_one_smul]
  have h1 : bvec 11 (d i) = ∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (unitMask κ i) :=
    (bvec_unit_sum d i hi).symm
  have h2 : (∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (lamApply (S[κ]!) i)) =
      ∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (unitMask κ i) := by
    have hstep : ∀ κ ∈ Finset.range 77,
        dz d κ • bvec 11 (lamApply (S[κ]!) i) =
          dz d κ • bvec 11 (unitMask κ i) + dz d κ • bvec 11 (X κ) := by
      intro κ hκ
      rw [hXeq κ (Finset.mem_range.mp hκ), smul_add]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hXsum, add_zero]
  have hz : bvec 11 (lamApply z i) =
      ∑ κ ∈ Finset.range 77, dz d κ • bvec 11 (lamApply (S[κ]!) i) := by
    rw [hz1, hz2]
  exact h1.trans (h2.symm.trans hz.symm)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
