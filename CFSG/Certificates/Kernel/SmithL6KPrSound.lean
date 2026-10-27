module

public import CFSG.Certificates.Kernel.SmithL6KWSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (tri applyCols)

theorem tvCols_invol {k : Nat} (hk : k < 1953) :
    ∀ x < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols k) x) = x := by
  refine xorAdd_ext (G := fun x => x) (fun a b => by simp only [applyCols_xorL])
    (fun a b => rfl) 20 ?_
  intro m hm
  obtain ⟨h0, h1, h2⟩ := tri_lt6 m hm
  rw [applyCols_powL _ (by rw [tvCols_size]; exact hm), tvCols_get hm,
    tvCols_wedge3 k (tvApply_lt hk (pow_lt64 h0)) (tvApply_lt hk (pow_lt64 h1))
      (tvApply_lt hk (pow_lt64 h2)), tvApply_tvApply hk, tvApply_tvApply hk, tvApply_tvApply hk,
    wedge3_tri m hm]

theorem tvApply_inj {k : Nat} (hk : k < 1953) : Function.Injective (tvApply k) :=
  Function.LeftInverse.injective (g := tvApply k) fun x => tvApply_tvApply hk x

theorem closeRow_facts {g R W M : Nat} (hg : g < 1953) (hW : ∀ i < 1395, fldW 20 W i = wt i)
    (hM : ∀ i < 1395, fldW 64 M i = wMask i)
    (h : closeRowK (tvCols g).toList (codeOf (tvPair g)) R W M = true) :
    ∀ i < 1395, fldW 11 R i < 1395 ∧ wt (fldW 11 R i) = applyCols (tvCols g) (wt i) ∧
      setM (wMask (fldW 11 R i)) = (setM (wMask i)).image (tvApply g) := by
  intro i hi
  unfold closeRowK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hj, hw⟩, hm⟩ := h i hi
  refine ⟨hj, ?_, ?_⟩
  · rw [← hW _ hj, hw, hW i hi, ← applyCols_toArray, Array.toArray_toList]
  · rw [← hM _ hj, hm, hM i hi, setM_imgMaskK (tvP_tvPair hg)]
    exact congrArg (fun f => Finset.image f (setM (wMask i)))
      (funext fun x => (tvApply_eq_tvA g x).symm)

theorem opp_of_reach {G : List Nat} {R : Nat → Nat → Nat} (hG : ∀ s < G.length, G.getD s 0 < 1953)
    (hRlt : ∀ s < G.length, ∀ i < 1395, R s i < 1395)
    (hRw : ∀ s < G.length, ∀ i < 1395, wt (R s i) = applyCols (tvCols (G.getD s 0)) (wt i))
    (hRm : ∀ s < G.length, ∀ i < 1395,
      setM (wMask (R s i)) = (setM (wMask i)).image (tvApply (G.getD s 0)))
    (hF : ∀ s < G.length, FormInv (G.getD s 0))
    (hinj : ∀ i < 1395, ∀ j < 1395, wt i = wt j → i = j)
    (hP : Reach 1395 G.length (· == 0) (fun s u v => R s u == v))
    (h0 : ∀ j < 1395, fB (wt 0) (wt j) = decide ((setM (wMask 0) ∩ setM (wMask j)).card = 1)) :
    ∀ i < 1395, ∀ j < 1395,
      fB (wt i) (wt j) = decide ((setM (wMask i) ∩ setM (wMask j)).card = 1) := by
  refine hP _ (fun v _ hv => by rw [beq_iff_eq.mp hv]; exact h0) ?_
  intro s hs u hu v _ he hQ j hj
  rw [← beq_iff_eq.mp he]
  have hg := hG s hs
  have hj0 := hRlt s hs j hj
  have hjj : R s (R s j) = j := hinj _ (hRlt s hs _ hj0) _ hj (by
    rw [hRw s hs _ hj0, hRw s hs j hj, tvCols_invol hg _ (wt_lt20K j)])
  rw [← hjj, hRw s hs u hu, hRw s hs _ hj0, hF s hs _ (wt_lt20K u) _ (wt_lt20K _), hQ _ hj0,
    hRm s hs u hu, hRm s hs _ hj0, ← Finset.image_inter _ _ (tvApply_inj hg),
    Finset.card_image_of_injective _ (tvApply_inj hg)]

theorem testBit_ge64 {x n : Nat} (hx : x < 2 ^ 64) (hn : 64 ≤ n) : x.testBit n = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hn))

theorem eq_of_setM_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : setM x = setM y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 64
  · have e : n ∈ setM x ↔ n ∈ setM y := by rw [h]
    rw [mem_setM, mem_setM] at e
    cases hxn : x.testBit n <;> cases hyn : y.testBit n
    · rfl
    · exact absurd (e.mpr ⟨hn, hyn⟩).2 (by rw [hxn]; decide)
    · exact absurd (e.mp ⟨hn, hxn⟩).2 (by rw [hyn]; decide)
    · rfl
  · rw [testBit_ge64 hx (by omega), testBit_ge64 hy (by omega)]

theorem beq_one_iff {M : Nat} (hM : M < 2 ^ 64) (h0 : M.testBit 0 = true) :
    (M == 1) = decide ((setM M).card = 1) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff]
  constructor
  · rintro rfl
    decide
  · intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have h0m : 0 ∈ setM M := mem_setM.mpr ⟨by decide, h0⟩
    rw [ha, Finset.mem_singleton] at h0m
    subst h0m
    have h1 : setM 1 = {0} := by decide
    exact eq_of_setM_eq hM (by decide) (by rw [ha, h1])

end CFSG.SmithL6.K
