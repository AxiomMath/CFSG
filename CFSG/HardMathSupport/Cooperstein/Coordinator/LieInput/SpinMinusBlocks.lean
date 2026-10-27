module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusFin
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.MatLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUEmbed
public import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbedding.LeviBlock

section ARun

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

@[expose] def runNodes (n a b : ℕ) : Set (Fin (n - 1)) := {j | a ≤ j.val ∧ j.val ≤ b}

theorem ofStdB_pair {m : ℕ} (i j k : Fin m) (hij : i ≠ j) :
    ofStdB m (Pi.single i (boolSign true) + Pi.single j (boolSign false)) k =
      (if i.val ≤ k.val then 1 else 0) - (if j.val ≤ k.val then 1 else 0) := by
  simp only [ofStdB, Pi.add_apply, Pi.single_apply, boolSign_true, boolSign_false]
  have key : ∀ x : Fin m, (if x.val ≤ k.val then ((if x = i then (1 : ℤ) else 0) +
      if x = j then -1 else 0) else 0) =
      (if x = i then (if i.val ≤ k.val then (1 : ℤ) else 0) else 0) -
        (if x = j then (if j.val ≤ k.val then (1 : ℤ) else 0) else 0) := by
    intro x
    rcases eq_or_ne x i with rfl | h1
    · have h2 : x ≠ j := hij
      simp [h2]
    · rcases eq_or_ne x j with rfl | h2
      · simp [h1]
        split_ifs <;> simp
      · simp [h1, h2]
  simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]


variable {lo hi : ℕ} (hlh : lo ≤ hi) (hhi : hi + 2 < n)

include hlh hhi

@[expose] def runCoord (u : Fin (hi - lo + 2)) : Fin (n - 1) :=
  ⟨lo + u.val, by have := u.isLt; omega⟩

theorem runCoord_injective : Function.Injective (runCoord (n := n) hlh hhi) := by
  intro u v h
  have := congrArg Fin.val h
  simp only [runCoord] at this
  exact Fin.ext (by omega)

@[expose] noncomputable def runIdx (hn1 : 1 ≤ n) (u : Fin (hi - lo + 2)) : Fin (n + n) :=
  epsM n hn1 (minusPos n (runCoord hlh hhi u) true)

theorem runIdx_injective (hn1 : 1 ≤ n) : Function.Injective (runIdx (n := n) hlh hhi hn1) := by
  intro u v h
  apply runCoord_injective hlh hhi
  have := (epsM n hn1).injective h
  exact ((minusPos_inj n).mp this).1

theorem runIdx_disj (hn1 : 1 ≤ n) (u v : Fin (hi - lo + 2)) :
    runIdx hlh hhi hn1 u ≠ Fin.rev (runIdx hlh hhi hn1 v) := by
  intro h
  unfold runIdx at h
  have h2 : Fin.rev (epsM n hn1 (minusPos n (runCoord hlh hhi v) true)) =
      epsM n hn1 (minusPos n (runCoord hlh hhi v) false) := by
    simpa using (epsM_not n hn1 (runCoord hlh hhi v) true).symm
  rw [h2] at h
  have := (minusPos_inj n).mp ((epsM n hn1).injective h)
  simp at this


@[expose] noncomputable def runMu (hn1 : 1 ≤ n) : Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F →*
    Matrix (Fin (n + n)) (Fin (n + n)) F where
  toFun := levMat (RingEquiv.refl F) (runIdx_injective hlh hhi hn1)
  map_one' := levMat_one _
  map_mul' := levMat_mul _ (runIdx_disj hlh hhi hn1)

theorem runMu_injective (hn1 : 1 ≤ n) : Function.Injective (runMu (F := F) hlh hhi hn1) := by
  intro g h hgh
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F,
      (runMu hlh hhi hn1 g).submatrix (runIdx hlh hhi hn1) (runIdx hlh hhi hn1) =
        (g : Matrix (Fin (hi - lo + 2)) (Fin (hi - lo + 2)) F) := by
    intro g
    ext i j
    have haj : runIdx hlh hhi hn1 j ∉ Set.range (Fin.rev ∘ runIdx hlh hhi hn1) :=
      fun ⟨k, hk⟩ => runIdx_disj hlh hhi hn1 j k hk.symm
    simp only [Matrix.submatrix_apply]
    show levMat (RingEquiv.refl F) (runIdx_injective hlh hhi hn1) g
      (runIdx hlh hhi hn1 i) (runIdx hlh hhi hn1 j) = _
    unfold levMat
    rw [Matrix.mul_apply, Finset.sum_eq_single (runIdx hlh hhi hn1 j)]
    · rw [extendMat_apply_map (runIdx_injective hlh hhi hn1),
        extendMat_apply_of_not_mem _ _ (Or.inr haj)]
      simp
    · intro t _ ht
      rw [extendMat_apply_of_not_mem _ _ (Or.inr haj), Matrix.one_apply_ne ht, mul_zero]
    · simp
  have h2 := congrArg (fun A => A.submatrix (runIdx hlh hhi hn1) (runIdx hlh hhi hn1)) hgh
  simp only [key] at h2
  exact Subtype.ext h2

theorem run_matM_longRoot (hn1 : 1 ≤ n) {u v : Fin (hi - lo + 2)} (huv : u ≠ v) (x : F)
    (hij : runCoord hlh hhi u ≠ runCoord hlh hhi v) :
    matM hn1 ((minusFrame n b c).longRoot hij true false (.ofAdd x)) =
      rootMatrix (RingEquiv.refl F) (runIdx hlh hhi hn1 u) (runIdx hlh hhi hn1 v) x := by
  rw [matM_longRoot hn1 hij true false x]
  rfl

theorem run_E1 (hn : 4 ≤ n) (hn1 : 1 ≤ n) (g : Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F) :
    ∃ t ∈ leviM (minusDatum n hirr) (runNodes n lo hi), matM hn1 t = runMu hlh hhi hn1 g := by
  classical
  have hct := minusDatum_isCTGroupDatum n hirr hn
  have hg : g ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin (hi - lo + 2)) F →
        Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top _
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨u, v, huv, cc⟩ := t
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    have hij : runCoord hlh hhi u ≠ runCoord hlh hhi v := fun h =>
      huv (runCoord_injective hlh hhi h)
    set i := runCoord hlh hhi u with hi_def
    set j := runCoord hlh hhi v with hj_def
    set γ : Fin (n - 1) → ℤ := ofStdB (n - 1)
      (Pi.single i (boolSign true) + Pi.single j (boolSign false)) with hγ
    have h : toStdB (n - 1) γ = Pi.single i (boolSign true) + Pi.single j (boolSign false) :=
      toStdB_ofStdB (n - 1) _
    refine ⟨(minusFrame n b c).longRoot hij true false (.ofAdd cc), ?_, ?_⟩
    · refine rootGroup_le_leviM hct (mem_roots_of_toStdB_eq_long n hij true false h)
        (fun k hk => ?_) (longRoot_mem_minusRootGroup n hirr hij true false h cc)
      rw [hγ, ofStdB_pair i j k hij]
      have hu := u.isLt
      have hv := v.isLt
      have hk' : k.val < lo ∨ hi < k.val := by
        by_contra hcon
        exact hk ⟨by omega, by omega⟩
      simp only [hi_def, hj_def, runCoord]
      split_ifs <;> omega
    · rw [run_matM_longRoot hlh hhi hn1 huv cc hij]
      show _ = levMat (RingEquiv.refl F) (runIdx_injective hlh hhi hn1) _
      rw [levMat_transvection _ (runIdx_disj hlh hhi hn1)]
  | one => exact ⟨1, one_mem _, by rw [map_one, map_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t1, h1, e1⟩ := hx
    obtain ⟨t2, h2, e2⟩ := hy
    exact ⟨t1 * t2, mul_mem h1 h2, by rw [map_mul, map_mul, e1, e2]⟩
  | inv x _ hx =>
    obtain ⟨t, ht, e⟩ := hx
    refine ⟨t⁻¹, inv_mem ht, ?_⟩
    have h1 : runMu hlh hhi hn1 x * runMu hlh hhi hn1 x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    calc matM hn1 t⁻¹ = matM hn1 t⁻¹ * (runMu hlh hhi hn1 x * runMu hlh hhi hn1 x⁻¹) := by
          rw [h1, mul_one]
      _ = (matM hn1 t⁻¹ * matM hn1 t) * runMu hlh hhi hn1 x⁻¹ := by rw [← e, mul_assoc]
      _ = runMu hlh hhi hn1 x⁻¹ := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]


theorem run_E2 (hn1 : 1 ≤ n) :
    leviM (minusDatum n hirr) (runNodes n lo hi) ≤
      liftImage (matM (b := b) (c := c) hn1) (runMu hlh hhi hn1) := by
  refine iSup₂_le fun i hi' => ?_
  have hk : i.val + 1 < n - 1 := by have := hi'.2; omega
  have hlo := hi'.1
  have hhi' := hi'.2
  let u : Fin (hi - lo + 2) := ⟨i.val - lo, by omega⟩
  let v : Fin (hi - lo + 2) := ⟨i.val + 1 - lo, by omega⟩
  have huv : u ≠ v := fun h => by have := congrArg Fin.val h; simp [u, v] at this; omega
  have hcu : runCoord hlh hhi u = i := Fin.ext (by simp [runCoord, u]; omega)
  have hcv : runCoord hlh hhi v = ⟨i.val + 1, hk⟩ := Fin.ext (by simp [runCoord, v]; omega)
  have hiu : runIdx hlh hhi hn1 u = epsM n hn1 (minusPos n i true) := by
    simp only [runIdx]; rw [hcu]
  have hiv : runIdx hlh hhi hn1 v = epsM n hn1 (minusPos n ⟨i.val + 1, hk⟩ true) := by
    simp only [runIdx]; rw [hcv]
  unfold rankOne
  refine sup_le ?_ ?_
  · refine (le_of_eq (minusRootGroup_single_of_lt n hirr hk)).trans ?_
    rintro _ ⟨m, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.transvection huv (Multiplicative.toAdd m), ?_⟩
    show levMat (RingEquiv.refl F) (runIdx_injective hlh hhi hn1) _ = _
    rw [levMat_transvection _ (runIdx_disj hlh hhi hn1), hiu, hiv]
    have := matM_longRoot (b := b) (c := c) hn1 (succ_ne_of_lt n hk) true false (Multiplicative.toAdd m)
    simp only [Bool.not_false, ofAdd_toAdd] at this
    exact this.symm
  · refine (le_of_eq (minusRootGroup_neg_single_of_lt n hirr hk)).trans ?_
    rintro _ ⟨m, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.transvection huv.symm (Multiplicative.toAdd m), ?_⟩
    show levMat (RingEquiv.refl F) (runIdx_injective hlh hhi hn1) _ = _
    rw [levMat_transvection _ (runIdx_disj hlh hhi hn1), hiu, hiv]
    have := matM_longRoot (b := b) (c := c) hn1 (succ_ne_of_lt n hk).symm true false (Multiplicative.toAdd m)
    simp only [Bool.not_false, ofAdd_toAdd] at this
    exact this.symm

@[expose] noncomputable def chEquivMinus (hn : 4 ≤ n) :
    Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F ≃*
      ↥(leviM (minusDatum n hirr) (runNodes n lo hi)) :=
  matLiftEquiv (matM (b := b) (c := c) (by omega : 1 ≤ n)) (runMu hlh hhi (by omega : 1 ≤ n))
    (leviM (minusDatum n hirr) (runNodes n lo hi)) (matM_injective hirr _)
    (run_E1 hirr hlh hhi hn (by omega)) (runMu_injective hlh hhi _) (run_E2 hirr hlh hhi _)

end ARun


end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
