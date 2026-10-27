module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

section One

theorem succ_zero_eq_zero_of_mem_flagStabilizer_one {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ flagStabilizer 3 K ({1} : Set ℕ)) (a : Fin 2) :
    (g : Matrix (Fin 3) (Fin 3) K) (Fin.succ a) 0 = 0 := by
  have hg1 : g ∈ stabilizer (flagSpace 3 K 1) := (mem_flagStabilizer.mp hg) 1 (by simp)
  have hmap : (flagSpace 3 K 1).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) =
      flagSpace 3 K 1 := mem_stabilizer.mp hg1
  have hv : (Pi.single (0 : Fin 3) (1 : K) : Fin 3 → K) ∈ flagSpace 3 K 1 := by
    rw [mem_flagSpace]
    intro j hj
    exact Pi.single_eq_of_ne (by omega) 1
  have hmem : mulVecLin (g : Matrix (Fin 3) (Fin 3) K) (Pi.single 0 1) ∈ flagSpace 3 K 1 := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hv
  have h0 := (mem_flagSpace.mp hmem) (Fin.succ a) (by simp)
  rwa [mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] at h0

@[expose] def leviBlockOne (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun a b => M (Fin.succ a) (Fin.succ b)

theorem leviBlockOne_apply (M : Matrix (Fin 3) (Fin 3) K) (a b : Fin 2) :
    leviBlockOne M a b = M (Fin.succ a) (Fin.succ b) := by
  rw [leviBlockOne, Matrix.of_apply]

theorem leviBlockOne_mul {g h : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ flagStabilizer 3 K ({1} : Set ℕ)) :
    leviBlockOne ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      leviBlockOne (g : Matrix (Fin 3) (Fin 3) K) *
        leviBlockOne (h : Matrix (Fin 3) (Fin 3) K) := by
  ext a b
  simp only [leviBlockOne_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Fin.sum_univ_succ, succ_zero_eq_zero_of_mem_flagStabilizer_one hg a, zero_mul, zero_add]

@[expose] def leviOneHom (K : Type) [Field K] :
    ↥(flagStabilizer 3 K ({1} : Set ℕ)) →* Matrix (Fin 2) (Fin 2) K where
  toFun g := leviBlockOne (g.1 : Matrix (Fin 3) (Fin 3) K)
  map_one' := by
    show leviBlockOne (1 : Matrix (Fin 3) (Fin 3) K) = 1
    ext a b
    simp only [leviBlockOne, Matrix.of_apply, Matrix.one_apply, Fin.succ_inj]
  map_mul' g h := leviBlockOne_mul g.2

@[expose] def leviOne (K : Type) [Field K] :
    ↥(flagStabilizer 3 K ({1} : Set ℕ)) →* Matrix.GeneralLinearGroup (Fin 2) K :=
  (leviOneHom K).toHomUnits

theorem leviOne_apply_apply (g : ↥(flagStabilizer 3 K ({1} : Set ℕ))) (a b : Fin 2) :
    ((leviOne K g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b =
      (g.1 : Matrix (Fin 3) (Fin 3) K) (Fin.succ a) (Fin.succ b) :=
  leviBlockOne_apply (g.1 : Matrix (Fin 3) (Fin 3) K) a b

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem leviOne_ker_le_unitriangular :
    (leviOne K).ker.map (flagStabilizer 3 K ({1} : Set ℕ)).subtype ≤ unitriangular 3 K := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hblk : ∀ a b : Fin 2, (g.1 : Matrix (Fin 3) (Fin 3) K) (Fin.succ a) (Fin.succ b) =
      (1 : Matrix (Fin 2) (Fin 2) K) a b := by
    intro a b
    have h1 : leviOne K g = 1 := MonoidHom.mem_ker.mp hg
    have h2 : ((leviOne K g : Matrix (Fin 2) (Fin 2) K)) = 1 := by rw [h1]; rfl
    rw [← h2]
    exact leviOne_apply_apply g a b
  have h10 : (g.1 : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    succ_zero_eq_zero_of_mem_flagStabilizer_one g.2 0
  have h20 : (g.1 : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    succ_zero_eq_zero_of_mem_flagStabilizer_one g.2 1
  have h11 : (g.1 : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    simpa using hblk 0 0
  have h22 : (g.1 : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    simpa using hblk 1 1
  have h12 : (g.1 : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    simpa using hblk 0 1
  have h21 : (g.1 : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    simpa using hblk 1 0
  have h00 : (g.1 : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    have hdet : (g.1 : Matrix (Fin 3) (Fin 3) K).det = (g.1 : Matrix (Fin 3) (Fin 3) K) 0 0 := by
      rw [Matrix.det_fin_three, h10, h20, h11, h22, h12, h21]
      ring
    rw [← hdet]
    exact g.1.2
  rw [mem_unitriangular]
  constructor
  · intro i j hij
    fin_cases i
    · exact absurd hij (by simp)
    · fin_cases j
      · exact h10
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
    · fin_cases j
      · exact h20
      · exact h21
      · exact absurd hij (by simp)
  · intro i
    fin_cases i
    · exact h00
    · exact h11
    · exact h22

section SurjectiveOne

@[expose] def blockDiagOne (a : K) (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => if h : i = 0 then (if j = 0 then a else 0)
    else (if h2 : j = 0 then 0 else A (Fin.pred i h) (Fin.pred j h2))

theorem blockDiagOne_zero_zero (a : K) (A : Matrix (Fin 2) (Fin 2) K) :
    blockDiagOne a A 0 0 = a := by
  rw [blockDiagOne, Matrix.of_apply, dif_pos rfl, if_pos rfl]

theorem blockDiagOne_succ_succ (a : K) (A : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    blockDiagOne a A (Fin.succ i) (Fin.succ j) = A i j := by
  rw [blockDiagOne, Matrix.of_apply, dif_neg (Fin.succ_ne_zero i),
    dif_neg (Fin.succ_ne_zero j), Fin.pred_succ, Fin.pred_succ]

theorem blockDiagOne_succ_zero (a : K) (A : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    blockDiagOne a A (Fin.succ i) 0 = 0 := by
  rw [blockDiagOne, Matrix.of_apply, dif_neg (Fin.succ_ne_zero i), dif_pos rfl]

theorem blockDiagOne_zero_succ (a : K) (A : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) :
    blockDiagOne a A 0 (Fin.succ j) = 0 := by
  rw [blockDiagOne, Matrix.of_apply, dif_pos rfl, if_neg (Fin.succ_ne_zero j)]

theorem det_blockDiagOne (a : K) (A : Matrix (Fin 2) (Fin 2) K) :
    (blockDiagOne a A).det = a * A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two, ← Fin.succ_one_eq_two,
    ← Fin.succ_zero_eq_one]
  simp only [blockDiagOne_zero_zero a A, blockDiagOne_succ_succ a A, blockDiagOne_zero_succ a A,
    blockDiagOne_succ_zero a A]
  ring

theorem blockDiagOne_map_le (a : K) (A : Matrix (Fin 2) (Fin 2) K) :
    (flagSpace 3 K 1).map (mulVecLin (blockDiagOne a A)) ≤ flagSpace 3 K 1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  rw [mem_flagSpace] at hw ⊢
  intro j hj
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [mulVecLin_apply, Matrix.mulVec_apply]
  rw [show (blockDiagOne a A).row (Fin.succ i) ⬝ᵥ w =
      ∑ k, blockDiagOne a A (Fin.succ i) k * w k from rfl, Fin.sum_univ_succ,
    blockDiagOne_succ_zero, zero_mul, zero_add]
  exact Finset.sum_eq_zero fun c _ => by
    rw [blockDiagOne_succ_succ, hw (Fin.succ c) (by simp), mul_zero]

theorem det_blockDiagOne_inv (A : Matrix.GeneralLinearGroup (Fin 2) K) :
    (blockDiagOne (((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹) (A : Matrix (Fin 2) (Fin 2) K)).det =
      1 := by
  rw [det_blockDiagOne, inv_mul_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero A)]

theorem leviOne_surjective : Function.Surjective (leviOne K) := by
  intro A
  have hdet : (((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹) ≠ 0 :=
    inv_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero A)
  refine ⟨⟨⟨blockDiagOne _ (A : Matrix (Fin 2) (Fin 2) K), det_blockDiagOne_inv A⟩, ?_⟩, ?_⟩
  · refine mem_flagStabilizer.mpr fun i hi => ?_
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact mem_stabilizer_of_map_le (blockDiagOne_map_le _ _)
  · apply Units.ext
    ext a b
    rw [leviOne_apply_apply]
    exact blockDiagOne_succ_succ _ _ a b

end SurjectiveOne

section Two

theorem last_eq_zero_of_mem_flagStabilizer_two {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ flagStabilizer 3 K ({2} : Set ℕ)) (c : Fin 2) :
    (g : Matrix (Fin 3) (Fin 3) K) 2 (Fin.castSucc c) = 0 := by
  have hg2 : g ∈ stabilizer (flagSpace 3 K 2) := (mem_flagStabilizer.mp hg) 2 (by simp)
  have hmap : (flagSpace 3 K 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) =
      flagSpace 3 K 2 := mem_stabilizer.mp hg2
  have hv : (Pi.single (Fin.castSucc c) (1 : K) : Fin 3 → K) ∈ flagSpace 3 K 2 := by
    rw [mem_flagSpace]
    intro j hj
    refine Pi.single_eq_of_ne ?_ 1
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_ofNat] at this
    omega
  have hmem : mulVecLin (g : Matrix (Fin 3) (Fin 3) K) (Pi.single (Fin.castSucc c) 1) ∈
      flagSpace 3 K 2 := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hv
  have h0 := (mem_flagSpace.mp hmem) 2 (by simp)
  rwa [mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] at h0

@[expose] def leviBlockTwo (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun a b => M (Fin.castSucc a) (Fin.castSucc b)

theorem leviBlockTwo_apply (M : Matrix (Fin 3) (Fin 3) K) (a b : Fin 2) :
    leviBlockTwo M a b = M (Fin.castSucc a) (Fin.castSucc b) := by
  rw [leviBlockTwo, Matrix.of_apply]

theorem leviBlockTwo_mul {g h : SpecialLinearGroup (Fin 3) K}
    (hh : h ∈ flagStabilizer 3 K ({2} : Set ℕ)) :
    leviBlockTwo ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      leviBlockTwo (g : Matrix (Fin 3) (Fin 3) K) *
        leviBlockTwo (h : Matrix (Fin 3) (Fin 3) K) := by
  ext a b
  simp only [leviBlockTwo_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc, show (Fin.last 2 : Fin 3) = 2 from rfl,
    last_eq_zero_of_mem_flagStabilizer_two hh b, mul_zero, add_zero]

@[expose] def leviTwoHom (K : Type) [Field K] :
    ↥(flagStabilizer 3 K ({2} : Set ℕ)) →* Matrix (Fin 2) (Fin 2) K where
  toFun g := leviBlockTwo (g.1 : Matrix (Fin 3) (Fin 3) K)
  map_one' := by
    show leviBlockTwo (1 : Matrix (Fin 3) (Fin 3) K) = 1
    ext a b
    simp only [leviBlockTwo, Matrix.of_apply, Matrix.one_apply, Fin.castSucc_inj]
  map_mul' g h := leviBlockTwo_mul h.2

@[expose] def leviTwo (K : Type) [Field K] :
    ↥(flagStabilizer 3 K ({2} : Set ℕ)) →* Matrix.GeneralLinearGroup (Fin 2) K :=
  (leviTwoHom K).toHomUnits

theorem leviTwo_apply_apply (g : ↥(flagStabilizer 3 K ({2} : Set ℕ))) (a b : Fin 2) :
    ((leviTwo K g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b =
      (g.1 : Matrix (Fin 3) (Fin 3) K) (Fin.castSucc a) (Fin.castSucc b) :=
  leviBlockTwo_apply (g.1 : Matrix (Fin 3) (Fin 3) K) a b

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem leviTwo_ker_le_unitriangular :
    (leviTwo K).ker.map (flagStabilizer 3 K ({2} : Set ℕ)).subtype ≤ unitriangular 3 K := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hblk : ∀ a b : Fin 2, (g.1 : Matrix (Fin 3) (Fin 3) K) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin 2) (Fin 2) K) a b := by
    intro a b
    have h1 : leviTwo K g = 1 := MonoidHom.mem_ker.mp hg
    have h2 : ((leviTwo K g : Matrix (Fin 2) (Fin 2) K)) = 1 := by rw [h1]; rfl
    rw [← h2]
    exact leviTwo_apply_apply g a b
  have h20 : (g.1 : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    last_eq_zero_of_mem_flagStabilizer_two g.2 0
  have h21 : (g.1 : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 :=
    last_eq_zero_of_mem_flagStabilizer_two g.2 1
  have h00 : (g.1 : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    simpa using hblk 0 0
  have h11 : (g.1 : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    simpa using hblk 1 1
  have h10 : (g.1 : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    simpa using hblk 1 0
  have h22 : (g.1 : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have hdet : (g.1 : Matrix (Fin 3) (Fin 3) K).det = (g.1 : Matrix (Fin 3) (Fin 3) K) 2 2 := by
      rw [Matrix.det_fin_three, h20, h21, h00, h11, h10]
      ring
    rw [← hdet]
    exact g.1.2
  rw [mem_unitriangular]
  constructor
  · intro i j hij
    fin_cases i
    · exact absurd hij (by simp)
    · fin_cases j
      · exact h10
      · exact absurd hij (by simp)
      · exact absurd hij (by simp)
    · fin_cases j
      · exact h20
      · exact h21
      · exact absurd hij (by simp)
  · intro i
    fin_cases i
    · exact h00
    · exact h11
    · exact h22

section SurjectiveTwo

@[expose] def blockDiagTwo (A : Matrix (Fin 2) (Fin 2) K) (a : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => if h : i = 2 then (if j = 2 then a else 0)
    else (if h2 : j = 2 then 0 else
      A ⟨i.val, by have := i.isLt; have h' : i.val ≠ 2 := fun hv => h (Fin.ext hv); omega⟩
        ⟨j.val, by have := j.isLt; have h' : j.val ≠ 2 := fun hv => h2 (Fin.ext hv); omega⟩)

theorem blockDiagTwo_two_two (A : Matrix (Fin 2) (Fin 2) K) (a : K) :
    blockDiagTwo A a 2 2 = a := by
  rw [blockDiagTwo, Matrix.of_apply, dif_pos rfl, if_pos rfl]

theorem blockDiagTwo_two_castSucc (A : Matrix (Fin 2) (Fin 2) K) (a : K) (j : Fin 2) :
    blockDiagTwo A a 2 (Fin.castSucc j) = 0 := by
  rw [blockDiagTwo, Matrix.of_apply, dif_pos rfl, if_neg]
  intro h
  have h1 : (Fin.castSucc j : Fin 3).val = 2 := by rw [h]; rfl
  rw [show (Fin.castSucc j : Fin 3).val = j.val from rfl] at h1
  omega

theorem blockDiagTwo_castSucc_two (A : Matrix (Fin 2) (Fin 2) K) (a : K) (i : Fin 2) :
    blockDiagTwo A a (Fin.castSucc i) 2 = 0 := by
  rw [blockDiagTwo, Matrix.of_apply, dif_neg, dif_pos rfl]
  intro h
  have h1 : (Fin.castSucc i : Fin 3).val = 2 := by rw [h]; rfl
  rw [show (Fin.castSucc i : Fin 3).val = i.val from rfl] at h1
  omega

theorem blockDiagTwo_castSucc_castSucc (A : Matrix (Fin 2) (Fin 2) K) (a : K) (i j : Fin 2) :
    blockDiagTwo A a (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  rw [blockDiagTwo, Matrix.of_apply, dif_neg, dif_neg]
  · congr 1 <;> exact Fin.ext rfl
  · intro h
    have h1 : (Fin.castSucc j : Fin 3).val = 2 := by rw [h]; rfl
    rw [show (Fin.castSucc j : Fin 3).val = j.val from rfl] at h1
    omega
  · intro h
    have h1 : (Fin.castSucc i : Fin 3).val = 2 := by rw [h]; rfl
    rw [show (Fin.castSucc i : Fin 3).val = i.val from rfl] at h1
    omega

theorem det_blockDiagTwo (A : Matrix (Fin 2) (Fin 2) K) (a : K) :
    (blockDiagTwo A a).det = A.det * a := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two,
    show (0 : Fin 3) = Fin.castSucc (0 : Fin 2) from rfl,
    show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from rfl]
  simp only [blockDiagTwo_two_two A a, blockDiagTwo_two_castSucc A a,
    blockDiagTwo_castSucc_two A a, blockDiagTwo_castSucc_castSucc A a]
  ring

theorem blockDiagTwo_map_le (A : Matrix (Fin 2) (Fin 2) K) (a : K) :
    (flagSpace 3 K 2).map (mulVecLin (blockDiagTwo A a)) ≤ flagSpace 3 K 2 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  rw [mem_flagSpace] at hw ⊢
  intro j hj
  have hj2 : j = 2 := by
    have := j.isLt
    omega
  subst hj2
  rw [mulVecLin_apply, Matrix.mulVec_apply]
  rw [show (blockDiagTwo A a).row 2 ⬝ᵥ w = ∑ k, blockDiagTwo A a 2 k * w k from rfl,
    Fin.sum_univ_castSucc, show (Fin.last 2 : Fin 3) = 2 from rfl,
    blockDiagTwo_two_two A a, hw 2 (by simp), mul_zero, add_zero]
  exact Finset.sum_eq_zero fun c _ => by
    simp only [blockDiagTwo_two_castSucc A a, zero_mul]

theorem det_blockDiagTwo_inv (A : Matrix.GeneralLinearGroup (Fin 2) K) :
    (blockDiagTwo (A : Matrix (Fin 2) (Fin 2) K) (((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹)).det =
      1 := by
  rw [det_blockDiagTwo, mul_inv_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero A)]

theorem leviTwo_surjective : Function.Surjective (leviTwo K) := by
  intro A
  refine ⟨⟨⟨blockDiagTwo (A : Matrix (Fin 2) (Fin 2) K) _,
    det_blockDiagTwo_inv A⟩, ?_⟩, ?_⟩
  · refine mem_flagStabilizer.mpr fun i hi => ?_
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact mem_stabilizer_of_map_le (blockDiagTwo_map_le _ _)
  · apply Units.ext
    ext a b
    rw [leviTwo_apply_apply]
    exact blockDiagTwo_castSucc_castSucc _ _ a b

end SurjectiveTwo



end Two

end One

end CFSG.LocalAnalysis.AGL81I.Section3
