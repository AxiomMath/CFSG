module

public import CFSG.LieType.SeitzGeneration.UnitaryOuterNormal
public import CFSG.LieType.SeitzGeneration.UnitaryToral

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def outerHeisLines (ω α : K) : Set (Matrix (Fin 3) (Fin 3) K) :=
  {heisC α, heisD ω, heisC α * heisD ω, heisC α * heisD ω ^ 2}

@[expose] def UnitaryOuterHeisCore : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ ω α : K, IsPrimitiveRoot ω 3 → α ^ (ℓ ^ f + 1) = 1 → (¬ ∃ μ : K, μ ^ 3 = α) →
      Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ outerHeisLines ω α, g ∈ FixU ℓ f K M} = ⊤

theorem mem_FixU_conj (h : UnitaryFieldData ℓ f K) (P : primeFormUnitary h (idGram K 3))
    {M N : Matrix (Fin 3) (Fin 3) K}
    (hMN : M * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N) {g : unitarySU ℓ f K 3}
    (hg : g ∈ FixU ℓ f K N) : conjSU h P g ∈ FixU ℓ f K M := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  set Pm : Matrix (Fin 3) (Fin 3) K := ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hPm
  set Pi : Matrix (Fin 3) (Fin 3) K :=
    (((P : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hiM : Pi * M = N * Pi := by
    calc Pi * M = Pi * (M * Pm) * Pi := by
          simp only [Matrix.mul_assoc, hPPi, Matrix.mul_one]
      _ = N * Pi := by rw [hMN, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hcoe : (((conjSU h P g : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi := by
    rw [coe_conjSU, Units.val_mul, Units.val_mul]
  rw [hcoe]
  calc Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi * M
      = Pm * (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N) * Pi := by
        rw [Matrix.mul_assoc _ Pi, hiM]; simp only [Matrix.mul_assoc]
    _ = c • (Pm * (N * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * Pi) := by
        rw [hc, Matrix.mul_smul, Matrix.smul_mul]
    _ = c • (M * (Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi)) := by
        congr 1
        calc Pm * (N * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * Pi
            = (Pm * N) * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi := by
              simp only [Matrix.mul_assoc]
          _ = M * (Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi) := by
              rw [← hMN]; simp only [Matrix.mul_assoc]

theorem eq_top_of_conj_closure (h : UnitaryFieldData ℓ f K) (P : primeFormUnitary h (idGram K 3))
    {Q : Subgroup (unitarySU ℓ f K 3)} {S : Set (unitarySU ℓ f K 3)}
    (hS : Subgroup.closure S = ⊤) (hQ : ∀ g ∈ S, conjSU h P g ∈ Q) : Q = ⊤ := by
  have hmap : Subgroup.map (conjSU h P).toMonoidHom (Subgroup.closure S) ≤ Q := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hQ g hg
  rw [hS, Subgroup.map_top_of_surjective _ (conjSU h P).surjective] at hmap
  exact top_unique hmap

theorem bar_mul_eq_one_of_pow_three (h : UnitaryFieldData ℓ f K) {g : GL (Fin 3) K}
    (hg : g ∈ primeFormUnitary h (idGram K 3)) {lam : K}
    (hlam : ((g ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = lam • 1) :
    h.bar lam * lam = 1 := by
  have h1 := mem_primeFormUnitary.1 (pow_mem hg 3)
  simp only [idGram, Units.val_one] at h1
  rw [hlam, barTranspose_smul_mul_smul] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simpa using h2

theorem closure_planeFixU_heis_outer (hcore : UnitaryOuterHeisCore) (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) {x y : GL (Fin 3) K}
    (hx : x ∈ primeFormUnitary h (idGram K 3)) (hy : y ∈ primeFormUnitary h (idGram K 3))
    {ω α : K} (hω : IsPrimitiveRoot ω 3)
    (hyx : (y : Matrix (Fin 3) (Fin 3) K) * x = ω • ((x : Matrix (Fin 3) (Fin 3) K) * y))
    (hy3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1)
    (hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) (hαc : ¬ ∃ μ : K, μ ^ 3 = α) :
    Subgroup.closure (planeFixU ℓ f K x y) = ⊤ := by
  obtain ⟨P, ξ, hPU, hξ3, hYP, hXP⟩ := exists_unitary_heisenberg_basis_alpha h hq3 hx hy hω hyx
    hy3 hx3
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  have hαN : α ^ (ℓ ^ f + 1) = 1 := by
    have := bar_mul_eq_one_of_pow_three h hx (lam := α) (by
      rw [Units.val_pow_eq_pow_val]; exact hx3)
    rwa [h.bar_apply, ← pow_succ] at this
  have hDξ : (diagonal ![ξ, ξ * ω, ξ * ω ^ 2] : Matrix (Fin 3) (Fin 3) K) = ξ • heisD ω := by
    ext i j
    by_cases hij : i = j
    · subst hij; fin_cases i <;> simp [heisD, mul_comm]
    · simp [heisD, hij]
  rw [hDξ] at hYP
  set Pu : primeFormUnitary h (idGram K 3) := ⟨P, hPU⟩ with hPu
  have hcl := hcore ℓ f K h hq3 hq ω α hω hαN hαc
  refine eq_top_of_conj_closure h Pu hcl ?_
  rintro g ⟨M, hM, hgM⟩
  refine Subgroup.subset_closure ?_
  have hPm : ((Pu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) := rfl
  simp only [outerHeisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl (mem_FixU_conj h Pu (by rw [hPm]; exact hXP) hgM)))
  · refine Or.inl (Or.inl (Or.inr (mem_FixU_conj h Pu (by rw [hPm]; exact hYP) ?_)))
    exact (mem_FixU_smul hξ0).2 hgM
  · refine Or.inl (Or.inr (mem_FixU_conj h Pu (by
      rw [hPm, Units.val_mul]; exact intertwine_mul_right hXP hYP) ?_))
    rw [Matrix.mul_smul]; exact (mem_FixU_smul hξ0).2 hgM
  · refine Or.inr (mem_FixU_conj h Pu (by
      rw [hPm, Units.val_mul, Units.val_pow_eq_pow_val]
      exact intertwine_mul_right hXP (intertwine_pow_right hYP 2)) ?_)
    rw [smul_pow, Matrix.mul_smul]; exact (mem_FixU_smul (pow_ne_zero 2 hξ0)).2 hgM

theorem closure_planeFixU_heis_inner (hcore : UnitaryHeisCore) (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) {x y : GL (Fin 3) K}
    (hx : x ∈ primeFormUnitary h (idGram K 3)) (hy : y ∈ primeFormUnitary h (idGram K 3))
    {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hxy : (x : Matrix (Fin 3) (Fin 3) K) * y = ω • ((y : Matrix (Fin 3) (Fin 3) K) * x))
    (hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1) (hy3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1) :
    Subgroup.closure (planeFixU ℓ f K x y) = ⊤ := by
  obtain ⟨P, ξ, hPU, hξ3, hXP, hYP⟩ := exists_unitary_heisenberg_basis_alpha h hq3 hy hx hω hxy
    hx3 (α := 1) (by rw [hy3, one_smul])
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  have hDξ : (diagonal ![ξ, ξ * ω, ξ * ω ^ 2] : Matrix (Fin 3) (Fin 3) K) = ξ • hD ω := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, mul_comm]
  rw [hDξ] at hXP
  have hYP' : (y : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) * hS := hYP
  set Pu : primeFormUnitary h (idGram K 3) := ⟨P, hPU⟩ with hPu
  have hcl := hcore ℓ f K h hq3 hq ω hω
  refine eq_top_of_conj_closure h Pu hcl ?_
  rintro g ⟨M, hM, hgM⟩
  refine Subgroup.subset_closure ?_
  have hPm : ((Pu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) := rfl
  have hgM' : g ∈ FixU ℓ f K M := hgM
  simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl (mem_FixU_conj h Pu (by rw [hPm]; exact hXP)
      ((mem_FixU_smul hξ0).2 hgM'))))
  · exact Or.inl (Or.inl (Or.inr (mem_FixU_conj h Pu (by rw [hPm]; exact hYP') hgM')))
  · refine Or.inl (Or.inr (mem_FixU_conj h Pu (by
      rw [hPm, Units.val_mul]; exact intertwine_mul_right hXP hYP') ?_))
    rw [Matrix.smul_mul]; exact (mem_FixU_smul hξ0).2 hgM'
  · refine Or.inr (mem_FixU_conj h Pu (by
      rw [hPm, Units.val_mul, Units.val_pow_eq_pow_val]
      exact intertwine_mul_right hXP (intertwine_pow_right hYP' 2)) ?_)
    rw [pow_two, Matrix.smul_mul, ← Matrix.mul_assoc]
    exact (mem_FixU_smul hξ0).2 hgM'

end CFSG.LieType.SeitzGeneration
