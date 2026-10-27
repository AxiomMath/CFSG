module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTorusDet
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSinger

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix
open CFSG.RankThree.PartTwo.Sec4 (isUnit_colMat mul_colMat_cyclic linearIndependent_cyclic
  exists_normal_form companionThree det_companionThree one_add_tau_add_sq)

@[expose] def HasCyclicVec3 {K : Type*} [Field K] (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∃ v : Fin 3 → K, LinearIndependent K ![v, A *ᵥ v, A *ᵥ (A *ᵥ v)]

variable {K : Type} [Field K]

section Cyclic

theorem hasCyclicVec3_iff {A : Matrix (Fin 3) (Fin 3) K} :
    HasCyclicVec3 A ↔ ∃ v : Fin 3 → K, LinearIndependent K ![v, A *ᵥ v, (A ^ 2) *ᵥ v] := by
  simp only [HasCyclicVec3, Matrix.mulVec_mulVec, sq]

theorem HasCyclicVec3.det_eq {A : Matrix (Fin 3) (Fin 3) K} {α : K} (hA : HasCyclicVec3 A)
    (hA3 : A ^ 3 = α • 1) : A.det = α := by
  obtain ⟨v, hv⟩ := hasCyclicVec3_iff.1 hA
  have hP := isUnit_colMat hv
  have h := congrArg Matrix.det (mul_colMat_cyclic hA3 v)
  rw [det_mul, det_mul, det_companionThree, mul_comm] at h
  exact mul_left_cancel₀ ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero h

theorem HasCyclicVec3.smul_conj {A : Matrix (Fin 3) (Fin 3) K} (hA : HasCyclicVec3 A)
    (g : GL (Fin 3) K) {κ : K} (hκ : κ ≠ 0) :
    HasCyclicVec3 (κ • ((g : Matrix (Fin 3) (Fin 3) K) * A *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
  obtain ⟨v, hv⟩ := hA
  set G : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K)
  set Gi : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hGiG : Gi * G = 1 := g.inv_mul
  have e : ∀ u, (κ • (G * A * Gi)) *ᵥ (G *ᵥ u) = κ • (G *ᵥ (A *ᵥ u)) := fun u => by
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (G * A), hGiG, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
  refine ⟨G *ᵥ v, ?_⟩
  rw [e, Matrix.mulVec_smul, e]
  have hinj : LinearMap.ker (Matrix.mulVecLin G) = ⊥ :=
    LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff_isUnit.2 g.isUnit)
  have h1 := (hv.map' (Matrix.mulVecLin G) hinj).units_smul
    ![1, Units.mk0 κ hκ, Units.mk0 κ hκ * Units.mk0 κ hκ]
  convert h1 using 1
  ext i : 1
  fin_cases i <;> simp [Units.smul_def, smul_smul]

theorem linearIndependent_cyclic_of_mul_eq {A D g : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g)
    (h : A * g = g * D) {u : Fin 3 → K}
    (hu : LinearIndependent K ![u, D *ᵥ u, (D ^ 2) *ᵥ u]) :
    LinearIndependent K ![g *ᵥ u, A *ᵥ (g *ᵥ u), (A ^ 2) *ᵥ (g *ᵥ u)] := by
  have h2 : A ^ 2 * g = g * D ^ 2 := by
    rw [sq, sq, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h, Matrix.mul_assoc]
  have hinj : LinearMap.ker (Matrix.mulVecLin g) = ⊥ :=
    LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff_isUnit.2 hg)
  convert hu.map' (Matrix.mulVecLin g) hinj using 1
  ext i : 1
  fin_cases i
  · rfl
  · simp [Matrix.mulVec_mulVec, h]
  · simp [Matrix.mulVec_mulVec, h2]

theorem linearIndependent_cyclic_diagonal {d : Fin 3 → K} (h01 : d 0 ≠ d 1) (h02 : d 0 ≠ d 2)
    (h12 : d 1 ≠ d 2) :
    LinearIndependent K ![(fun _ => 1 : Fin 3 → K), diagonal d *ᵥ (fun _ => 1),
      (diagonal d ^ 2) *ᵥ (fun _ => 1)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have e : ∀ i, c 0 + c 1 * d i + c 2 * d i ^ 2 = 0 := by
    intro i
    have := congrFun hc i
    simpa [Fin.sum_univ_three, Matrix.mulVec_diagonal, diagonal_pow] using this
  have e01 : (d 0 - d 1) * (c 1 + c 2 * (d 0 + d 1)) = 0 := by linear_combination e 0 - e 1
  have e02 : (d 0 - d 2) * (c 1 + c 2 * (d 0 + d 2)) = 0 := by linear_combination e 0 - e 2
  have f01 := (mul_eq_zero.1 e01).resolve_left (sub_ne_zero.2 h01)
  have f02 := (mul_eq_zero.1 e02).resolve_left (sub_ne_zero.2 h02)
  have hc2 : c 2 = 0 := by
    have h : (d 1 - d 2) * c 2 = 0 := by linear_combination f01 - f02
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h12)
  have hc1 : c 1 = 0 := by linear_combination f01 - (d 0 + d 1) * hc2
  have hc0 : c 0 = 0 := by linear_combination e 0 - d 0 * hc1 - d 0 ^ 2 * hc2
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2

theorem exists_invariant_of_mul_eq_diagonal {A g : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g)
    {ε : K} (hε0 : ε ≠ 0) (hε1 : ε ≠ 1) (h : A * g = g * diagonal ![ε, 1, 1])
    {S : Set (GL (Fin 3) K)}
    (hS : ∀ B ∈ S, ∃ κ : K, (B : Matrix (Fin 3) (Fin 3) K) * A = κ • (A * B)) :
    ∃ W : Submodule K (Fin 3 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ B ∈ S, ∀ w ∈ W, (B : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
  obtain ⟨G, rfl⟩ := hg
  set Gi : Matrix (Fin 3) (Fin 3) K := ((G⁻¹ : (Matrix (Fin 3) (Fin 3) K)ˣ) :
    Matrix (Fin 3) (Fin 3) K)
  have hGiG : Gi * G = 1 := G.inv_mul
  have hGGi : (G : Matrix (Fin 3) (Fin 3) K) * Gi = 1 := G.mul_inv
  have hGiG' : ∀ X : Matrix (Fin 3) (Fin 3) K, Gi * (G * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  have hGGi' : ∀ X : Matrix (Fin 3) (Fin 3) K, (G : Matrix (Fin 3) (Fin 3) K) * (Gi * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, hGGi, Matrix.one_mul]
  set W : Submodule K (Fin 3 → K) :=
    LinearMap.ker ((LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 0).comp
      (Matrix.mulVecLin Gi))
  have hmem : ∀ w, w ∈ W ↔ (Gi *ᵥ w) 0 = 0 := fun w => Iff.rfl
  have hGv : ∀ u : Fin 3 → K, Gi *ᵥ ((G : Matrix (Fin 3) (Fin 3) K) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]
  refine ⟨W, ?_, ?_, ?_⟩
  ·
    intro hbot
    have h1 : (G : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single (1 : Fin 3) (1 : K) ∈ W := by
      rw [hmem, hGv]
      simp
    rw [hbot, Submodule.mem_bot] at h1
    have h2 := hGv (Pi.single (1 : Fin 3) (1 : K))
    rw [h1, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 1
    simp at h3
  ·
    intro htop
    have h1 : (G : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single (0 : Fin 3) (1 : K) ∈ W := by
      rw [htop]
      exact Submodule.mem_top
    rw [hmem, hGv] at h1
    simp at h1
  · intro B hB w hw
    obtain ⟨κ, hκ⟩ := hS B hB
    set Bm : Matrix (Fin 3) (Fin 3) K := (B : Matrix (Fin 3) (Fin 3) K)
    set M : Matrix (Fin 3) (Fin 3) K := Gi * Bm * G with hM
    have hD : Gi * A * G = diagonal ![ε, 1, 1] := by
      rw [Matrix.mul_assoc, h, hGiG']
    have hMD : M * diagonal ![ε, 1, 1] = κ • (diagonal ![ε, 1, 1] * M) := by
      rw [← hD, hM]
      calc Gi * Bm * G * (Gi * A * G) = Gi * (Bm * A) * G := by
            simp only [Matrix.mul_assoc, hGGi']
        _ = Gi * (κ • (A * Bm)) * G := by rw [hκ]
        _ = κ • (Gi * A * G * (Gi * Bm * G)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hGGi']
    have e : ∀ r s, M r s * (![ε, 1, 1] : Fin 3 → K) s =
        κ * ((![ε, 1, 1] : Fin 3 → K) r * M r s) := fun r s => by
      have := congrFun (congrFun hMD r) s
      rwa [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul] at this
    have e00 : M 0 0 * ε = κ * (ε * M 0 0) := e 0 0
    have e01 : M 0 1 * 1 = κ * (ε * M 0 1) := e 0 1
    have e02 : M 0 2 * 1 = κ * (ε * M 0 2) := e 0 2
    have e11 : M 1 1 * 1 = κ * (1 * M 1 1) := e 1 1
    have e12 : M 1 2 * 1 = κ * (1 * M 1 2) := e 1 2
    have e21 : M 2 1 * 1 = κ * (1 * M 2 1) := e 2 1
    have e22 : M 2 2 * 1 = κ * (1 * M 2 2) := e 2 2
    have hdetM : M.det ≠ 0 := by
      rw [hM, Matrix.det_mul, Matrix.det_mul]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact ((Matrix.isUnit_iff_isUnit_det _).1 (G⁻¹).isUnit).ne_zero
      · exact ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
      · exact ((Matrix.isUnit_iff_isUnit_det _).1 G.isUnit).ne_zero
    have hκ1 : κ = 1 := by
      by_contra hκ1
      have hκ1' : 1 - κ ≠ 0 := sub_ne_zero.2 (Ne.symm hκ1)
      have z : ∀ x : K, x * 1 = κ * (1 * x) → x = 0 := fun x hx => by
        have : (1 - κ) * x = 0 := by linear_combination hx
        exact (mul_eq_zero.1 this).resolve_left hκ1'
      have h00 : M 0 0 = 0 := by
        have : (ε * (1 - κ)) * M 0 0 = 0 := by linear_combination e00
        exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero hε0 hκ1')
      apply hdetM
      rw [Matrix.det_fin_three, h00, z _ e11, z _ e12, z _ e21, z _ e22]
      ring
    subst hκ1
    have z : ∀ x : K, x * 1 = 1 * (ε * x) → x = 0 := fun x hx => by
      have : (ε - 1) * x = 0 := by linear_combination -hx
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hε1)
    have hM01 : M 0 1 = 0 := z _ e01
    have hM02 : M 0 2 = 0 := z _ e02
    rw [hmem] at hw ⊢
    have hBw : Gi *ᵥ (Bm *ᵥ w) = M *ᵥ (Gi *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.mul_assoc (Gi * Bm), hGGi,
        Matrix.mul_one]
    rw [hBw]
    generalize Gi *ᵥ w = u at hw ⊢
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [hw, hM01, hM02]
    ring

theorem hasCyclicVec3_of_irreducible {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {A : GL (Fin 3) K} {α : K} (hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hA : ∀ c : K, (A : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) (S : Set (GL (Fin 3) K))
    (hS : ∀ B ∈ S, ∃ κ : K,
      (B : Matrix (Fin 3) (Fin 3) K) * A = κ • ((A : Matrix (Fin 3) (Fin 3) K) * B))
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ B ∈ S, ∀ w ∈ W, (B : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    HasCyclicVec3 (A : Matrix (Fin 3) (Fin 3) K) := by
  rw [hasCyclicVec3_iff]
  have hα0 : α ≠ 0 := ne_zero_of_pow_three_eq_smul hA3
  by_cases hcube : ∃ μ : K, μ ^ 3 = α
  swap
  ·
    have hα : ∀ μ : K, μ ^ 3 ≠ α := fun μ h => hcube ⟨μ, h⟩
    refine ⟨Pi.single (0 : Fin 3) (1 : K), linearIndependent_cyclic hα hA3 ?_⟩
    intro h0
    have := congrFun h0 0
    simp at this
  obtain ⟨μ, hμ⟩ := hcube
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hα0
    rw [← hμ]
    ring
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have h3 : (3 : K) ≠ 0 := by
    intro h3
    have hs := one_add_tau_add_sq hω3 hω1
    have h2 : (ω - 1) ^ 2 = 0 := by linear_combination hs - ω * h3
    exact hω1 (sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2))
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h2, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  obtain ⟨y, hy⟩ : ∃ y : Matrix (Fin 3) (Fin 3) K, y = μ⁻¹ • (A : Matrix (Fin 3) (Fin 3) K) :=
    ⟨_, rfl⟩
  have hy3 : y ^ 3 = 1 := by
    rw [hy, smul_pow, hA3, smul_smul, ← hμ, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hμ0),
      one_smul]
  have hys : ∀ c : K, y ≠ c • 1 := by
    intro c hc
    apply hA (μ * c)
    calc (A : Matrix (Fin 3) (Fin 3) K) = μ • y := by
          rw [hy, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      _ = (μ * c) • 1 := by rw [hc, smul_smul]
  obtain ⟨g, j, hg, hcases⟩ := exists_normal_form hω3 hω1 h3 hy3 hys
  obtain ⟨s, hs⟩ : ∃ s : K, s = ω ^ (j : ℕ) * μ⁻¹ := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact mul_ne_zero (pow_ne_zero _ hω0) (inv_ne_zero hμ0)
  have hsy : ω ^ (j : ℕ) • y = s • (A : Matrix (Fin 3) (Fin 3) K) := by
    rw [hy, smul_smul, hs]
  rw [hsy] at hcases
  have hnot : ∀ ε : K, ε ≠ 0 → ε ≠ 1 →
      (s • (A : Matrix (Fin 3) (Fin 3) K)) * g = g * diagonal ![ε, 1, 1] → False := by
    intro ε hε0 hε1 h
    have hS' : ∀ B ∈ S, ∃ κ : K, (B : Matrix (Fin 3) (Fin 3) K) * (s • (A : Matrix (Fin 3)
        (Fin 3) K)) = κ • ((s • (A : Matrix (Fin 3) (Fin 3) K)) * B) := by
      intro B hB
      obtain ⟨κ, hκ⟩ := hS B hB
      refine ⟨κ, ?_⟩
      rw [Matrix.mul_smul, hκ, Matrix.smul_mul, smul_comm]
    obtain ⟨W, hW0, hWT, hWinv⟩ := exists_invariant_of_mul_eq_diagonal hg hε0 hε1 h hS'
    rcases hirr W hWinv with h' | h'
    · exact hW0 h'
    · exact hWT h'
  rcases hcases with h | h | h
  ·
    have hD : diagonal ![s⁻¹ * ω, s⁻¹ * ω ^ 2, s⁻¹] = s⁻¹ • diagonal ![ω, ω ^ 2, 1] := by
      ext r t
      fin_cases r <;> fin_cases t <;> simp
    have hMg : (A : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal ![s⁻¹ * ω, s⁻¹ * ω ^ 2, s⁻¹] := by
      rw [hD, Matrix.mul_smul, ← h, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hsi : s⁻¹ ≠ 0 := inv_ne_zero hs0
    have h01 : s⁻¹ * ω ≠ s⁻¹ * ω ^ 2 := by
      intro h'
      apply hω1
      have h'' : ω * ω = ω * 1 := by
        rw [mul_one, ← sq]
        exact (mul_left_cancel₀ hsi h').symm
      exact mul_left_cancel₀ hω0 h''
    have h02 : s⁻¹ * ω ≠ s⁻¹ := fun h' =>
      hω1 (mul_left_cancel₀ hsi (h'.trans (mul_one _).symm))
    have h12 : s⁻¹ * ω ^ 2 ≠ s⁻¹ := fun h' =>
      hω2 (mul_left_cancel₀ hsi (h'.trans (mul_one _).symm))
    exact ⟨g *ᵥ (fun _ => 1), linearIndependent_cyclic_of_mul_eq hg hMg
      (linearIndependent_cyclic_diagonal (d := ![s⁻¹ * ω, s⁻¹ * ω ^ 2, s⁻¹]) h01 h02 h12)⟩
  · exact (hnot ω hω0 hω1 h).elim
  · exact (hnot (ω ^ 2) (pow_ne_zero 2 hω0) hω2 h).elim

end Cyclic

section Conj

theorem exists_conj_of_hasCyclicVec3 {A B : GL (Fin 3) K} {α : K}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hB3 : (B : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hA : HasCyclicVec3 (A : Matrix (Fin 3) (Fin 3) K))
    (hB : HasCyclicVec3 (B : Matrix (Fin 3) (Fin 3) K)) :
    ∃ g : GL (Fin 3) K, g * A = B * g := by
  obtain ⟨v, hv⟩ := hasCyclicVec3_iff.1 hA
  obtain ⟨w, hw⟩ := hasCyclicVec3_iff.1 hB
  obtain ⟨P, hP⟩ := isUnit_colMat hv
  obtain ⟨Q, hQ⟩ := isUnit_colMat hw
  have hAP : (A : Matrix (Fin 3) (Fin 3) K) * P = P * companionThree α := by
    rw [hP]
    exact mul_colMat_cyclic hA3 v
  have hBQ : (B : Matrix (Fin 3) (Fin 3) K) * Q = Q * companionThree α := by
    rw [hQ]
    exact mul_colMat_cyclic hB3 w
  have hPA : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A =
      companionThree α * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    calc ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A
        = ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((A : Matrix (Fin 3) (Fin 3) K) * (P * ((P⁻¹ : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K))) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((A : Matrix (Fin 3) (Fin 3) K) * P) *
            ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          simp only [Matrix.mul_assoc]
      _ = ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (P * companionThree α) *
            ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hAP]
      _ = companionThree α * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨Q * P⁻¹, Units.ext ?_⟩
  simp only [Units.val_mul]
  calc (Q : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A
      = Q * (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A) := Matrix.mul_assoc _ _ _
    _ = Q * (companionThree α * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [hPA]
    _ = Q * companionThree α * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
        (Matrix.mul_assoc _ _ _).symm
    _ = B * Q * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [hBQ]
    _ = B * (Q * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := Matrix.mul_assoc _ _ _

theorem exists_SL_conj_of_hasCyclicVec3 [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {A B : GL (Fin 3) K} {α β : K} (hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hB3 : (B : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1)
    (hdet : (A : Matrix (Fin 3) (Fin 3) K).det = (B : Matrix (Fin 3) (Fin 3) K).det)
    (hA : HasCyclicVec3 (A : Matrix (Fin 3) (Fin 3) K))
    (hB : HasCyclicVec3 (B : Matrix (Fin 3) (Fin 3) K)) :
    ∃ g : SpecialLinearGroup (Fin 3) K,
      SpecialLinearGroup.toGL g * A = B * SpecialLinearGroup.toGL g := by
  have hαβ : α = β := by rw [← hA.det_eq hA3, ← hB.det_eq hB3, hdet]
  subst hαβ
  obtain ⟨g₀, hg₀⟩ := exists_conj_of_hasCyclicVec3 hA3 hB3 hA hB
  obtain ⟨δ, hδ, hdetδ⟩ :=
    exists_commute_det_eq_of_pow_three h3 hA3 (GeneralLinearGroup.det g₀)⁻¹
  have hg1 : ((g₀ * δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, hdetδ, mul_inv_cancel, Units.val_one]
  refine ⟨⟨_, hg1⟩, ?_⟩
  have hgl : SpecialLinearGroup.toGL ⟨_, hg1⟩ = g₀ * δ := Units.ext rfl
  rw [hgl]
  calc g₀ * δ * A = g₀ * (δ * A) := mul_assoc _ _ _
    _ = g₀ * (A * δ) := by rw [hδ]
    _ = g₀ * A * δ := (mul_assoc _ _ _).symm
    _ = B * g₀ * δ := by rw [hg₀]
    _ = B * (g₀ * δ) := mul_assoc _ _ _

end Conj

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
