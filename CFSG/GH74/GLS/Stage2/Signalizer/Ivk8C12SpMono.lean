module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Mono
public import CFSG.Open.StatedDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.Open

@[expose] def kpermS : Fin 4 → Equiv.Perm (Fin 2 ⊕ Fin 2) :=
  ![1, Equiv.swap (Sum.inl 0) (Sum.inl 1) * Equiv.swap (Sum.inr 0) (Sum.inr 1),
    Equiv.swap (Sum.inl 0) (Sum.inr 0) * Equiv.swap (Sum.inl 1) (Sum.inr 1),
    Equiv.swap (Sum.inl 0) (Sum.inr 1) * Equiv.swap (Sum.inl 1) (Sum.inr 0)]

theorem kpermS_mul : ∀ g h : Fin 4, ∃ k : Fin 4, kpermS g * kpermS h = kpermS k := by decide

theorem kpermS_sq : ∀ g : Fin 4, kpermS g * kpermS g = 1 := by decide

section MonoS

variable {K : Type} [Field K]

@[expose] def monoS (σ : Equiv.Perm (Fin 2 ⊕ Fin 2)) (ε : Fin 2 ⊕ Fin 2 → K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.of fun i j => if i = σ j then ε j else 0

theorem monoS_mul (σ τ : Equiv.Perm (Fin 2 ⊕ Fin 2)) (ε δ : Fin 2 ⊕ Fin 2 → K) :
    monoS σ ε * monoS τ δ = monoS (σ * τ) (fun k => ε (τ k) * δ k) := by
  ext i k
  simp only [monoS, Matrix.mul_apply, Matrix.of_apply, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (τ k)]
  · by_cases h : i = σ (τ k) <;> simp [h]
  · intro j _ hj
    simp [hj]
  · simp

theorem monoS_one_eq : monoS (1 : Equiv.Perm (Fin 2 ⊕ Fin 2)) (fun _ => (1 : K)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [monoS, Matrix.one_apply, h]

theorem monoS_mulVec (σ : Equiv.Perm (Fin 2 ⊕ Fin 2)) (ε w : Fin 2 ⊕ Fin 2 → K)
    (i : Fin 2 ⊕ Fin 2) : (monoS σ ε *ᵥ w) i = ε (σ⁻¹ i) * w (σ⁻¹ i) := by
  simp only [Matrix.mulVec, dotProduct, monoS, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ⁻¹ i)]
  · simp
  · intro j _ hj
    have : ¬ i = σ j := fun h => hj (by rw [h]; simp)
    simp [this]
  · simp

theorem monoS_conj_gram (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (σ : Equiv.Perm (Fin 2 ⊕ Fin 2)) (ε : Fin 2 ⊕ Fin 2 → K) (i j : Fin 2 ⊕ Fin 2) :
    ((monoS σ ε)ᵀ * G * monoS σ ε) i j = ε i * G (σ i) (σ j) * ε j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, monoS, Matrix.of_apply]
  simp [mul_ite, mul_comm, mul_left_comm]

@[expose] def IsSgnS (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : Prop :=
  ∃ (g : Fin 4) (ε : Fin 2 ⊕ Fin 2 → K), (∀ i, ε i = 1 ∨ ε i = -1) ∧ A = monoS (kpermS g) ε

theorem IsSgnS.mul {A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hA : IsSgnS A)
    (hB : IsSgnS B) : IsSgnS (A * B) := by
  obtain ⟨g, ε, hε, rfl⟩ := hA
  obtain ⟨h, δ, hδ, rfl⟩ := hB
  obtain ⟨k, hk⟩ := kpermS_mul g h
  exact ⟨k, fun i => ε (kpermS h i) * δ i, fun i => pm_mul (hε _) (hδ _), by
    rw [monoS_mul, hk]⟩

theorem isSgnS_one : IsSgnS (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
  ⟨0, fun _ => 1, fun _ => Or.inl rfl, by rw [← monoS_one_eq]; rfl⟩

theorem IsSgnS.inv {A : GL (Fin 2 ⊕ Fin 2) K}
    (hA : IsSgnS (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    IsSgnS ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  obtain ⟨g, ε, hε, hAe⟩ := hA
  refine ⟨g, fun k => ε (kpermS g k), fun i => hε _, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_inv]
  apply Matrix.inv_eq_left_inv
  rw [hAe, monoS_mul, kpermS_sq, ← monoS_one_eq]
  congr 1
  funext k
  have hk : kpermS g (kpermS g k) = k := by
    have := congrArg (fun σ : Equiv.Perm (Fin 2 ⊕ Fin 2) => σ k) (kpermS_sq g)
    simpa using this
  simp only [hk]
  exact pm_mul_self (hε k)

variable (K) in
@[expose] def sgnGroupS : Subgroup (GL (Fin 2 ⊕ Fin 2) K) where
  carrier := {A | IsSgnS (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)}
  mul_mem' := fun {A B} hA hB => by
    have := IsSgnS.mul hA hB
    simpa using this
  one_mem' := by simpa using isSgnS_one
  inv_mem' := fun {A} hA => IsSgnS.inv hA

theorem sgnS_pow_four {A : GL (Fin 2 ⊕ Fin 2) K} (hA : A ∈ sgnGroupS K) : A ^ 4 = 1 := by
  obtain ⟨g, ε, hε, hAe⟩ := hA
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, hAe]
  have h2 : monoS (kpermS g) ε * monoS (kpermS g) ε =
      monoS 1 (fun k => ε (kpermS g k) * ε k) := by
    rw [monoS_mul, kpermS_sq]
  have h4 : monoS (1 : Equiv.Perm (Fin 2 ⊕ Fin 2)) (fun k => ε (kpermS g k) * ε k) *
      monoS 1 (fun k => ε (kpermS g k) * ε k) = 1 := by
    rw [monoS_mul, mul_one, ← monoS_one_eq]
    congr 1
    funext k
    exact pm_mul_self (pm_mul (hε _) (hε _))
  have e4 : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, M ^ 4 = (M * M) * (M * M) :=
    fun M => by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e4, h2, h4]

theorem isPGroup_sgnGroupS : IsPGroup 2 ↥(sgnGroupS K) := fun A =>
  ⟨2, Subtype.ext (by simpa using sgnS_pow_four A.2)⟩

@[expose] def monoGLS (g : Fin 4) (ε : Fin 2 ⊕ Fin 2 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    GL (Fin 2 ⊕ Fin 2) K where
  val := monoS (kpermS g) ε
  inv := monoS (kpermS g) (fun k => ε (kpermS g k))
  val_inv := by
    rw [monoS_mul, kpermS_sq, ← monoS_one_eq]
    congr 1
    funext k
    exact pm_mul_self (hε _)
  inv_val := by
    have hk : ∀ k, kpermS g (kpermS g k) = k := fun k => by
      have := congrArg (fun σ : Equiv.Perm (Fin 2 ⊕ Fin 2) => σ k) (kpermS_sq g)
      simpa using this
    rw [monoS_mul, kpermS_sq, ← monoS_one_eq]
    congr 1
    funext k
    simp only [hk]
    exact pm_mul_self (hε k)

theorem monoGLS_mem_sgnGroupS (g : Fin 4) (ε : Fin 2 ⊕ Fin 2 → K)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : monoGLS g ε hε ∈ sgnGroupS K := ⟨g, ε, hε, rfl⟩

end MonoS

section Explicit

variable {K : Type} [Field K]

@[expose] def spEa : Fin 2 ⊕ Fin 2 → K := Sum.elim ![1, -1] ![1, -1]

@[expose] def spEs : Fin 2 ⊕ Fin 2 → K := fun _ => 1

@[expose] def spEt : Fin 2 ⊕ Fin 2 → K := Sum.elim ![1, 1] ![-1, -1]

theorem spEa_pm (i : Fin 2 ⊕ Fin 2) : (spEa i : K) = 1 ∨ (spEa i : K) = -1 := by
  rcases i with i | i <;> fin_cases i <;> simp [spEa]

theorem spEs_pm (i : Fin 2 ⊕ Fin 2) : (spEs i : K) = 1 ∨ (spEs i : K) = -1 :=
  Or.inl rfl

theorem spEt_pm (i : Fin 2 ⊕ Fin 2) : (spEt i : K) = 1 ∨ (spEt i : K) = -1 := by
  rcases i with i | i <;> fin_cases i <;> simp [spEt]

theorem monoS_symplectic (g : Fin 4) (ε : Fin 2 ⊕ Fin 2 → K)
    (h : ∀ i j, ε i * (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0)
      (kpermS g i) (kpermS g j) * ε j = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0
        i j) :
    (monoS (kpermS g) ε)ᵀ * Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 *
      monoS (kpermS g) ε = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 := by
  ext i j
  rw [monoS_conj_gram]
  exact h i j

theorem monoGLS_a_mem : monoGLS 0 spEa spEa_pm ∈ StatedSp 2 K :=
  Subgroup.subset_closure (monoS_symplectic 0 spEa (by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [kpermS, spEa]))

theorem monoGLS_s_mem : monoGLS 1 spEs spEs_pm ∈ StatedSp 2 K :=
  Subgroup.subset_closure (monoS_symplectic 1 spEs (by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [kpermS, spEs, Equiv.swap_apply_def]))

theorem monoGLS_t_mem : monoGLS 2 spEt spEt_pm ∈ StatedSp 2 K :=
  Subgroup.subset_closure (monoS_symplectic 2 spEt (by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [kpermS, spEt, Equiv.swap_apply_def]))

end Explicit

section Irred

variable {K : Type} [Field K]

@[expose] def bvS (i : Fin 2 ⊕ Fin 2) : Fin 2 ⊕ Fin 2 → K := fun j => if i = j then 1 else 0

theorem monoS_mulVec_bvS (σ : Equiv.Perm (Fin 2 ⊕ Fin 2)) (ε : Fin 2 ⊕ Fin 2 → K)
    (j : Fin 2 ⊕ Fin 2) : monoS σ ε *ᵥ bvS j = ε j • bvS (σ j) := by
  funext i
  rw [monoS_mulVec]
  simp only [bvS, Pi.smul_apply, smul_eq_mul]
  by_cases h : σ j = i
  · have h' : j = σ⁻¹ i := by rw [← h]; simp
    simp only [eq_true h, eq_true h', ↓reduceIte, mul_one]
    rw [← h']
  · have h' : ¬ j = σ⁻¹ i := fun h' => h (by rw [h']; simp)
    simp only [eq_false h, eq_false h', ↓reduceIte, mul_zero]

theorem eq_bot_or_top_of_sp_invariant (hK : ∀ x : K, x = 0 ∨ x = 1 ∨ x = -1) (h2 : (2 : K) ≠ 0)
    (W : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (ha : ∀ w ∈ W, monoS (kpermS 0) spEa *ᵥ w ∈ W)
    (hs : ∀ w ∈ W, monoS (kpermS 1) spEs *ᵥ w ∈ W)
    (ht : ∀ w ∈ W, monoS (kpermS 2) spEt *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  have hs0 : monoS (kpermS 1) spEs *ᵥ bvS (Sum.inl 0) = (bvS (Sum.inl 1) : Fin 2 ⊕ Fin 2 → K) := by
    rw [monoS_mulVec_bvS]
    simp [spEs, kpermS, Equiv.swap_apply_def]
  have hs1 : monoS (kpermS 1) spEs *ᵥ bvS (Sum.inr 0) = (bvS (Sum.inr 1) : Fin 2 ⊕ Fin 2 → K) := by
    rw [monoS_mulVec_bvS]
    simp [spEs, kpermS, Equiv.swap_apply_def]
  have hs2 : monoS (kpermS 1) spEs *ᵥ bvS (Sum.inl 1) = (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) := by
    rw [monoS_mulVec_bvS]
    simp [spEs, kpermS, Equiv.swap_apply_def]
  have hs3 : monoS (kpermS 1) spEs *ᵥ bvS (Sum.inr 1) = (bvS (Sum.inr 0) : Fin 2 ⊕ Fin 2 → K) := by
    rw [monoS_mulVec_bvS]
    simp [spEs, kpermS, Equiv.swap_apply_def]
  have ht0 : monoS (kpermS 2) spEt *ᵥ bvS (Sum.inl 0) = (bvS (Sum.inr 0) : Fin 2 ⊕ Fin 2 → K) := by
    rw [monoS_mulVec_bvS]
    simp [spEt, kpermS, Equiv.swap_apply_def]
  have ht1 : monoS (kpermS 2) spEt *ᵥ bvS (Sum.inr 0) =
      (-1 : K) • (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) := by
    rw [monoS_mulVec_bvS]
    simp [spEt, kpermS, Equiv.swap_apply_def]
  have key : ∀ x y : K, (x ≠ 0 ∨ y ≠ 0) →
      x • (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) + y • bvS (Sum.inr 0) ∈ W → W = ⊤ := by
    intro x y hxy hu
    have hxy2 : x ^ 2 + y ^ 2 ≠ 0 := by
      intro h
      rcases hK x with hx | hx | hx <;> rcases hK y with hy | hy | hy <;>
        simp [hx, hy] at h hxy <;> exact h2 (by linear_combination h)
    have htu : (-y) • (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) + x • bvS (Sum.inr 0) ∈ W := by
      have := ht _ hu
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ht0, ht1] at this
      convert this using 1
      module
    have he1 : (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) ∈ W := by
      have h := W.sub_mem (W.smul_mem x hu) (W.smul_mem y htu)
      have hv : x • (x • (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) + y • bvS (Sum.inr 0)) -
          y • ((-y) • (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) + x • bvS (Sum.inr 0)) =
          (x ^ 2 + y ^ 2) • bvS (Sum.inl 0) := by
        module
      rw [hv] at h
      have := W.smul_mem (x ^ 2 + y ^ 2)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hxy2, one_smul] at this
    have hf1 : (bvS (Sum.inr 0) : Fin 2 ⊕ Fin 2 → K) ∈ W := by
      have := ht _ he1
      rwa [ht0] at this
    have he2 : (bvS (Sum.inl 1) : Fin 2 ⊕ Fin 2 → K) ∈ W := by
      have := hs _ he1
      rwa [hs0] at this
    have hf2 : (bvS (Sum.inr 1) : Fin 2 ⊕ Fin 2 → K) ∈ W := by
      have := hs _ hf1
      rwa [hs1] at this
    rw [Submodule.eq_top_iff']
    intro v
    rw [pi_eq_sum_univ v]
    refine W.sum_mem fun i _ => W.smul_mem _ ?_
    rcases i with i | i <;> fin_cases i
    · exact he1
    · exact he2
    · exact hf1
    · exact hf2
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have h1 : (2 * w (Sum.inl 0)) • (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) +
      (2 * w (Sum.inr 0)) • bvS (Sum.inr 0) ∈ W := by
    have := W.add_mem hwW (ha w hwW)
    have hv : w + monoS (kpermS 0) spEa *ᵥ w = (2 * w (Sum.inl 0)) •
        (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) + (2 * w (Sum.inr 0)) • bvS (Sum.inr 0) := by
      funext i
      rw [Pi.add_apply, monoS_mulVec]
      rcases i with i | i <;> fin_cases i <;> simp [spEa, kpermS, bvS] <;> ring
    rwa [hv] at this
  have h2' : (2 * w (Sum.inl 1)) • (bvS (Sum.inl 1) : Fin 2 ⊕ Fin 2 → K) +
      (2 * w (Sum.inr 1)) • bvS (Sum.inr 1) ∈ W := by
    have := W.sub_mem hwW (ha w hwW)
    have hv : w - monoS (kpermS 0) spEa *ᵥ w = (2 * w (Sum.inl 1)) •
        (bvS (Sum.inl 1) : Fin 2 ⊕ Fin 2 → K) + (2 * w (Sum.inr 1)) • bvS (Sum.inr 1) := by
      funext i
      rw [Pi.sub_apply, monoS_mulVec]
      rcases i with i | i <;> fin_cases i <;> simp [spEa, kpermS, bvS] <;> ring
    rwa [hv] at this
  have h3 : (2 * w (Sum.inl 1)) • (bvS (Sum.inl 0) : Fin 2 ⊕ Fin 2 → K) +
      (2 * w (Sum.inr 1)) • bvS (Sum.inr 0) ∈ W := by
    have := hs _ h2'
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hs2, hs3] at this
    exact this
  by_cases hA : w (Sum.inl 0) ≠ 0 ∨ w (Sum.inr 0) ≠ 0
  · refine key _ _ ?_ h1
    rcases hA with hA | hA
    · exact Or.inl (mul_ne_zero h2 hA)
    · exact Or.inr (mul_ne_zero h2 hA)
  · push Not at hA
    have hB : w (Sum.inl 1) ≠ 0 ∨ w (Sum.inr 1) ≠ 0 := by
      by_contra hB
      push Not at hB
      apply hw0
      funext i
      rcases i with i | i <;> fin_cases i
      · exact hA.1
      · exact hB.1
      · exact hA.2
      · exact hB.2
    refine key _ _ ?_ h3
    rcases hB with hB | hB
    · exact Or.inl (mul_ne_zero h2 hB)
    · exact Or.inr (mul_ne_zero h2 hB)

end Irred

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
