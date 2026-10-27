module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

section Mat

variable {K : Type} [Field K]

@[expose] noncomputable def l514y0_D (η : Kˣ) : GL (Fin 3) K :=
  GeneralLinearGroup.scalar (Fin 3) η⁻¹ * diagE (η ^ 3)

theorem l514y0_D_eq (η : Kˣ) : (l514y0_D η : GL (Fin 3) K) = diagUnits (η ^ 2) η⁻¹ η⁻¹ := by
  apply Units.ext
  rw [l514y0_D, Units.val_mul, coe_scalar_eq_smul, coe_diagE, coe_diagUnits]
  have h0 : (η : K) ≠ 0 := η.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
  all_goals field_simp

theorem l514y0_commute_D_iff (η : Kˣ) (s : GL (Fin 3) K) :
    Commute s (l514y0_D η) ↔ Commute s (diagE (η ^ 3)) := by
  have hc : Commute s (GeneralLinearGroup.scalar (Fin 3) η⁻¹) := commute_scalar η⁻¹ s
  unfold l514y0_D
  constructor
  · intro h
    have := hc.inv_right.mul_right h
    rwa [inv_mul_cancel_left] at this
  · intro h
    exact hc.mul_right h

theorem l514y0_diagE_pow_three (e : Kˣ) : diagE e ^ 3 = diagE (e ^ 3) := by
  have h : ∀ a b : Kˣ, diagE a * diagE b = diagE (a * b) := fun a b => by
    unfold diagE
    rw [diagUnits_mul, mul_one]
  rw [pow_succ, pow_two, h, h, pow_succ, pow_two]

theorem l514y0_D_cube (η : Kˣ) (h9 : η ^ 9 = 1) :
    l514y0_D η ^ 3 = GeneralLinearGroup.scalar (Fin 3) (η⁻¹ ^ 3) := by
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) η⁻¹ : GL (Fin 3) K) (diagE (η ^ 3)) :=
    (commute_scalar η⁻¹ _).symm
  unfold l514y0_D
  rw [hc.mul_pow, l514y0_diagE_pow_three, ← pow_mul, show 3 * 3 = 9 from rfl, h9]
  have h1 : (diagE (1 : Kˣ) : GL (Fin 3) K) = 1 := by
    unfold diagE
    apply Units.ext
    rw [coe_diagUnits]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h1, mul_one, map_pow]

theorem l514y0_D_not_scalar (η : Kˣ) (h3 : η ^ 3 ≠ 1) :
    ∀ c : Kˣ, l514y0_D η ≠ GeneralLinearGroup.scalar (Fin 3) c := by
  intro c h
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  rw [l514y0_D_eq, coe_diagUnits, GeneralLinearGroup.coe_scalar] at this
  have h00 := congrFun (congrFun this 0) 0
  have h11 := congrFun (congrFun this 1) 1
  simp at h00 h11
  apply h3
  have h0 : (η : K) ≠ 0 := η.ne_zero
  have : (η : K) ^ 3 = 1 := by
    have e : (η : K) ^ 2 = (η : K)⁻¹ := h00.trans h11.symm
    field_simp at e
    exact e
  exact Units.ext (by simpa using this)

theorem l514y0_frobGL_scalar (σ : K ≃+* K) (c : Kˣ) :
    frobGL σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_frobGL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, h]

theorem l514y0_frobGL_diagE (σ : K ≃+* K) (e : Kˣ) :
    frobGL σ (diagE e) = diagE (Units.map (σ : K →* K) e) := by
  apply Units.ext
  rw [coe_frobGL, coe_diagE, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem l514y0_frobGL_D (σ : K ≃+* K) (η : Kˣ) (hη : σ ((η : K) ^ 3) = (η : K) ^ 3) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧
      frobGL σ (l514y0_D η) = GeneralLinearGroup.scalar (Fin 3) c * l514y0_D η := by
  set η' : Kˣ := Units.map (σ : K →* K) η with hη'
  have h3 : η' ^ 3 = η ^ 3 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    simpa [hη', map_pow] using hη
  refine ⟨η'⁻¹ * η, ?_, ?_⟩
  · rw [mul_pow, inv_pow, h3, inv_mul_cancel]
  · unfold l514y0_D
    have e1 : Units.map (σ : K →* K) (η ^ 3) = η ^ 3 := by rw [map_pow, ← hη', h3]
    have e2 : Units.map (σ : K →* K) η⁻¹ = η'⁻¹ := by rw [map_inv]
    rw [map_mul, l514y0_frobGL_scalar, l514y0_frobGL_diagE, e1, e2, ← mul_assoc, ← map_mul]
    congr 2
    group

theorem l514y0_trace_D (η : Kˣ) :
    Matrix.trace ((l514y0_D η : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (η : K) ^ 2 + (η : K)⁻¹ + (η : K)⁻¹ := by
  rw [l514y0_D_eq, coe_diagUnits, Matrix.trace_diagonal, Fin.sum_univ_three]
  simp [Units.val_inv_eq_inv_val]

theorem l514y0_scalar_eq_one_of_conj (η : Kˣ) (h3 : (3 : K) ≠ 0) (hζ : η ^ 3 ≠ 1)
    (hζ3 : (η ^ 3) ^ 3 = 1) (s : GL (Fin 3) K) (c : Kˣ)
    (h : s * l514y0_D η * s⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * l514y0_D η) : c = 1 := by
  have h1 := congrArg (fun g : GL (Fin 3) K => Matrix.trace (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Units.val_mul] at h1
  have e1 : Matrix.trace (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((l514y0_D η : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      Matrix.trace ((l514y0_D η : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have e2 : Matrix.trace (((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * ((l514y0_D η : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (c : K) * Matrix.trace ((l514y0_D η : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  rw [e1, e2] at h1
  have h0 : (η : K) ≠ 0 := η.ne_zero
  have ht : (η : K) ^ 3 ≠ 1 := fun h => hζ (Units.ext (by simpa using h))
  have ht3 : ((η : K) ^ 3) ^ 3 = 1 := by simpa using congrArg Units.val hζ3
  have hq : ((η : K) ^ 3) ^ 2 + (η : K) ^ 3 + 1 = 0 := by
    have : ((η : K) ^ 3 - 1) * (((η : K) ^ 3) ^ 2 + (η : K) ^ 3 + 1) = 0 := by
      linear_combination ht3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) ht
    · exact h
  have htr : Matrix.trace ((l514y0_D η : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    rw [l514y0_trace_D]
    intro h
    have h2 : (η : K) ^ 3 + 2 = 0 := by
      field_simp at h
      linear_combination h
    have h4 : (3 : K) = 0 := by
      have : (η : K) ^ 3 = -2 := by linear_combination h2
      rw [this] at hq
      linear_combination hq
    exact h3 h4
  have : ((c : K) - 1) * Matrix.trace ((l514y0_D η : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.1 this with h | h
  · exact Units.ext (sub_eq_zero.1 h)
  · exact absurd h htr

end Mat



section Mem

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem l514y0_diagUnits_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {a b c : Kˣ}
    (habc : (a : K) * b * c = 1)
    (hu : π = false → (a : K) ^ (p ^ f + 1) = 1 ∧ (b : K) ^ (p ^ f + 1) = 1 ∧
      (c : K) ^ (p ^ f + 1) = 1) :
    diagUnits a b c ∈ slPi π 3 (p ^ f) K := by
  rw [mem_slPi_iff hπ]
  refine ⟨?_, ?_⟩
  · cases π
    · have h := hπ rfl
      obtain ⟨ha, hb, hc⟩ := hu rfl
      rw [mem_glPi_false h, coe_diagUnits]
      have e1 : h.bar (a : K) * a = 1 := by rw [h.bar_apply, ← pow_succ]; exact ha
      have e2 : h.bar (b : K) * b = 1 := by rw [h.bar_apply, ← pow_succ]; exact hb
      have e3 : h.bar (c : K) * c = 1 := by rw [h.bar_apply, ← pow_succ]; exact hc
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, e1, e2, e3]
    · exact mem_glPi_true _ _
  · rw [coe_diagUnits, det_diagonal, Fin.prod_univ_three]
    simpa using habc

theorem l514y0_D_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {η : Kˣ}
    (h : π = false → (η : K) ^ (p ^ f + 1) = 1) : l514y0_D η ∈ slPi π 3 (p ^ f) K := by
  rw [l514y0_D_eq]
  refine l514y0_diagUnits_mem_slPi hπ ?_ fun hf => ?_
  · have h0 : (η : K) ≠ 0 := η.ne_zero
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  · have h1 := h hf
    refine ⟨?_, ?_, ?_⟩
    · simp only [Units.val_pow_eq_pow_val]
      rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
    · simp only [Units.val_inv_eq_inv_val]
      rw [inv_pow, h1, inv_one]
    · simp only [Units.val_inv_eq_inv_val]
      rw [inv_pow, h1, inv_one]

theorem l514y0_scalar_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {c : Kˣ}
    (h3 : c ^ 3 = 1) (hu : π = false → (c : K) ^ (p ^ f + 1) = 1) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ slPi π 3 (p ^ f) K := by
  have e : (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) = diagUnits c c c := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, coe_diagUnits]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  rw [e]
  refine l514y0_diagUnits_mem_slPi hπ ?_ fun hf => ⟨hu hf, hu hf, hu hf⟩
  have : ((c ^ 3 : Kˣ) : K) = 1 := by rw [h3]; rfl
  simpa [pow_succ, mul_assoc] using this

end Mem

section Eta

theorem l514y0_cube_root_cases {K : Type} [Field K] {ζ t : K} (hζ3 : ζ ^ 3 = 1) (hζ : ζ ≠ 1)
    (ht3 : t ^ 3 = 1) (ht : t ≠ 1) : t = ζ ∨ t = ζ ^ 2 := by
  have h1 : ζ ^ 2 + ζ + 1 = 0 := by
    have : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hζ
    · exact h
  have h2 : t ^ 2 + t + 1 = 0 := by
    have : (t - 1) * (t ^ 2 + t + 1) = 0 := by linear_combination ht3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) ht
    · exact h
  have : (t - ζ) * (t - ζ ^ 2) = 0 := by linear_combination h2 - t * h1 + hζ3
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

theorem l514y0_exists_eta {K : Type} [Field K] [Finite K] (h9 : 9 ∣ Nat.card K - 1) {ζ : K}
    (hζ3 : ζ ^ 3 = 1) (hζ : ζ ≠ 1) : ∃ η : Kˣ, η ^ 9 = 1 ∧ (η : K) ^ 3 = ζ := by
  have hcard : Nat.card (rootsOfUnity 9 K) = 9 := CFSG.LinearGroups.card_rootsOfUnity_of_dvd h9
  have hcyc : IsCyclic (rootsOfUnity 9 K) := rootsOfUnity.isCyclic K 9
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity 9 K)
  rw [hcard] at hg
  set η₁ : Kˣ := (g : Kˣ) with hη₁
  have h91 : η₁ ^ 9 = 1 := (mem_rootsOfUnity _ _).1 g.2
  have h31 : η₁ ^ 3 ≠ 1 := by
    intro h
    have : g ^ 3 = 1 := Subtype.ext (by simpa [hη₁] using h)
    have := orderOf_dvd_of_pow_eq_one this
    rw [hg] at this
    omega
  have ht3 : ((η₁ : K) ^ 3) ^ 3 = 1 := by
    have := congrArg Units.val h91
    simpa [← pow_mul] using this
  have ht : (η₁ : K) ^ 3 ≠ 1 := fun h => h31 (Units.ext (by simpa using h))
  rcases l514y0_cube_root_cases hζ3 hζ ht3 ht with h | h
  · exact ⟨η₁, h91, h⟩
  · refine ⟨η₁ ^ 2, by rw [← pow_mul, mul_comm, pow_mul, h91, one_pow], ?_⟩
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, h, ← pow_mul]
    have : ζ ^ 4 = ζ := by
      calc ζ ^ 4 = ζ ^ 3 * ζ := by ring
        _ = ζ := by rw [hζ3, one_mul]
    simpa using this

theorem l514y0_nine_dvd {q q₀ : ℕ} (π : Bool) (hq : q = q₀ ^ 3) (h₀ : ModThree π q₀) :
    (π = true → q % 9 = 1) ∧ (π = false → q % 9 = 8) := by
  have hm : q₀ ^ 3 % 9 = (q₀ % 9) ^ 3 % 9 := Nat.pow_mod _ _ _
  cases π
  · refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    change q₀ % 3 = 2 at h₀
    have : q₀ % 9 = 2 ∨ q₀ % 9 = 5 ∨ q₀ % 9 = 8 := by omega
    rw [hq, hm]
    rcases this with h | h | h <;> rw [h] <;> norm_num
  · refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    change q₀ % 3 = 1 at h₀
    have : q₀ % 9 = 1 ∨ q₀ % 9 = 4 ∨ q₀ % 9 = 7 := by omega
    rw [hq, hm]
    rcases this with h | h | h <;> rw [h] <;> norm_num

end Eta

end CFSG.HardMathSupport.Solomon.Coordinator
