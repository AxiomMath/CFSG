module

public import CFSG.LieType.SeitzGeneration.SingerUMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Powers

variable {F : Type} [Field F] {n : ℕ}

theorem pow_mul_eq_of_smul_comm {X Y : Matrix (Fin n) (Fin n) F} {κ : F} (hκ : κ ≠ 0)
    (h : X * Y = κ • (Y * X)) (k : ℕ) : Y ^ k * X = (κ⁻¹) ^ k • (X * Y ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hYX : Y * X = κ⁻¹ • (X * Y) := by
      rw [h, smul_smul, inv_mul_cancel₀ hκ, one_smul]
    calc Y ^ (k + 1) * X = Y ^ k * (Y * X) := by rw [pow_succ, Matrix.mul_assoc]
      _ = Y ^ k * (κ⁻¹ • (X * Y)) := by rw [hYX]
      _ = κ⁻¹ • ((Y ^ k * X) * Y) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = κ⁻¹ • ((κ⁻¹ ^ k • (X * Y ^ k)) * Y) := by rw [ih]
      _ = (κ⁻¹) ^ (k + 1) • (X * Y ^ (k + 1)) := by
        rw [Matrix.smul_mul, smul_smul, ← pow_succ', pow_succ Y k, Matrix.mul_assoc]

theorem mul_pow_eq_of_smul_comm {X Y : Matrix (Fin n) (Fin n) F} {κ : F} (hκ : κ ≠ 0)
    (h : X * Y = κ • (Y * X)) (m : ℕ) :
    (X * Y) ^ m = (κ⁻¹) ^ (∑ i ∈ Finset.range m, i) • (X ^ m * Y ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc (X * Y) ^ (m + 1) = (X * Y) ^ m * (X * Y) := by rw [pow_succ]
      _ = (κ⁻¹ ^ (∑ i ∈ Finset.range m, i) • (X ^ m * Y ^ m)) * (X * Y) := by rw [ih]
      _ = κ⁻¹ ^ (∑ i ∈ Finset.range m, i) • (X ^ m * (Y ^ m * X) * Y) := by
        rw [Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
      _ = κ⁻¹ ^ (∑ i ∈ Finset.range m, i) • (X ^ m * ((κ⁻¹) ^ m • (X * Y ^ m)) * Y) := by
        rw [pow_mul_eq_of_smul_comm hκ h m]
      _ = κ⁻¹ ^ (∑ i ∈ Finset.range (m + 1), i) • (X ^ (m + 1) * Y ^ (m + 1)) := by
        rw [Finset.sum_range_succ, pow_add, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        congr 1
        simp only [pow_succ, Matrix.mul_assoc]

theorem mul_pow_five_of_smul_comm {X Y : Matrix (Fin n) (Fin n) F} {κ : F} (hκ5 : κ ^ 5 = 1)
    (h : X * Y = κ • (Y * X)) : (X * Y) ^ 5 = X ^ 5 * Y ^ 5 := by
  have hκ : κ ≠ 0 := by
    rintro rfl
    simp at hκ5
  rw [mul_pow_eq_of_smul_comm hκ h 5]
  have h10 : (κ⁻¹) ^ (∑ i ∈ Finset.range 5, i) = 1 := by
    have : ∑ i ∈ Finset.range 5, i = 5 * 2 := by decide
    rw [this, pow_mul, inv_pow, hκ5]
    simp
  rw [h10, one_smul]

end Powers

section Lines

variable {ℓ f : ℕ} {F : Type} [Field F]

theorem eq_top_of_heis_pair_of_split [Finite F] [Fact ℓ.Prime] [CharP F ℓ]
    (h : UnitaryFieldData ℓ f F) (hpq : 5 ∣ ℓ ^ f + 1)
    {u v : GL (Fin 5) F} (hu : u ∈ primeFormUnitary h (idGram F 5))
    (hv : v ∈ primeFormUnitary h (idGram F 5)) {ζ : F} (hζ : IsPrimitiveRoot ζ 5)
    (hcomm : (u : Matrix (Fin 5) (Fin 5) F) * v = ζ • ((v : Matrix (Fin 5) (Fin 5) F) * u))
    {cu cv : F} (hcu : ((u ^ 5 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = cu • 1)
    (hcv : ((v ^ 5 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = cv • 1)
    (hsplit : ∃ μ : F, μ ^ 5 = cu) {H : Subgroup (SUid (unitaryInvolution F ℓ f) 5)}
    (h0 : HeisTensor.Cent H (u : Matrix (Fin 5) (Fin 5) F))
    (h1 : HeisTensor.Cent H (v : Matrix (Fin 5) (Fin 5) F)) : H = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ν, hν⟩ := hsplit
  have hcu0 : cu ≠ 0 := scalar_ne_zero_of_pow hcu
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hν
    exact hcu0 hν.symm
  have hcuN : h.bar cu * cu = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) hu hcu
  have hcuN' : cu ^ (ℓ ^ f + 1) = 1 := by
    have h2 := hcuN
    rw [h.bar_apply, ← pow_succ] at h2
    exact h2
  have hνN : h.bar ν * ν = 1 :=
    bar_mul_eq_one_of_pow_eq h Nat.prime_five (by norm_num) hpq hν0 hν hcuN'
  have hu5 : ((u ^ 5 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = (ν ^ 5) • 1 := by
    rw [hcu, hν]
  by_cases hs : ∃ μ : F, μ ^ 5 = cv
  · exact eq_top_of_heis_pair_prime_gu h (torusFourierGenU_of_prime h le_rfl hpq) Nat.prime_five
      le_rfl hpq hu hv hζ hν0 hνN hs hu5 hcv hcomm h0 h1
  · exact eq_top_of_heis_pair_prime_nonsplit h (singerTorusGenU_of_prime h le_rfl hpq)
      Nat.prime_five le_rfl hpq hu hv hζ hν0 hνN hs hu5 hcv hcomm h0 h1

theorem exists_line_index (m₀ m₁ : ℕ) (h0 : ¬ 5 ∣ m₀) (h1 : ¬ 5 ∣ m₁) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ 5 ∣ m₀ + j * m₁ := by
  have h0' : m₀ % 5 = 1 ∨ m₀ % 5 = 2 ∨ m₀ % 5 = 3 ∨ m₀ % 5 = 4 := by omega
  have h1' : m₁ % 5 = 1 ∨ m₁ % 5 = 2 ∨ m₁ % 5 = 3 ∨ m₁ % 5 = 4 := by omega
  rcases h0' with h0' | h0' | h0' | h0' <;> rcases h1' with h1' | h1' | h1' | h1' <;>
    first
    | exact ⟨1, by omega, by omega, by omega⟩
    | exact ⟨2, by omega, by omega, by omega⟩
    | exact ⟨3, by omega, by omega, by omega⟩
    | exact ⟨4, by omega, by omega, by omega⟩

theorem exists_pow_five_of_dvd [Finite F] {γ : Fˣ} {m : ℕ} (hm : 5 ∣ m) :
    ∃ μ : F, μ ^ 5 = ((γ ^ m : Fˣ) : F) := by
  obtain ⟨t, rfl⟩ := hm
  refine ⟨((γ ^ t : Fˣ) : F), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]

theorem eq_top_of_heis_lines [Finite F] [Fact ℓ.Prime] [CharP F ℓ]
    (h : UnitaryFieldData ℓ f F) (hpq : 5 ∣ ℓ ^ f + 1) {g₀ g₁ : GL (Fin 5) F}
    (hg₀ : g₀ ∈ primeFormUnitary h (idGram F 5)) (hg₁ : g₁ ∈ primeFormUnitary h (idGram F 5))
    {ζ : F} (hζ : IsPrimitiveRoot ζ 5)
    (hcomm : (g₀ : Matrix (Fin 5) (Fin 5) F) * g₁ = ζ • ((g₁ : Matrix (Fin 5) (Fin 5) F) * g₀))
    {c₀ c₁ : F} (h₀ : ((g₀ ^ 5 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = c₀ • 1)
    (h₁ : ((g₁ ^ 5 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = c₁ • 1)
    {H : Subgroup (SUid (unitaryInvolution F ℓ f) 5)}
    (hH : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) →
      HeisTensor.Cent H (((g₀ ^ a * g₁ ^ b : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F)) :
    H = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hCent0 : HeisTensor.Cent H (g₀ : Matrix (Fin 5) (Fin 5) F) := by
    simpa using hH 1 0 (by omega)
  have hCent1 : HeisTensor.Cent H (g₁ : Matrix (Fin 5) (Fin 5) F) := by
    simpa using hH 0 1 (by omega)
  have hcomm' : (g₁ : Matrix (Fin 5) (Fin 5) F) * g₀ =
      ζ⁻¹ • ((g₀ : Matrix (Fin 5) (Fin 5) F) * g₁) := by
    rw [hcomm, smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  by_cases hs₀ : ∃ μ : F, μ ^ 5 = c₀
  · exact eq_top_of_heis_pair_of_split h hpq hg₀ hg₁ hζ hcomm h₀ h₁ hs₀ hCent0 hCent1
  by_cases hs₁ : ∃ μ : F, μ ^ 5 = c₁
  · have hζi : IsPrimitiveRoot ζ⁻¹ 5 := hζ.inv
    exact eq_top_of_heis_pair_of_split h hpq hg₁ hg₀ hζi hcomm' h₁ h₀ hs₁ hCent1 hCent0
  have hc₀0 : c₀ ≠ 0 := scalar_ne_zero_of_pow h₀
  have hc₁0 : c₁ ≠ 0 := scalar_ne_zero_of_pow h₁
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hpow : ∀ x : Fˣ, ∃ m : ℕ, γ ^ m = x := fun x =>
    (Submonoid.mem_powers_iff _ _).1 ((mem_powers_iff_mem_zpowers).2 (hγ x))
  obtain ⟨m₀, hm₀⟩ := hpow (Units.mk0 c₀ hc₀0)
  obtain ⟨m₁, hm₁⟩ := hpow (Units.mk0 c₁ hc₁0)
  have hc₀' : ((γ ^ m₀ : Fˣ) : F) = c₀ := by rw [hm₀]; rfl
  have hc₁' : ((γ ^ m₁ : Fˣ) : F) = c₁ := by rw [hm₁]; rfl
  have hn₀ : ¬ 5 ∣ m₀ := fun hd => by
    obtain ⟨μ, hμ⟩ := exists_pow_five_of_dvd (γ := γ) hd
    exact hs₀ ⟨μ, by rw [hμ, hc₀']⟩
  have hn₁ : ¬ 5 ∣ m₁ := fun hd => by
    obtain ⟨μ, hμ⟩ := exists_pow_five_of_dvd (γ := γ) hd
    exact hs₁ ⟨μ, by rw [hμ, hc₁']⟩
  obtain ⟨j, hj1, hj4, hjd⟩ := exists_line_index m₀ m₁ hn₀ hn₁
  set X : Matrix (Fin 5) (Fin 5) F := (g₀ : Matrix (Fin 5) (Fin 5) F) with hX
  set G : Matrix (Fin 5) (Fin 5) F := (g₁ : Matrix (Fin 5) (Fin 5) F) with hG
  have hX5 : X ^ 5 = c₀ • 1 := by rw [hX, ← Units.val_pow_eq_pow_val]; exact h₀
  have hG5 : G ^ 5 = c₁ • 1 := by rw [hG, ← Units.val_pow_eq_pow_val]; exact h₁
  have hcommj : X * G ^ j = (ζ ^ j) • (G ^ j * X) := by
    have h1 := pow_mul_eq_of_smul_comm hζ0 hcomm j
    rw [h1, smul_smul, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow, one_smul]
  have h5 : (ζ ^ j) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ5, one_pow]
  have hcuM : (X * G ^ j) ^ 5 = (c₀ * c₁ ^ j) • 1 := by
    rw [mul_pow_five_of_smul_comm h5 hcommj, hX5, ← pow_mul, mul_comm j 5, pow_mul, hG5,
      smul_pow, one_pow, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have hcu : (((g₀ * g₁ ^ j) ^ 5 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      (c₀ * c₁ ^ j) • 1 := by
    rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val]
    exact hcuM
  have hsplit : ∃ μ : F, μ ^ 5 = c₀ * c₁ ^ j := by
    obtain ⟨μ, hμ⟩ := exists_pow_five_of_dvd (γ := γ) hjd
    refine ⟨μ, ?_⟩
    rw [hμ]
    calc ((γ ^ (m₀ + j * m₁) : Fˣ) : F) = ((γ ^ m₀ * (γ ^ m₁) ^ j : Fˣ) : F) := by
          rw [pow_add, mul_comm j m₁, pow_mul]
      _ = ((γ ^ m₀ : Fˣ) : F) * ((γ ^ m₁ : Fˣ) : F) ^ j := by
          simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      _ = c₀ * c₁ ^ j := by rw [hc₀', hc₁']
  have hu : g₀ * g₁ ^ j ∈ primeFormUnitary h (idGram F 5) := mul_mem hg₀ (pow_mem hg₁ j)
  have huv : ((g₀ * g₁ ^ j : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
      (g₁ : Matrix (Fin 5) (Fin 5) F) =
      ζ • ((g₁ : Matrix (Fin 5) (Fin 5) F) * ((g₀ * g₁ ^ j : GL (Fin 5) F) :
        Matrix (Fin 5) (Fin 5) F)) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    change X * G ^ j * G = ζ • (G * (X * G ^ j))
    calc X * G ^ j * G = X * (G ^ j * G) := by rw [Matrix.mul_assoc]
      _ = X * (G * G ^ j) := by rw [← pow_succ, ← pow_succ']
      _ = (X * G) * G ^ j := by rw [Matrix.mul_assoc]
      _ = (ζ • (G * X)) * G ^ j := by rw [hcomm]
      _ = ζ • (G * (X * G ^ j)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
  exact eq_top_of_heis_pair_of_split h hpq hu hg₁ hζ huv hcu h₁ hsplit
    (by simpa using hH 1 j (by omega)) hCent1

end Lines

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
