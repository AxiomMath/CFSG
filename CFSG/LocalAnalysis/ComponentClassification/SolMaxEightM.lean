module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightL
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightD

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem isPGroup_sup_zpowers_of_le_centralizer {G : Type*} [Group G] {p : ℕ} {P : Subgroup G}
    {x : G} (hP : IsPGroup p P) (hx : IsPGroup p (zpowers x))
    (hPx : P ≤ centralizer ({x} : Set G)) : IsPGroup p (P ⊔ zpowers x : Subgroup G) := by
  refine IsPGroup.to_sup_of_normal_right' hP hx
    (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
  intro y hy
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have hxy : Commute x y := (mem_centralizer_singleton_iff.mp (hPx hy)).symm
  exact (hxy.zpow_left k).eq

theorem exists_eq_conj_of_odd_orderOf {G : Type*} [Group G] {n t : G} (hn : Odd (orderOf n))
    (ht2 : t * t = 1) (hx2 : n * t * (n * t) = 1) : ∃ c : G, n * t = c * t * c⁻¹ := by
  obtain ⟨m, hm⟩ := hn
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htn : t * n * t⁻¹ = n⁻¹ := by
    rw [htinv]
    calc t * n * t = n⁻¹ * (n * t * (n * t)) := by group
      _ = n⁻¹ := by rw [hx2, mul_one]
  have hpow : t * n ^ (m + 1) * t⁻¹ = (n ^ (m + 1))⁻¹ := by
    rw [← conj_pow, htn, inv_pow]
  refine ⟨n ^ (m + 1), ?_⟩
  have h1 : t * (n ^ (m + 1))⁻¹ = n ^ (m + 1) * t := by
    rw [← hpow]
    calc t * (t * n ^ (m + 1) * t⁻¹) = t * t * n ^ (m + 1) * t⁻¹ := by simp only [mul_assoc]
      _ = n ^ (m + 1) * t := by rw [ht2, one_mul, htinv]
  have h3 : n ^ (2 * m + 1) = 1 := by rw [← hm, pow_orderOf_eq_one]
  calc n * t = n ^ (2 * m + 1) * n * t := by rw [h3, one_mul]
    _ = n ^ (m + 1) * (n ^ (m + 1) * t) := by
        rw [← pow_succ, ← mul_assoc, ← pow_add]
        congr 2
        ring
    _ = n ^ (m + 1) * t * (n ^ (m + 1))⁻¹ := by rw [mul_assoc (n ^ (m + 1)) t, h1]

theorem exists_eight_swap_frame {σ τ : Perm (Fin 9)} (hσ2 : σ * σ = 1)
    (hσ8 : σ.support.card = 8) (hτ2 : τ.support.card = 2) (hτσ : τ * σ = σ * τ) :
    ∃ v : Fin 4 → Perm (Fin 9), v 0 = τ ∧ (∀ i, v i * σ = σ * v i) ∧
      (∀ i j, v i * v j = v j * v i) ∧ (∀ i, v i * v i = 1) ∧ (∀ i, (v i).support.card = 2) ∧
      (∀ i, v i * τ ∈ alternatingGroup (Fin 9)) ∧
      ∀ i j, i ≠ j → v i * v j ≠ 1 ∧ (v i * v j).support.card ≤ 4 := by
  classical
  set σ₀ : Perm (Fin 9) := SixGen.permOf [(0, 1), (2, 3), (4, 5), (6, 7)] with hσ₀def
  have hct : σ₀.cycleType = σ.cycleType := by
    rw [SixGen.cycleType_of_mul_self (k := 4) hσ2 (by norm_num) hσ8,
      SixGen.cycleType_of_mul_self (k := 4) (by decide) (by norm_num) (by decide)]
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct)
  set τ' := π⁻¹ * τ * π with hτ'def
  have hτ'σ₀ : τ' * σ₀ = σ₀ * τ' := by
    have h1 : σ₀ = π⁻¹ * σ * π := by rw [← hπ]; group
    rw [h1, hτ'def]
    calc π⁻¹ * τ * π * (π⁻¹ * σ * π) = π⁻¹ * (τ * σ) * π := by group
      _ = π⁻¹ * (σ * τ) * π := by rw [hτσ]
      _ = π⁻¹ * σ * π * (π⁻¹ * τ * π) := by group
  have hτ'2 : τ'.support.card = 2 := by
    rw [hτ'def]
    have := Perm.card_support_conj (σ := π⁻¹) (τ := τ)
    rw [inv_inv] at this
    rw [this, hτ2]
  obtain ⟨a, b, hab, hτ'ab⟩ := Perm.card_support_eq_two.mp hτ'2
  set w₁ : Fin 4 → Perm (Fin 9) := ![swap 0 1, swap 2 3, swap 4 5, swap 6 7] with hw₁def
  set w₂ : Fin 4 → Perm (Fin 9) := ![swap 2 3, swap 0 1, swap 4 5, swap 6 7] with hw₂def
  set w₃ : Fin 4 → Perm (Fin 9) := ![swap 4 5, swap 0 1, swap 2 3, swap 6 7] with hw₃def
  set w₄ : Fin 4 → Perm (Fin 9) := ![swap 6 7, swap 0 1, swap 2 3, swap 4 5] with hw₄def
  have hcases : ∀ a b : Fin 9, a ≠ b → swap a b * σ₀ = σ₀ * swap a b →
      swap a b = w₁ 0 ∨ swap a b = w₂ 0 ∨ swap a b = w₃ 0 ∨ swap a b = w₄ 0 := by
    decide
  have hframe : ∀ w : Fin 4 → Perm (Fin 9), (w = w₁ ∨ w = w₂ ∨ w = w₃ ∨ w = w₄) →
      (∀ i, w i * σ₀ = σ₀ * w i) ∧ (∀ i j, w i * w j = w j * w i) ∧ (∀ i, w i * w i = 1) ∧
      (∀ i, (w i).support.card = 2) ∧ (∀ i, Perm.sign (w i * w 0) = 1) ∧
      ∀ i j, i ≠ j → w i * w j ≠ 1 ∧ (w i * w j).support.card ≤ 4 := by
    rintro w (rfl | rfl | rfl | rfl) <;> decide
  obtain ⟨w, hw0, hwσ, hww, hw2, hwc, hwA, hwne⟩ : ∃ w : Fin 4 → Perm (Fin 9), w 0 = τ' ∧
      (∀ i, w i * σ₀ = σ₀ * w i) ∧ (∀ i j, w i * w j = w j * w i) ∧ (∀ i, w i * w i = 1) ∧
      (∀ i, (w i).support.card = 2) ∧ (∀ i, Perm.sign (w i * w 0) = 1) ∧
      ∀ i j, i ≠ j → w i * w j ≠ 1 ∧ (w i * w j).support.card ≤ 4 := by
    rcases hcases a b hab (by rw [← hτ'ab]; exact hτ'σ₀) with h | h | h | h
    · exact ⟨w₁, by rw [hτ'ab, h], hframe w₁ (Or.inl rfl)⟩
    · exact ⟨w₂, by rw [hτ'ab, h], hframe w₂ (Or.inr (Or.inl rfl))⟩
    · exact ⟨w₃, by rw [hτ'ab, h], hframe w₃ (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨w₄, by rw [hτ'ab, h], hframe w₄ (Or.inr (Or.inr (Or.inr rfl)))⟩
  have hmul : ∀ x y : Perm (Fin 9), π * x * π⁻¹ * (π * y * π⁻¹) = π * (x * y) * π⁻¹ := by
    intro x y; group
  have hinj : ∀ x y : Perm (Fin 9), π * x * π⁻¹ = π * y * π⁻¹ → x = y := by
    intro x y h
    have := congrArg (fun z => π⁻¹ * z * π) h
    simpa [mul_assoc] using this
  have hτ : π * w 0 * π⁻¹ = τ := by rw [hw0, hτ'def]; group
  refine ⟨fun i => π * w i * π⁻¹, hτ, fun i => ?_, fun i j => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_, fun i j hij => ⟨?_, ?_⟩⟩
  · dsimp only
    rw [← hπ, hmul, hmul, hwσ i]
  · dsimp only
    rw [hmul, hmul, hww i j]
  · dsimp only
    rw [hmul, hw2 i]; group
  · exact (Perm.card_support_conj (σ := π) (τ := w i)).trans (hwc i)
  · dsimp only
    rw [← hτ, hmul]
    exact (alternatingGroup.normal (α := Fin 9)).conj_mem _
      (Perm.mem_alternatingGroup.mpr (hwA i)) π
  · dsimp only
    rw [hmul]
    intro h
    apply (hwne i j hij).1
    apply hinj
    rw [h]; group
  · dsimp only
    rw [hmul]
    exact (Perm.card_support_conj (σ := π) (τ := w i * w j)).trans_le (hwne i j hij).2

variable {X : Type} [Group X] {M : Subgroup X}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}

theorem IsPermAction.exists_involution_lift_of_two_group (hρ : IsPermAction θ ρ) [Finite X]
    {B : Subgroup X} (hBN : B ≤ normalizer (M : Set X)) (hB2 : IsPGroup 2 B)
    {b : Perm (Fin 9)} (hbA : b ∈ alternatingGroup (Fin 9)) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hb : ∀ (g : X) (hg : g ∈ B), b * ρ ⟨g, hBN hg⟩ = ρ ⟨g, hBN hg⟩ * b) :
    ∃ m : X, ∃ hm : m ∈ M, m ∈ centralizer (B : Set X) ∧ m * m = 1 ∧
      ρ ⟨m, le_normalizer hm⟩ = b := by
  classical
  obtain ⟨x, hxB, hxθ⟩ := hρ.exists_lift_of_isPGroup hBN hB2 (b := ⟨b, hbA⟩) hb
  let fM : ↥M →* Perm (Fin 9) := ρ.comp (Subgroup.inclusion le_normalizer)
  have hfx : fM x = b := by
    change ρ ⟨x, le_normalizer x.2⟩ = b
    rw [hρ.apply_of_mem (by norm_num) x, hxθ]
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  obtain ⟨k, ⟨a, hxa⟩, hxk⟩ :=
    exists_pow_prime_pow_eq_map (p := 2) Nat.prime_two fM x (by rw [hfx, hbo])
  have hmM : ((x ^ k : ↥M) : X) ∈ M := (x ^ k).2
  have hmρ : ρ ⟨((x ^ k : ↥M) : X), le_normalizer hmM⟩ = b := by
    change fM (x ^ k) = b
    rw [hxk, hfx]
  refine ⟨((x ^ k : ↥M) : X), hmM, ?_, ?_, hmρ⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem hxB k
  · set m : X := ((x ^ k : ↥M) : X) with hmdef
    have hm2M : m * m ∈ M := M.mul_mem hmM hmM
    have h1 : ρ ⟨m * m, le_normalizer hm2M⟩ = 1 := by
      have h2 : (⟨m * m, le_normalizer hm2M⟩ : ↥(normalizer (M : Set X))) =
          ⟨m, le_normalizer hmM⟩ * ⟨m, le_normalizer hmM⟩ := rfl
      rw [h2, map_mul, hmρ, hb2]
    have hodd := odd_orderOf_of_rho_eq_one hρ hm2M h1
    have hmo : orderOf m = 2 ^ a := by rw [hmdef, Subgroup.orderOf_coe, hxa]
    have hdvd : orderOf (m * m) ∣ 2 ^ a := by
      rw [← hmo, ← sq]
      exact orderOf_pow_dvd 2
    have hcop : Nat.Coprime (orderOf (m * m)) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

end CFSG.ComponentClassification.SolMax
