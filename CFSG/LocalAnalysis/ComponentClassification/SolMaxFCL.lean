module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_lift_involution [Finite X] {M : Subgroup X}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {B : Subgroup X}
    (hBN : B ≤ normalizer (M : Set X)) (hB2 : IsPGroup 2 B) {b : Perm (Fin 9)}
    (hbA : b ∈ alternatingGroup (Fin 9)) (hb2 : b * b = 1)
    (hb : ∀ (g : X) (hg : g ∈ B), b * ρ ⟨g, hBN hg⟩ = ρ ⟨g, hBN hg⟩ * b) :
    ∃ (x : X) (hxM : x ∈ M), x ∈ centralizer (B : Set X) ∧ x * x = 1 ∧
      ρ ⟨x, le_normalizer hxM⟩ = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₁, hxC, hxθ⟩ := hρ.exists_lift_of_isPGroup hBN hB2 (b := ⟨b, hbA⟩) hb
  have hρx₁ : ρ ⟨x₁, le_normalizer x₁.2⟩ = b := by
    rw [hρ.apply_of_mem (by norm_num) x₁, hxθ]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x₁ : X)).ne'
  set x₂ : X := (x₁ : X) ^ m with hx₂def
  have hx₂M : x₂ ∈ M := pow_mem x₁.2 m
  have hx₂C : x₂ ∈ centralizer (B : Set X) := pow_mem hxC m
  have hx₂k : x₂ ^ 2 ^ k = 1 := by
    rw [hx₂def, ← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hρx₂ : ρ ⟨x₂, le_normalizer hx₂M⟩ = b := by
    have h1 : (⟨x₂, le_normalizer hx₂M⟩ : ↥(normalizer (M : Set X))) =
        (⟨x₁, le_normalizer x₁.2⟩ : ↥(normalizer (M : Set X))) ^ m :=
      Subtype.ext (by simp [hx₂def])
    obtain ⟨j, rfl⟩ := hm
    rw [h1, map_pow, hρx₁, pow_succ, pow_mul, sq, hb2, one_pow, one_mul]
  have hsqM : x₂ * x₂ ∈ M := mul_mem hx₂M hx₂M
  have hρsq : ρ ⟨x₂ * x₂, le_normalizer hsqM⟩ = 1 := by
    have h1 : (⟨x₂ * x₂, le_normalizer hsqM⟩ : ↥(normalizer (M : Set X))) =
        ⟨x₂, le_normalizer hx₂M⟩ * ⟨x₂, le_normalizer hx₂M⟩ := Subtype.ext rfl
    rw [h1, map_mul, hρx₂, hb2]
  have hodd : Odd (orderOf (x₂ * x₂)) :=
    odd_orderOf_of_mem_oddCoreIn (mem_core_of_mem_coreActionKernel hρ (by norm_num) hsqM
      (hρ.mem_coreActionKernel _ hρsq))
  have hsq2 : (x₂ * x₂) ^ 2 ^ k = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hx₂k, one_pow]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq2)
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact ⟨x₂, hx₂M, hx₂C, hj, hρx₂⟩

@[expose] def SignalizerNineTwoPointCentralizerInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
    ∀ f ∈ normalizer (Sol78.signalizerCompletion E E : Set X), f * f = 1 → f * t = t * f →
      ∀ hfN : f ∈ normalizer (M : Set X), (ρ ⟨f, hfN⟩).support.card = 2 →
        centralizer ({f} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)

@[expose] def SignalizerNineFusionCountEightInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
    ∀ s ∈ S, s ∉ Q → ∀ g : X, g⁻¹ * t * g = s →
      g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) → s * s = 1 →
      (∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card) →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 →
      5 ≤ (ρ ⟨s, hsN⟩).support.card → ρ ⟨s, hsN⟩ ∈ alternatingGroup (Fin 9) →
      (∃ q ∈ Q, ∃ m ∈ S, m ∈ M ∧ (∀ y ∈ Q, y * m = m * y) ∧ s = q * m) → False

end CFSG.ComponentClassification.SolMax
