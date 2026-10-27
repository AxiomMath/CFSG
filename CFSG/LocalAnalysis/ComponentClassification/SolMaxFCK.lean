module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCJ

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_split_conj [Finite X] {E M Q Sc : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc)
    (hScard : Nat.card Sc =
      2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2)
    {x : X} (hxS : x ∈ Sc) (hx2 : x * x = 1)
    (hxA : ρ ⟨x, hHN (hSH hxS)⟩ ∈ alternatingGroup (Fin 9)) :
    ∃ h ∈ normalizer (Sol78.signalizerCompletion E E : Set X), h * x * h⁻¹ ∈ Sc ∧
      ∃ q ∈ Q, ∃ m ∈ Sc, m ∈ M ∧ (∀ y ∈ Q, y * m = m * y) ∧ h * x * h⁻¹ = q * m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hxN : x ∈ normalizer (M : Set X) := hHN (hSH hxS)
  have hKQ := inf_kernel_eq_of_sylow hQK hQcard hQS hS2
  have hxNQ : x ∈ normalizer (Q : Set X) :=
    le_normalizer_of_sylow_kernel hHN hQK hQcard hQS hSH hS2 hxS
  set B₀ := Q ⊔ zpowers x with hB₀def
  have hB₀2 : IsPGroup 2 B₀ :=
    hQ2.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self hx2) (zpowers_le.mpr hxNQ)
  have hB₀H : B₀ ≤ H := sup_le (hQK.trans inf_le_left) (zpowers_le.mpr (hSH hxS))
  have hB₀N : B₀ ≤ normalizer (M : Set X) := hB₀H.trans hHN
  have hb : ∀ (y : X) (hy : y ∈ B₀),
      ρ ⟨x, hxN⟩ * ρ ⟨y, hB₀N hy⟩ = ρ ⟨y, hB₀N hy⟩ * ρ ⟨x, hxN⟩ := by
    set Z : Subgroup X := ((centralizer ({ρ ⟨x, hxN⟩} : Set (Perm (Fin 9)))).comap ρ).map
      (normalizer (M : Set X)).subtype with hZdef
    have hQZ : Q ≤ Z := fun q hq => by
      refine ⟨⟨q, hHN (hQK hq).1⟩, ?_, rfl⟩
      have h1 : ρ ⟨q, hHN (hQK hq).1⟩ = 1 :=
        hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK hq).2
      show ρ ⟨q, hHN (hQK hq).1⟩ ∈ centralizer ({ρ ⟨x, hxN⟩} : Set (Perm (Fin 9)))
      rw [h1]
      exact one_mem _
    have hxZ : x ∈ Z := ⟨⟨x, hxN⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr rfl), rfl⟩
    intro y hy
    obtain ⟨y', hy', hyy⟩ := sup_le hQZ (zpowers_le.mpr hxZ) hy
    have h1 : (⟨y, hB₀N hy⟩ : ↥(normalizer (M : Set X))) = y' := Subtype.ext hyy.symm
    rw [h1]
    exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hy')).symm
  obtain ⟨x₁, hxC, hxθ⟩ := hρ.exists_lift_of_isPGroup hB₀N hB₀2 (b := ⟨ρ ⟨x, hxN⟩, hxA⟩) hb
  have hρx₁ : ρ ⟨x₁, le_normalizer x₁.2⟩ = ρ ⟨x, hxN⟩ := by
    rw [hρ.apply_of_mem (by norm_num) x₁, hxθ]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x₁ : X)).ne'
  set x₂ : X := (x₁ : X) ^ m with hx₂def
  have hx₂M : x₂ ∈ M := pow_mem x₁.2 m
  have hx₂C : x₂ ∈ centralizer (B₀ : Set X) := pow_mem hxC m
  have hx₂2 : IsPGroup 2 (zpowers x₂) := by
    have h1 : x₂ ^ 2 ^ k = 1 := by
      rw [hx₂def, ← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hρx₂ : ρ ⟨x₂, le_normalizer hx₂M⟩ = ρ ⟨x, hxN⟩ := by
    have h1 : (⟨x₂, le_normalizer hx₂M⟩ : ↥(normalizer (M : Set X))) =
        (⟨x₁, le_normalizer x₁.2⟩ : ↥(normalizer (M : Set X))) ^ m :=
      Subtype.ext (by simp [hx₂def])
    have hρx2 : ρ ⟨x, hxN⟩ * ρ ⟨x, hxN⟩ = 1 := by
      rw [← map_mul]
      have h2 : (⟨x, hxN⟩ : ↥(normalizer (M : Set X))) * ⟨x, hxN⟩ = 1 := Subtype.ext hx2
      rw [h2, map_one]
    obtain ⟨j, rfl⟩ := hm
    rw [h1, map_pow, hρx₁, pow_succ, pow_mul, sq, hρx2, one_pow, one_mul]
  set B₁ := B₀ ⊔ zpowers x₂ with hB₁def
  have hB₁2 : IsPGroup 2 B₁ := hB₀2.to_sup_of_normal_left' hx₂2
    (zpowers_le.mpr (Subgroup.centralizer_le_normalizer (B₀ : Set X) hx₂C))
  have hB₁H : B₁ ≤ H := sup_le hB₀H (zpowers_le.mpr (hMH hx₂M))
  obtain ⟨h, hhH, hh⟩ := exists_conj_le_of_card_eq_of_le hSH hScard hB₁H hB₁2
  have hhN : h ∈ normalizer (M : Set X) := hHN hhH
  have hQB₁ : Q ≤ B₁ := le_sup_left.trans le_sup_left
  have hhQ : ∀ y ∈ Q, h * y * h⁻¹ ∈ Q := fun y hy => by
    have h1 : h * y * h⁻¹ ∈ Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      mem_inf.mpr ⟨hh y (hQB₁ hy), mem_inf.mpr ⟨mul_mem (mul_mem hhH (hQK hy).1) (inv_mem hhH),
        UnbalancedLayer.conj_mem_coreActionKernel hhN (hQK hy).2⟩⟩
    rwa [hKQ] at h1
  have hQmap : Q.map (MulAut.conj h).toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj h).injective).ge
    rintro _ ⟨y, hy, rfl⟩
    exact hhQ y hy
  have hhQ' : ∀ y ∈ Q, h⁻¹ * y * h ∈ Q := fun y hy => by
    rw [← hQmap] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa [MulAut.conj_apply, mul_assoc] using hz
  set mm := h * x₂ * h⁻¹ with hmmdef
  have hx''S : h * x * h⁻¹ ∈ Sc := hh x (mem_sup_left (mem_sup_right (mem_zpowers x)))
  have hmmS : mm ∈ Sc := hh x₂ (mem_sup_right (mem_zpowers x₂))
  have hmmM : mm ∈ M := (mem_normalizer_iff.mp hhN x₂).mp hx₂M
  have hmmC : ∀ y ∈ Q, y * mm = mm * y := fun y hy => by
    have h1 := mem_centralizer_iff.mp hx₂C (h⁻¹ * y * h) (mem_sup_left (hhQ' y hy))
    rw [hmmdef]
    calc y * (h * x₂ * h⁻¹) = h * ((h⁻¹ * y * h) * x₂) * h⁻¹ := by group
      _ = h * (x₂ * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
      _ = h * x₂ * h⁻¹ * y := by group
  have hx''N : h * x * h⁻¹ ∈ normalizer (M : Set X) := hHN (hSH hx''S)
  have hmmN : mm ∈ normalizer (M : Set X) := le_normalizer hmmM
  have hρx'' : ρ ⟨h * x * h⁻¹, hx''N⟩ = ρ ⟨h, hhN⟩ * ρ ⟨x, hxN⟩ * (ρ ⟨h, hhN⟩)⁻¹ :=
    apply_conj_of_mem_normalizer ρ hhN hxN hx''N
  have hρmm : ρ ⟨mm, hmmN⟩ = ρ ⟨h, hhN⟩ * ρ ⟨x, hxN⟩ * (ρ ⟨h, hhN⟩)⁻¹ := by
    rw [apply_conj_of_mem_normalizer ρ hhN (le_normalizer hx₂M) hmmN, hρx₂]
  set q := h * x * h⁻¹ * mm⁻¹ with hqdef
  have hqQ : q ∈ Q := by
    have hqS : q ∈ Sc := mul_mem hx''S (inv_mem hmmS)
    have hqN : q ∈ normalizer (M : Set X) := mul_mem hx''N (inv_mem hmmN)
    have hρq : ρ ⟨q, hqN⟩ = 1 := by
      have h1 : (⟨q, hqN⟩ : ↥(normalizer (M : Set X))) = ⟨h * x * h⁻¹, hx''N⟩ * (⟨mm, hmmN⟩)⁻¹ :=
        Subtype.ext rfl
      rw [h1, map_mul, map_inv, hρx'', hρmm, mul_inv_cancel]
    have h1 : q ∈ Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      mem_inf.mpr ⟨hqS, mem_inf.mpr ⟨hSH hqS, hρ.mem_coreActionKernel hqN hρq⟩⟩
    rwa [hKQ] at h1
  exact ⟨h, hhH, hx''S, q, hqQ, mm, hmmS, hmmM, hmmC, by rw [hqdef]; group⟩

end CFSG.ComponentClassification.SolMax
