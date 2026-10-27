module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUEntry

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {k : Subfield K}

theorem norm_expand (hσ : ∀ c, σ (σ c) = c) {l : K} (hl : σ l * l = -1) (x y : K) :
    σ (x + σ l * y) * (x + σ l * y) =
      σ x * x - σ y * y + l * (x * σ y) + σ l * (σ x * y) := by
  simp only [map_add, map_mul, hσ]
  linear_combination (σ y * y) * hl

theorem exists_circle_not_mem (hσ : ∀ c, σ (σ c) = c) (hk : ∀ x ∈ k, σ x ∈ k)
    {l₁ l₂ l₃ : K} (m₁ : l₁ ∈ k) (m₂ : l₂ ∈ k) (m₃ : l₃ ∈ k) (d₁₂ : l₁ ≠ l₂) (d₁₃ : l₁ ≠ l₃)
    (d₂₃ : l₂ ≠ l₃) (n₁ : σ l₁ * l₁ = -1) (n₂ : σ l₂ * l₂ = -1) (n₃ : σ l₃ * l₃ = -1)
    {x y c : K} (hc : c ∈ k) (hcw : c * x * σ y ∉ k) :
    ∃ l ∈ ({l₁, l₂, l₃} : Set K), σ (x + σ l * y) * (x + σ l * y) ∉ k := by
  by_contra hall
  push Not at hall
  have g₁ := hall l₁ (by simp)
  have g₂ := hall l₂ (by simp)
  have g₃ := hall l₃ (by simp)
  rw [norm_expand hσ n₁] at g₁
  rw [norm_expand hσ n₂] at g₂
  rw [norm_expand hσ n₃] at g₃
  have hl₁ : l₁ ≠ 0 := by rintro rfl; simp at n₁
  have hl₂ : l₂ ≠ 0 := by rintro rfl; simp at n₂
  have hl₃ : l₃ ≠ 0 := by rintro rfl; simp at n₃
  set w : K := x * σ y with hw
  have hσw : σ w = σ x * y := by rw [hw, map_mul, hσ]
  rw [← hσw] at g₁ g₂ g₃
  set D₁ : K := l₁ - l₃ with hD₁
  set D₂ : K := l₂ - l₃ with hD₂
  have hΔ : (D₁ * σ D₂ - D₂ * σ D₁) * (l₁ * l₂ * l₃) = D₁ * D₂ * (l₁ - l₂) := by
    simp only [hD₁, hD₂, map_sub]
    linear_combination (l₁ - l₃) * l₁ * (l₃ * n₂ - l₂ * n₃) - (l₂ - l₃) * l₂ * (l₃ * n₁ - l₁ * n₃)
  have hΔ0 : D₁ * σ D₂ - D₂ * σ D₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hΔ
    have : D₁ * D₂ * (l₁ - l₂) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.2 d₁₃) (sub_ne_zero.2 d₂₃)) (sub_ne_zero.2 d₁₂)
    exact this hΔ.symm
  have hsolve : (D₁ * σ D₂ - D₂ * σ D₁) * w =
      ((σ x * x - σ y * y + l₁ * w + σ l₁ * σ w) - (σ x * x - σ y * y + l₃ * w + σ l₃ * σ w)) *
        σ D₂ - ((σ x * x - σ y * y + l₂ * w + σ l₂ * σ w) -
          (σ x * x - σ y * y + l₃ * w + σ l₃ * σ w)) * σ D₁ := by
    simp only [hD₁, hD₂, map_sub]
    ring
  have hwk : w ∈ k := by
    have hD₁k : D₁ ∈ k := k.sub_mem m₁ m₃
    have hD₂k : D₂ ∈ k := k.sub_mem m₂ m₃
    have hσD₁k : σ D₁ ∈ k := hk _ hD₁k
    have hσD₂k : σ D₂ ∈ k := hk _ hD₂k
    have hΔk : D₁ * σ D₂ - D₂ * σ D₁ ∈ k :=
      k.sub_mem (k.mul_mem hD₁k hσD₂k) (k.mul_mem hD₂k hσD₁k)
    have hRk : ((σ x * x - σ y * y + l₁ * w + σ l₁ * σ w) -
        (σ x * x - σ y * y + l₃ * w + σ l₃ * σ w)) * σ D₂ - ((σ x * x - σ y * y + l₂ * w +
          σ l₂ * σ w) - (σ x * x - σ y * y + l₃ * w + σ l₃ * σ w)) * σ D₁ ∈ k := by
      refine k.sub_mem (k.mul_mem (k.sub_mem g₁ g₃) hσD₂k) (k.mul_mem (k.sub_mem g₂ g₃) hσD₁k)
    have := k.div_mem hRk hΔk
    rwa [← hsolve, mul_div_cancel_left₀ _ hΔ0] at this
  exact hcw (by rw [mul_assoc]; exact k.mul_mem hc hwk)

@[expose] def planeVec (r s : Fin n) (l : K) : Fin n → K :=
  Pi.single r 1 + l • Pi.single s 1

theorem herm_planeVec_left (r s : Fin n) (l : K) (b : Fin n → K) :
    herm σ (planeVec r s l) b = b r + σ l * b s := by
  simp [planeVec, herm_single_left]

theorem herm_planeVec_self {r s : Fin n} (hrs : r ≠ s) (l : K) (hl : σ l * l = -1) :
    herm σ (planeVec r s l) (planeVec r s l) = 0 := by
  rw [herm_planeVec_left]
  simp [planeVec, hrs.symm, hl]

theorem isRat_planeVec (r s : Fin n) {l : K} (hl : l ∈ k) : IsRat k (planeVec r s l) := by
  intro i
  simp only [planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  refine k.add_mem ?_ (k.mul_mem hl ?_) <;> split_ifs <;> simp [k.one_mem, k.zero_mem]

theorem exists_rat_iso_not_mem (hσ : ∀ c, σ (σ c) = c) (hk : ∀ x ∈ k, σ x ∈ k)
    (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = σ (x : K))
    (h3 : ∃ l₁ l₂ l₃ : k, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧ σk l₁ * l₁ = -1 ∧ σk l₂ * l₂ = -1 ∧
      σk l₃ * l₃ = -1)
    {b : Fin n → K} {r s : Fin n} (hrs : r ≠ s) {c : K} (hc : c ∈ k)
    (hcw : c * b r * σ (b s) ∉ k) :
    ∃ e : Fin n → K, IsRat k e ∧ herm σ e e = 0 ∧ σ (herm σ e b) * herm σ e b ∉ k := by
  obtain ⟨l₁, l₂, l₃, d₁₂, d₁₃, d₂₃, n₁, n₂, n₃⟩ := h3
  have key : ∀ l : k, σk l * l = -1 → σ (l : K) * (l : K) = -1 := by
    intro l hl
    have := congrArg (fun z : k => (z : K)) hl
    simpa [hσk] using this
  obtain ⟨l, hl, hlk⟩ := exists_circle_not_mem hσ hk (l₁ := (l₁ : K)) (l₂ := (l₂ : K))
    (l₃ := (l₃ : K)) l₁.2 l₂.2 l₃.2 (fun h => d₁₂ (Subtype.ext h)) (fun h => d₁₃ (Subtype.ext h))
    (fun h => d₂₃ (Subtype.ext h)) (key _ n₁) (key _ n₂) (key _ n₃) (x := b r) (y := b s) hc hcw
  have hlm : l ∈ k ∧ σ l * l = -1 := by
    rcases hl with rfl | rfl | rfl
    · exact ⟨l₁.2, key _ n₁⟩
    · exact ⟨l₂.2, key _ n₂⟩
    · exact ⟨l₃.2, key _ n₃⟩
  refine ⟨planeVec r s l, isRat_planeVec r s hlm.1, herm_planeVec_self hrs l hlm.2, ?_⟩
  rwa [herm_planeVec_left]

section Concrete

open CFSG.LieType.BorelTits

theorem exists_three_norm_neg_one {F : Type} [Field F] [Finite F] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP F ℓ] (hF : Nat.card F = (ℓ ^ f) ^ 2) :
    ∃ l₁ l₂ l₃ : F, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧ unitaryInvolution F ℓ f l₁ * l₁ = -1 ∧
      unitaryInvolution F ℓ f l₂ * l₂ = -1 ∧ unitaryInvolution F ℓ f l₃ * l₃ = -1 := by
  have hq : 1 < ℓ ^ f := one_lt_pow_of_card hF
  obtain ⟨u, hu⟩ := (isUnitaryInvolution_unitaryInvolution hF).exists_norm_neg_one
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (ℓ ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hF]
  set q : ℕ := ℓ ^ f with hqdef
  obtain ⟨m, hm⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have hq1 : q ^ 2 - 1 = (q + 1) * (q - 1) := sq_sub_one_eq q hq.le
  have hq2 : q - 1 = m + 1 := by omega
  set ω : Fˣ := g ^ (q - 1) with hω
  have hωn : unitaryInvolution F ℓ f (ω : F) * (ω : F) = 1 := by
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ,
      hω, ← pow_mul, mul_comm, ← hq1, ← hord, pow_orderOf_eq_one, Units.val_one]
  have hω1 : ω ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by omega) ?_
    rw [hord, hq1, hq2, hm]
    nlinarith
  have hω2 : ω ^ 2 ≠ 1 := by
    have : ω ^ 2 = g ^ (2 * (q - 1)) := by rw [hω, ← pow_mul, mul_comm]
    rw [this]
    refine pow_ne_one_of_lt_orderOf (by omega) ?_
    rw [hord, hq1, hq2, hm]
    nlinarith
  have hωn2 : unitaryInvolution F ℓ f ((ω ^ 2 : Fˣ) : F) * ((ω ^ 2 : Fˣ) : F) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hωn, one_pow]
  have hω0 : (ω : F) ≠ 0 := ω.ne_zero
  refine ⟨u, u * ω, u * (ω ^ 2 : Fˣ), ?_, ?_, ?_, hu, ?_, ?_⟩
  · intro h
    apply hω1
    have : (ω : F) = 1 := by
      have h2 := mul_left_cancel₀ hu0 (by rw [mul_one]; exact h.symm : u * (ω : F) = u * 1)
      exact h2
    exact Units.ext this
  · intro h
    apply hω2
    have : ((ω ^ 2 : Fˣ) : F) = 1 := mul_left_cancel₀ hu0 (by rw [mul_one]; exact h.symm)
    exact Units.ext this
  · intro h
    apply hω1
    have h2 : (ω : F) = ((ω ^ 2 : Fˣ) : F) := mul_left_cancel₀ hu0 h
    rw [Units.val_pow_eq_pow_val, sq] at h2
    have : (ω : F) = 1 := by
      exact mul_left_cancel₀ hω0
        (by rw [mul_one]; exact h2.symm : (ω : F) * (ω : F) = (ω : F) * 1)
    exact Units.ext this
  · rw [map_mul]
    calc unitaryInvolution F ℓ f u * unitaryInvolution F ℓ f (ω : F) * (u * (ω : F))
        = (unitaryInvolution F ℓ f u * u) * (unitaryInvolution F ℓ f (ω : F) * (ω : F)) := by ring
      _ = -1 := by rw [hu, hωn, mul_one]
  · rw [map_mul]
    calc unitaryInvolution F ℓ f u * unitaryInvolution F ℓ f ((ω ^ 2 : Fˣ) : F) *
        (u * ((ω ^ 2 : Fˣ) : F))
        = (unitaryInvolution F ℓ f u * u) *
          (unitaryInvolution F ℓ f ((ω ^ 2 : Fˣ) : F) * ((ω ^ 2 : Fˣ) : F)) := by ring
      _ = -1 := by rw [hu, hωn2, mul_one]

end Concrete

section Pair

variable [Finite K] {p : ℕ}

theorem exists_pair_su (hσ : ∀ c, σ (σ c) = c) (hk : ∀ x ∈ k, σ x ∈ k)
    (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = σ (x : K)) (hU : IsUnitaryInvolution σk)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : k, s ≠ 0 ∧ σk s * s ≠ 1)
    (h3' : ∃ l₁ l₂ l₃ : k, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧ σk l₁ * l₁ = -1 ∧ σk l₂ * l₂ = -1 ∧
      σk l₃ * l₃ = -1)
    (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    (hne : (ratSU σ k hk n).map (suConj hσ A hA) ≠ ratSU σ k hk n) :
    ∃ a e : Fin n → K, IsRat k a ∧ herm σ a a = 0 ∧ IsRat k e ∧ herm σ e e = 0 ∧
      σ (herm σ e ((A : Matrix (Fin n) (Fin n) K) *ᵥ a)) *
        herm σ e ((A : Matrix (Fin n) (Fin n) K) *ᵥ a) ∉ k := by
  obtain ⟨a, c, ha, hia, hc, -, r, s, hrs, hirr⟩ :=
    exists_offDiag_not_mem_su hσ hk σk hσk hU hp hp2 hK hn h3 A hA hne
  obtain ⟨e, he, hie, hN⟩ := exists_rat_iso_not_mem hσ hk σk hσk h3' hrs hc hirr
  exact ⟨a, e, ha, hia, he, hie, hN⟩

end Pair

end CFSG.LieType.SeitzGeneration.SUPair
