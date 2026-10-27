module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbDiag
public import CFSG.GH74.GLS.Stage2.OddAut.ElemAbBasis
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbGen

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

namespace Four

variable {e₁ f₁ e₂ f₂ z : Fin n → K}

theorem eq_one_of_diagOn_one {y : SUid σ n} (hy : DiagOn σ y e₁ f₁ e₂ f₂ z 1 1)
    (hspan : ∀ v : Fin n → K, ∃ ε₁ φ₁ ε₂ φ₂ c₅ : K,
      v = vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ + c₅ • z) : y = 1 := by
  apply ext_smul
  intro v
  obtain ⟨ε₁, φ₁, ε₂, φ₂, c₅, rfl⟩ := hspan v
  have h1 : y • e₁ = e₁ := by rw [hy.e1, one_smul]
  have h2 : y • f₁ = f₁ := by rw [hy.f1, inv_one, one_smul]
  have h3 : y • e₂ = e₂ := by rw [hy.e2, one_smul]
  have h4 : y • f₂ = f₂ := by rw [hy.f2, inv_one, one_smul]
  rw [one_smul]
  simp only [vec4, smul_add, smul_comm y ε₁ e₁, smul_comm y φ₁ f₁, smul_comm y ε₂ e₂,
    smul_comm y φ₂ f₂, smul_comm y c₅ z, h1, h2, h3, h4, hy.z]

theorem pow_mul_pow_pow_eq_one {r : ℕ} {α β : K} (hα : α ^ r = 1) (hβ : β ^ r = 1) (i j : ℕ) :
    (α ^ i * β ^ j) ^ r = 1 := by
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i r, mul_comm j r, pow_mul, pow_mul, hα, hβ,
    one_pow, one_pow, one_mul]

theorem pow_add_sub_eq_one {r : ℕ} {α β : K} (hα : α ^ r = 1) (hβ : β ^ r = 1) {i j i' j' : ℕ}
    (hi' : i' ≤ r) (hj' : j' ≤ r) (h : α ^ i * β ^ j = α ^ i' * β ^ j') :
    α ^ (i + (r - i')) * β ^ (j + (r - j')) = 1 := by
  calc α ^ (i + (r - i')) * β ^ (j + (r - j'))
      = (α ^ i * β ^ j) * (α ^ (r - i') * β ^ (r - j')) := by rw [pow_add, pow_add]; ring
    _ = (α ^ i' * β ^ j') * (α ^ (r - i') * β ^ (r - j')) := by rw [h]
    _ = α ^ (i' + (r - i')) * β ^ (j' + (r - j')) := by rw [pow_add, pow_add]; ring
    _ = 1 := by rw [Nat.add_sub_of_le hi', Nat.add_sub_of_le hj', hα, hβ, one_mul]

end Four

theorem exists_four_elements {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {ξ : K}
    (hξ : IsPrimitiveRoot ξ r) {e₁ f₁ e₂ f₂ z : Fin n → K} {a b : SUid σ n}
    {α₁ α₂ β₁ β₂ : K} (hDa : DiagOn σ a e₁ f₁ e₂ f₂ z α₁ α₂)
    (hDb : DiagOn σ b e₁ f₁ e₂ f₂ z β₁ β₂) (hα₁ : α₁ ^ r = 1) (hα₂ : α₂ ^ r = 1)
    (hβ₁ : β₁ ^ r = 1) (hβ₂ : β₂ ^ r = 1)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → r ∣ i ∧ r ∣ j)
    (hspan : ∀ v : Fin n → K, ∃ ε₁ φ₁ ε₂ φ₂ c₅ : K,
      v = vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ + c₅ • z) :
    ∃ xa xb x1 x1' : SUid σ n,
      (∃ i j : ℕ, xa = a ^ i * b ^ j) ∧ (∃ i j : ℕ, xb = a ^ i * b ^ j) ∧
      (∃ i j : ℕ, x1 = a ^ i * b ^ j) ∧ (∃ i j : ℕ, x1' = a ^ i * b ^ j) ∧
      DiagOn σ xa e₁ f₁ e₂ f₂ z ξ 1 ∧ DiagOn σ xb e₁ f₁ e₂ f₂ z 1 ξ ∧
      DiagOn σ x1 e₁ f₁ e₂ f₂ z ξ ξ ∧ DiagOn σ x1' e₁ f₁ e₂ f₂ z ξ ξ⁻¹ := by
  classical
  have _ := hr2
  have hr0 : 0 < r := hr.pos
  set S : Finset K := Polynomial.nthRootsFinset r (1 : K)
  have hSmem : ∀ u : K, u ∈ S ↔ u ^ r = 1 := fun u => Polynomial.mem_nthRootsFinset hr0 1
  have hScard : S.card = r := hξ.card_nthRootsFinset
  let Φ : Fin r × Fin r → S × S := fun ij =>
    (⟨α₁ ^ (ij.1 : ℕ) * β₁ ^ (ij.2 : ℕ),
        (hSmem _).2 (Four.pow_mul_pow_pow_eq_one hα₁ hβ₁ _ _)⟩,
      ⟨α₂ ^ (ij.1 : ℕ) * β₂ ^ (ij.2 : ℕ),
        (hSmem _).2 (Four.pow_mul_pow_pow_eq_one hα₂ hβ₂ _ _)⟩)
  have hΦinj : Function.Injective Φ := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : α₁ ^ (i : ℕ) * β₁ ^ (j : ℕ) = α₁ ^ (i' : ℕ) * β₁ ^ (j' : ℕ) :=
      congrArg (fun t : S × S => (t.1 : K)) h
    have h2 : α₂ ^ (i : ℕ) * β₂ ^ (j : ℕ) = α₂ ^ (i' : ℕ) * β₂ ^ (j' : ℕ) :=
      congrArg (fun t : S × S => (t.2 : K)) h
    have hy : DiagOn σ (a ^ ((i : ℕ) + (r - i')) * b ^ ((j : ℕ) + (r - j'))) e₁ f₁ e₂ f₂ z 1 1 := by
      have := (hDa.pow ((i : ℕ) + (r - i'))).mul (hDb.pow ((j : ℕ) + (r - j')))
      rwa [Four.pow_add_sub_eq_one hα₁ hβ₁ i'.isLt.le j'.isLt.le h1,
        Four.pow_add_sub_eq_one hα₂ hβ₂ i'.isLt.le j'.isLt.le h2] at this
    obtain ⟨d1, d2⟩ := hind _ _ (Four.eq_one_of_diagOn_one hy hspan)
    exact Prod.ext (Fin.ext (CFSG.GH74.GLS.Stage2.OddAut.eq_of_dvd_add_sub' i.isLt i'.isLt d1))
      (Fin.ext (CFSG.GH74.GLS.Stage2.OddAut.eq_of_dvd_add_sub' j.isLt j'.isLt d2))
  have hΦbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hΦinj, ?_⟩
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hScard]
  have key : ∀ u v : K, u ^ r = 1 → v ^ r = 1 → ∃ i j : ℕ,
      α₁ ^ i * β₁ ^ j = u ∧ α₂ ^ i * β₂ ^ j = v := by
    intro u v hu hv
    obtain ⟨⟨i, j⟩, hij⟩ := hΦbij.2 (⟨u, (hSmem u).2 hu⟩, ⟨v, (hSmem v).2 hv⟩)
    exact ⟨i, j, congrArg (fun t : S × S => (t.1 : K)) hij,
      congrArg (fun t : S × S => (t.2 : K)) hij⟩
  have hmk : ∀ (i j : ℕ) (u v : K), α₁ ^ i * β₁ ^ j = u → α₂ ^ i * β₂ ^ j = v →
      DiagOn σ (a ^ i * b ^ j) e₁ f₁ e₂ f₂ z u v := by
    intro i j u v hu hv
    have := (hDa.pow i).mul (hDb.pow j)
    rwa [hu, hv] at this
  have hξr : ξ ^ r = 1 := hξ.pow_eq_one
  have hξir : ξ⁻¹ ^ r = 1 := by rw [inv_pow, hξr, inv_one]
  obtain ⟨i₁, j₁, h₁, h₁'⟩ := key ξ 1 hξr (one_pow r)
  obtain ⟨i₂, j₂, h₂, h₂'⟩ := key 1 ξ (one_pow r) hξr
  obtain ⟨i₃, j₃, h₃, h₃'⟩ := key ξ ξ hξr hξr
  obtain ⟨i₄, j₄, h₄, h₄'⟩ := key ξ ξ⁻¹ hξr hξir
  exact ⟨a ^ i₁ * b ^ j₁, a ^ i₂ * b ^ j₂, a ^ i₃ * b ^ j₃, a ^ i₄ * b ^ j₄,
    ⟨i₁, j₁, rfl⟩, ⟨i₂, j₂, rfl⟩, ⟨i₃, j₃, rfl⟩, ⟨i₄, j₄, rfl⟩,
    hmk _ _ _ _ h₁ h₁', hmk _ _ _ _ h₂ h₂', hmk _ _ _ _ h₃ h₃', hmk _ _ _ _ h₄ h₄'⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub
