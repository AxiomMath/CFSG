module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedDisjoint
public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedEven

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFiveFixed

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier
  CFSG.Wreathed.ConditionalUniformOddFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem sum_mul_four_unitVector {q₁ q₂ q₃ q₄ : ι} (h₁ : q₁ ∈ B) (h₂ : q₂ ∈ B) (h₃ : q₃ ∈ B)
    (h₄ : q₄ ∈ B) (f : ι → ℤ) (a₁ a₂ a₃ a₄ : ℤ) :
    ∑ φ ∈ B, f φ * (a₁ * unitVector q₁ φ + a₂ * unitVector q₂ φ + a₃ * unitVector q₃ φ +
      a₄ * unitVector q₄ φ) = a₁ * f q₁ + a₂ * f q₂ + a₃ * f q₃ + a₄ * f q₄ := by
  have h : ∀ φ, f φ * (a₁ * unitVector q₁ φ + a₂ * unitVector q₂ φ + a₃ * unitVector q₃ φ +
      a₄ * unitVector q₄ φ) = a₁ * (f φ * unitVector q₁ φ) + a₂ * (f φ * unitVector q₂ φ) +
      a₃ * (f φ * unitVector q₃ φ) + a₄ * (f φ * unitVector q₄ φ) := fun φ => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_mul_unitVector h₁,
    sum_mul_unitVector h₂, sum_mul_unitVector h₃, sum_mul_unitVector h₄]

theorem sum_mul_lincomb {κ₁ : Type*} [Fintype κ₁] {g : κ₁ → ι} (hg : ∀ l, g l ∈ B)
    (f : ι → ℤ) (a : κ₁ → ℤ) :
    ∑ φ ∈ B, f φ * ∑ l, a l * unitVector (g l) φ = ∑ l, a l * f (g l) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : ∀ φ, f φ * (a l * unitVector (g l) φ) = a l * (f φ * unitVector (g l) φ) :=
    fun φ => by ring
  rw [Finset.sum_congr rfl fun φ _ => h φ, ← Finset.mul_sum, sum_mul_unitVector (hg l)]

@[expose] def fixedPart (p A Bq Dq : ι) (σ τ₀ κ : ℤ) : ι → ℤ := fun φ =>
  -unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ + κ * unitVector Dq φ

theorem sum_mul_fixedPart {A Bq Dq : ι} (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B)
    (σ τ₀ κ : ℤ) (f : ι → ℤ) :
    ∑ φ ∈ B, f φ * fixedPart p A Bq Dq σ τ₀ κ φ = -f p - σ * f A - τ₀ * f Bq + κ * f Dq := by
  calc ∑ φ ∈ B, f φ * fixedPart p A Bq Dq σ τ₀ κ φ = ∑ φ ∈ B, f φ * ((-1) * unitVector p φ +
      (-σ) * unitVector A φ + (-τ₀) * unitVector Bq φ + κ * unitVector Dq φ) :=
        Finset.sum_congr rfl fun φ _ => by rw [fixedPart]; ring
    _ = _ := by rw [sum_mul_four_unitVector hp hA hBq hDq]; ring

theorem fixedPart_of_ne {A Bq Dq φ : ι} (σ τ₀ κ : ℤ) (hp : φ ≠ p) (hA : φ ≠ A) (hB : φ ≠ Bq)
    (hD : φ ≠ Dq) : fixedPart p A Bq Dq σ τ₀ κ φ = 0 := by
  rw [fixedPart, unitVector_of_ne hp, unitVector_of_ne hA, unitVector_of_ne hB,
    unitVector_of_ne hD]
  ring

theorem even_quadruple {A Bq Dq ω : ι} {σ τ₀ κ δ : ℤ} {y₀ C yr xk d : ι → ℤ}
    (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) (hω : ω ∈ B)
    (hAp : A ≠ p) (hBp : Bq ≠ p) (hDp : Dq ≠ p) (hωp : ω ≠ p) (hBA : Bq ≠ A) (hDA : Dq ≠ A)
    (hωA : ω ≠ A) (hDB : Dq ≠ Bq) (hωB : ω ≠ Bq) (hωD : ω ≠ Dq)
    (hσ : σ = 1 ∨ σ = -1) (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1)
    (hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + σ * unitVector A φ - τ₀ * unitVector Bq φ +
      κ * unitVector Dq φ)
    (hC : ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ -
      κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ)
    (hyv : ∀ φ ∈ B, yr φ = 0 ∨ yr φ = 1 ∨ yr φ = -1)
    (hy4 : (B.filter fun φ => yr φ ≠ 0).card = 4) (hyp : yr p = 0) (hyA : yr A = 0)
    (hyy₀ : ∑ φ ∈ B, yr φ * y₀ φ = 0) (hyC : ∑ φ ∈ B, yr φ * C φ = 0)
    (hyx : ∑ φ ∈ B, yr φ * xk φ = 0) (hxp : xk p = -1) (hxA : xk A = -σ)
    (hxsq : ∑ φ ∈ B, xk φ * xk φ = 8) (hxy₀ : ∑ φ ∈ B, xk φ * y₀ φ = 0)
    (hxC : ∑ φ ∈ B, xk φ * C φ = 0) (hpar : ∀ φ ∈ B, xk φ ≡ y₀ φ + yr φ [ZMOD 2])
    (hdx : ∑ φ ∈ B, d φ * xk φ = 0) (hdy : ∑ φ ∈ B, d φ * yr φ = 0)
    (hP1 : -d p - σ * d A - τ₀ * d Bq + κ * d Dq = -(2 * σ * δ)) :
    yr Bq = 0 ∧ yr Dq = 0 ∧ yr ω = 0 ∧ xk Bq = -τ₀ ∧ xk Dq = κ ∧ xk ω = 0 ∧
      ∃ (γ : Fin 4 → ι) (ε : Fin 4 → ℤ), Function.Injective γ ∧ (∀ l, γ l ∈ B) ∧
        (∀ l, ε l = 1 ∨ ε l = -1) ∧ (∀ φ ∈ B, yr φ ≠ 0 ↔ ∃ l, φ = γ l) ∧
        (∀ φ ∈ B, yr φ = ∑ l, (quadSign l * ε l) * unitVector (γ l) φ) ∧
        (∀ φ ∈ B, xk φ = fixedPart p A Bq Dq σ τ₀ κ φ + ∑ l, ε l * unitVector (γ l) φ) ∧
        (∀ l, γ l ≠ p ∧ γ l ≠ A ∧ γ l ≠ Bq ∧ γ l ≠ Dq ∧ γ l ≠ ω) ∧
        ε 0 * d (γ 0) + ε 1 * d (γ 1) = σ * δ ∧ ε 2 * d (γ 2) + ε 3 * d (γ 3) = σ * δ := by
  obtain ⟨hyB, hyD, hyω, hxB, hxD, hxω, hxs, hx0⟩ := even_column hp hA hBq hDq hω hAp hBp hDp
    hωp hBA hDA hωA hDB hωB hωD hσ hτ₀ hκ hy₀ hC hyv hy4 hyp hyA hyy₀ hyC hyx hxp hxA hxsq hxy₀
    hxC hpar
  obtain ⟨γ, hγinj, hγB, hsupp, hγs, hγy⟩ := exists_quadruple_labels hyv hy4 hxs hyx
  refine ⟨hyB, hyD, hyω, hxB, hxD, hxω, γ, fun l => xk (γ l), hγinj, hγB, hγs, hsupp, ?_⟩
  have hγy0 : ∀ l, yr (γ l) ≠ 0 := fun l => (hsupp _ (hγB l)).mpr ⟨l, rfl⟩
  have hγcore : ∀ l, γ l ≠ p ∧ γ l ≠ A ∧ γ l ≠ Bq ∧ γ l ≠ Dq ∧ γ l ≠ ω := by
    intro l
    refine ⟨fun h => hγy0 l (by rw [h, hyp]), fun h => hγy0 l (by rw [h, hyA]),
      fun h => hγy0 l (by rw [h, hyB]), fun h => hγy0 l (by rw [h, hyD]),
      fun h => hγy0 l (by rw [h, hyω])⟩
  have hyrep : ∀ φ ∈ B, yr φ = ∑ l, (quadSign l * xk (γ l)) * unitVector (γ l) φ := by
    intro φ hφ
    by_cases hφy : yr φ = 0
    · rw [hφy]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      rw [unitVector_of_ne fun h => hγy0 l (by rw [← h]; exact hφy), mul_zero]
    · obtain ⟨l, rfl⟩ := (hsupp φ hφ).mp hφy
      rw [Finset.sum_eq_single l (fun l' _ hl' => by
          rw [unitVector_of_ne fun h => hl' (hγinj h).symm, mul_zero])
        fun h => absurd (Finset.mem_univ l) h, unitVector_self, mul_one, hγy l]
  have hxrep : ∀ φ ∈ B, xk φ = fixedPart p A Bq Dq σ τ₀ κ φ +
      ∑ l, xk (γ l) * unitVector (γ l) φ := by
    intro φ hφ
    by_cases hφγ : ∃ l, φ = γ l
    · obtain ⟨l, rfl⟩ := hφγ
      obtain ⟨h1, h2, h3, h4, -⟩ := hγcore l
      rw [fixedPart_of_ne σ τ₀ κ h1 h2 h3 h4, zero_add,
        Finset.sum_eq_single l (fun l' _ hl' => by
          rw [unitVector_of_ne fun h => hl' (hγinj h).symm, mul_zero])
        fun h => absurd (Finset.mem_univ l) h, unitVector_self, mul_one]
    · push Not at hφγ
      have hsum0 : ∑ l, xk (γ l) * unitVector (γ l) φ = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [unitVector_of_ne (hφγ l), mul_zero]
      rw [hsum0, add_zero]
      have hyφ : yr φ = 0 := by
        by_contra hne
        obtain ⟨l, hl⟩ := (hsupp φ hφ).mp hne
        exact hφγ l hl
      by_cases hφp : φ = p
      · subst hφp
        simp [fixedPart, unitVector, hxp, hAp.symm, hBp.symm, hDp.symm]
      by_cases hφA : φ = A
      · subst hφA
        simp [fixedPart, unitVector, hxA, hAp, hBA.symm, hDA.symm]
      by_cases hφB : φ = Bq
      · subst hφB
        simp [fixedPart, unitVector, hxB, hBp, hBA, hDB.symm]
      by_cases hφD : φ = Dq
      · subst hφD
        simp [fixedPart, unitVector, hxD, hDp, hDA, hDB]
      rw [fixedPart_of_ne σ τ₀ κ hφp hφA hφB hφD, hx0 φ hφ hφp hφA hφB hφD hyφ]
  refine ⟨hyrep, hxrep, hγcore, ?_⟩
  have e1 := hdx
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hxrep φ hφ]] at e1
  simp only [mul_add, Finset.sum_add_distrib] at e1
  rw [sum_mul_fixedPart hp hA hBq hDq, sum_mul_lincomb hγB, Fin.sum_univ_four] at e1
  have e2 := hdy
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hyrep φ hφ], sum_mul_lincomb hγB,
    Fin.sum_univ_four, quadSign_zero, quadSign_one, quadSign_two, quadSign_three] at e2
  beta_reduce
  constructor <;> linarith only [e1, e2, hP1]


theorem fixedPart_core {A Bq Dq : ι} (σ τ₀ κ : ℤ) (hAp : A ≠ p) (hBp : Bq ≠ p) (hDp : Dq ≠ p)
    (hBA : Bq ≠ A) (hDA : Dq ≠ A) (hDB : Dq ≠ Bq) :
    fixedPart p A Bq Dq σ τ₀ κ p = -1 ∧ fixedPart p A Bq Dq σ τ₀ κ A = -σ ∧
      fixedPart p A Bq Dq σ τ₀ κ Bq = -τ₀ ∧ fixedPart p A Bq Dq σ τ₀ κ Dq = κ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [fixedPart, unitVector, hAp, hBp, hDp, hBA, hDA, hDB, hAp.symm, hBp.symm, hDp.symm,
      hBA.symm, hDA.symm, hDB.symm]

theorem even_quadruples_disjoint {A Bq Dq : ι} {σ τ₀ κ V : ℤ} {xr xt yr yt d : ι → ℤ}
    {γr γt : Fin 4 → ι} {εr εt : Fin 4 → ℤ} (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B)
    (hDq : Dq ∈ B) (hAp : A ≠ p) (hBp : Bq ≠ p) (hDp : Dq ≠ p) (hBA : Bq ≠ A) (hDA : Dq ≠ A)
    (hDB : Dq ≠ Bq) (hσ : σ = 1 ∨ σ = -1) (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1)
    (hd : ∀ φ ∈ B, 0 < d φ) (hγr : Function.Injective γr) (hγt : Function.Injective γt)
    (hγrB : ∀ l, γr l ∈ B) (hγtB : ∀ l, γt l ∈ B) (hεr : ∀ l, εr l = 1 ∨ εr l = -1)
    (hεt : ∀ l, εt l = 1 ∨ εt l = -1)
    (hγrc : ∀ l, γr l ≠ p ∧ γr l ≠ A ∧ γr l ≠ Bq ∧ γr l ≠ Dq)
    (hγtc : ∀ l, γt l ≠ p ∧ γt l ≠ A ∧ γt l ≠ Bq ∧ γt l ≠ Dq)
    (hxr : ∀ φ ∈ B, xr φ = fixedPart p A Bq Dq σ τ₀ κ φ + ∑ l, εr l * unitVector (γr l) φ)
    (hxt : ∀ φ ∈ B, xt φ = fixedPart p A Bq Dq σ τ₀ κ φ + ∑ l, εt l * unitVector (γt l) φ)
    (hyr : ∀ φ ∈ B, yr φ = ∑ l, (quadSign l * εr l) * unitVector (γr l) φ)
    (hyt : ∀ φ ∈ B, yt φ = ∑ l, (quadSign l * εt l) * unitVector (γt l) φ)
    (hxx : ∑ φ ∈ B, xr φ * xt φ = 4) (hyy : ∑ φ ∈ B, yr φ * yt φ = 0)
    (hyx : ∑ φ ∈ B, yr φ * xt φ = 0) (hxy : ∑ φ ∈ B, yt φ * xr φ = 0)
    (hr₀ : εr 0 * d (γr 0) + εr 1 * d (γr 1) = V) (hr₁ : εr 2 * d (γr 2) + εr 3 * d (γr 3) = V)
    (ht₀ : εt 0 * d (γt 0) + εt 1 * d (γt 1) = V)
    (ht₁ : εt 2 * d (γt 2) + εt 3 * d (γt 3) = V) :
    ∀ l l', γr l ≠ γt l' := by
  obtain ⟨hPp, hPA, hPB, hPD⟩ := fixedPart_core σ τ₀ κ hAp hBp hDp hBA hDA hDB
  set P := fixedPart p A Bq Dq σ τ₀ κ with hP
  have hPγr : ∀ l, P (γr l) = 0 := fun l => by
    obtain ⟨h1, h2, h3, h4⟩ := hγrc l
    exact fixedPart_of_ne σ τ₀ κ h1 h2 h3 h4
  have hPγt : ∀ l, P (γt l) = 0 := fun l => by
    obtain ⟨h1, h2, h3, h4⟩ := hγtc l
    exact fixedPart_of_ne σ τ₀ κ h1 h2 h3 h4
  have hPP : ∑ φ ∈ B, P φ * P φ = 4 := by
    rw [sum_mul_fixedPart hp hA hBq hDq, hPp, hPA, hPB, hPD]
    rcases hσ with rfl | rfl <;> rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;>
      norm_num
  have hPU : ∀ (γ : Fin 4 → ι) (a : Fin 4 → ℤ), (∀ l, γ l ∈ B) → (∀ l, P (γ l) = 0) →
      ∑ φ ∈ B, P φ * ∑ l, a l * unitVector (γ l) φ = 0 := by
    intro γ a hγ h0
    rw [sum_mul_lincomb hγ]
    exact Finset.sum_eq_zero fun l _ => by rw [h0 l, mul_zero]
  have hcomm : ∀ f g : ι → ℤ, ∑ φ ∈ B, f φ * g φ = ∑ φ ∈ B, g φ * f φ :=
    fun f g => Finset.sum_congr rfl fun φ _ => mul_comm _ _
  have hUU : ∑ φ ∈ B, (∑ l, εr l * unitVector (γr l) φ) * (∑ l, εt l * unitVector (γt l) φ) =
      0 := by
    have hexp : ∑ φ ∈ B, xr φ * xt φ = ∑ φ ∈ B, P φ * P φ +
        ∑ φ ∈ B, P φ * (∑ l, εt l * unitVector (γt l) φ) +
        ∑ φ ∈ B, P φ * (∑ l, εr l * unitVector (γr l) φ) +
        ∑ φ ∈ B, (∑ l, εr l * unitVector (γr l) φ) * (∑ l, εt l * unitVector (γt l) φ) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun φ hφ => by rw [hxr φ hφ, hxt φ hφ]; ring
    rw [hxx, hPP, hPU γt εt hγtB hPγt, hPU γr εr hγrB hPγr] at hexp
    linarith
  have hUY : ∑ φ ∈ B, (∑ l, εr l * unitVector (γr l) φ) * yt φ = 0 := by
    have hexp : ∑ φ ∈ B, yt φ * xr φ = ∑ φ ∈ B, P φ * yt φ +
        ∑ φ ∈ B, (∑ l, εr l * unitVector (γr l) φ) * yt φ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun φ hφ => by rw [hxr φ hφ]; ring
    have hPy : ∑ φ ∈ B, P φ * yt φ = 0 := by
      rw [Finset.sum_congr rfl fun φ hφ => by rw [hyt φ hφ]]
      exact hPU γt _ hγtB hPγt
    rw [hxy, hPy] at hexp
    linarith
  have hYU : ∑ φ ∈ B, yr φ * (∑ l, εt l * unitVector (γt l) φ) = 0 := by
    have hexp : ∑ φ ∈ B, yr φ * xt φ = ∑ φ ∈ B, P φ * yr φ +
        ∑ φ ∈ B, yr φ * (∑ l, εt l * unitVector (γt l) φ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun φ hφ => by rw [hxt φ hφ]; ring
    have hPy : ∑ φ ∈ B, P φ * yr φ = 0 := by
      rw [Finset.sum_congr rfl fun φ hφ => by rw [hyr φ hφ]]
      exact hPU γr _ hγrB hPγr
    rw [hyx, hPy] at hexp
    linarith
  exact quadruple_disjoint (Ur := fun φ => ∑ l, εr l * unitVector (γr l) φ)
    (Ut := fun φ => ∑ l, εt l * unitVector (γt l) φ) hγr hγt hγrB hεr hεt hd
    (fun _ _ => rfl) hyr (fun _ _ => rfl) hyt hUU hUY hYU hyy hr₀ hr₁ ht₀ ht₁

end CFSG.Wreathed.ConditionalFiveFixed
