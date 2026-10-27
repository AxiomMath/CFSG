module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeValues
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeWeighted
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeSolve
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeBase

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatRelative

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.FlatComplete

namespace Support

variable {ι : Type*} {BB : Finset ι} {m M : ℕ} {V : Finset (ZMod m × ZMod m)}
  {X : ZMod m → ι → ℂ} {c : ZMod m → ZMod m → ι → ℂ} {δ₀ δ₁ δ₂ δ₃ δ₄ α γ : ℤ}
  {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι} {ψ : ZMod m × ZMod m → ι}
  {er : ℕ → Fin 2}
  (hS : Support BB m M V X c δ₀ δ₁ δ₂ δ₃ δ₄ α γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ er)
include hS

theorem values_central [NeZero m] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hpow : ∃ n, m = 2 ^ n)
    (hMeven : Even M) {q : ℕ} {ε : ℤ} (val : ι → ℂ) (lam Φ : ℂ) (hlam : lam = 1)
    (hΦ : Φ = q)
    (hsec : ∀ χ ∈ BB, 2 * val χ = lam * ((1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j χ + (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
          (∑ i : ZMod m, c i (0 - i) χ - ∑ i : ZMod m, c i (-(j : ZMod m) - i) χ))) :
    val χ₀ = δ₀ * ε * q ∧ val χ₁ = -δ₁ ∧ val χ₂ = -(δ₂ * (2 + ε * q)) ∧
      val χ₃ = δ₃ * (1 + 2 * ε * q) ∧ (∀ e, val (P 1 e) = δ₂ * ε * q) ∧
      ∀ e, val (Q 1 e) = -δ₃ := by
  have hm := hS.hm
  have hM2 := hS.hM
  have hMm : M ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have h1M : 1 ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  obtain ⟨x₀, x₁, x₂, x₃, -, -⟩ := hS.values hζ hMm val lam Φ ε hsec
  have hneg : (-1 : ℂ) ^ M = 1 := hMeven.neg_one_pow
  have hP := fun e => hS.values_even hζ hpow val lam Φ ε hsec h1M e
  subst hlam hΦ
  rw [hneg] at x₂ x₃
  refine ⟨by rw [x₀]; ring, by rw [x₁]; ring, by rw [x₂]; ring, by rw [x₃]; ring,
    fun e => ?_, fun e => ?_⟩
  · rw [(hP e).1]
    ring
  · rw [(hP e).2]
    ring

theorem alternatives [NeZero m] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hpow : ∃ n, m = 2 ^ n)
    (hMeven : Even M) {q : ℕ} (hq3 : 3 ≤ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (deg : ι → ℤ)
    {D Δ β : ℤ} (hpos : 0 < deg χ₀ ∧ 0 < deg χ₁ ∧ 0 < deg χ₂ ∧ 0 < deg χ₃ ∧ 0 < deg χ₄)
    (hD : 0 < D) (hΔ : 0 < Δ) (hdξ : ∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = D)
    (hdPQ : ∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = deg χ₂ ∧ deg (Q r er) = deg χ₃)
    (hdψ : ∀ I ∈ V, deg (ψ I) = Δ)
    (hlin1 : δ₀ * deg χ₀ + δ₁ * deg χ₁ = -(α * D)) (hlin2 : δ₂ * deg χ₂ + δ₃ * deg χ₃ = -(α * D))
    (h4 : δ₄ * deg χ₄ = δ₃ * deg χ₃ - δ₀ * deg χ₀) (hgΔ : γ * Δ = δ₂ * deg χ₂ - δ₃ * deg χ₃)
    (s₀ : δ₀ = 1 ∨ δ₀ = -1) (s₁ : δ₁ = 1 ∨ δ₁ = -1) (s₂ : δ₂ = 1 ∨ δ₂ = -1)
    (s₃ : δ₃ = 1 ∨ δ₃ = -1) (s₄ : δ₄ = 1 ∨ δ₄ = -1) (sα : α = 1 ∨ α = -1)
    (sβ : β = 1 ∨ β = -1) (sγ : γ = 1 ∨ γ = -1)
    (Y₀ : ι → ℤ) (hY0 : ∀ χ ∈ BB, Y₀ χ = (β • (Pi.single χ₀ δ₀ + Pi.single χ₁ δ₁ -
      Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃ : ι → ℤ)) χ)
    (val : ι → ℂ) (lam Φ : ℂ) (hlam : lam = 1) (hΦ : Φ = q)
    (hsec : ∀ χ ∈ BB, 2 * val χ = lam * ((1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j χ + (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
          (∑ i : ZMod m, c i (0 - i) χ - ∑ i : ZMod m, c i (-(j : ZMod m) - i) χ)))
    (wt : ι → ℂ) (hwt : ∀ χ ∈ BB, wt χ = val χ * val χ / (deg χ : ℂ))
    (hEY : ∑ χ ∈ BB, wt χ * (Y₀ χ : ℂ) = 0)
    (hEX : ∑ χ ∈ BB, wt χ * X (-(2 * ((1 : ℕ) : ZMod m))) χ = 0) :
    Xor
      ((deg χ₀ = (q : ℤ) ^ 3 * deg χ₁ ∧ deg χ₂ = ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg χ₃ = q * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg χ₄ = q * (q + ε) * deg χ₁) ∧
        (δ₀ = -(ε * δ₁) ∧ δ₂ = δ₁ ∧ δ₃ = -(ε * δ₁) ∧ δ₄ = -δ₁ ∧ α = ε * δ₁ ∧ γ = ε * δ₁) ∧
        D = ((q : ℤ) ^ 3 - ε) * deg χ₁ ∧
        (∀ h ∈ (Finset.Ico 1 m).filter Odd, deg (ξ h) = ((q : ℤ) ^ 3 - ε) * deg χ₁) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
          deg (Q r er) = q * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁) ∧
        Δ = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁ ∧
        ∀ I ∈ V, deg (ψ I) = (q + ε) * ((q : ℤ) ^ 2 + ε * q + 1) * deg χ₁)
      ((q : ℤ) ∣ deg χ₁ ∧
        (q * deg χ₀ = deg χ₁ ∧ q * deg χ₂ = deg χ₁ ∧ deg χ₃ = deg χ₁ ∧
          q * deg χ₄ = (q + ε) * deg χ₁) ∧
        (δ₀ = -(ε * δ₁) ∧ δ₂ = -(ε * δ₁) ∧ δ₃ = δ₁ ∧ δ₄ = δ₁ ∧ α = -δ₁ ∧ γ = -δ₁) ∧
        q * D = (q - ε) * deg χ₁ ∧
        (∀ h ∈ (Finset.Ico 1 m).filter Odd, q * deg (ξ h) = (q - ε) * deg χ₁) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ er, q * deg (P r er) = deg χ₁ ∧ deg (Q r er) = deg χ₁) ∧
        q * Δ = (q + ε) * deg χ₁ ∧ ∀ I ∈ V, q * deg (ψ I) = (q + ε) * deg χ₁) := by
  obtain ⟨hf₀, hf₁, hf₂, hf₃, hf₄⟩ := hpos
  have h1M : 1 ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr ⟨le_rfl, by have := hS.hM; omega⟩
  obtain ⟨v₀, v₁, v₂, v₃, vP, vQ⟩ :=
    hS.values_central hζ hpow hMeven val lam Φ hlam hΦ (q := q) (ε := ε) hsec
  obtain ⟨hP0, hQ0⟩ := hS.memPQ 1 h1M 0
  obtain ⟨hP1, hQ1⟩ := hS.memPQ 1 h1M 1
  obtain ⟨dP0, dQ0⟩ := hdPQ 1 h1M 0
  obtain ⟨dP1, dQ1⟩ := hdPQ 1 h1M 1
  have E1 : (β : ℂ) * ((δ₀ : ℂ) * ε * q * (δ₀ * ε * q) / (deg χ₀ : ℂ) * δ₀ +
      -(δ₁ : ℂ) * -δ₁ / (deg χ₁ : ℂ) * δ₁ -
      -((δ₂ : ℂ) * (2 + ε * q)) * -(δ₂ * (2 + ε * q)) / (deg χ₂ : ℂ) * δ₂ -
      (δ₃ : ℂ) * (1 + 2 * ε * q) * (δ₃ * (1 + 2 * ε * q)) / (deg χ₃ : ℂ) * δ₃) = 0 := by
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hY0 χ hχ], ← weightedSum_apply, map_zsmul,
      map_sub, map_sub, map_add, weightedSum_single wt hS.memχ₀,
      weightedSum_single wt hS.memχ₁, weightedSum_single wt hS.memχ₂,
      weightedSum_single wt hS.memχ₃, zsmul_eq_mul, hwt χ₀ hS.memχ₀, hwt χ₁ hS.memχ₁,
      hwt χ₂ hS.memχ₂, hwt χ₃ hS.memχ₃, v₀, v₁, v₂, v₃] at hEY
    exact hEY
  have E2 : (δ₀ : ℂ) * ε * q * (δ₀ * ε * q) / (deg χ₀ : ℂ) * δ₀ +
      -(δ₁ : ℂ) * -δ₁ / (deg χ₁ : ℂ) * δ₁ +
      -((δ₂ : ℂ) * (2 + ε * q)) * -(δ₂ * (2 + ε * q)) / (deg χ₂ : ℂ) * δ₂ +
      (δ₃ : ℂ) * (1 + 2 * ε * q) * (δ₃ * (1 + 2 * ε * q)) / (deg χ₃ : ℂ) * δ₃ -
      (δ₂ : ℂ) * ε * q * (δ₂ * ε * q) / (deg χ₂ : ℂ) * δ₂ -
      (δ₂ : ℂ) * ε * q * (δ₂ * ε * q) / (deg χ₂ : ℂ) * δ₂ -
      -(δ₃ : ℂ) * -δ₃ / (deg χ₃ : ℂ) * δ₃ - -(δ₃ : ℂ) * -δ₃ / (deg χ₃ : ℂ) * δ₃ = 0 := by
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hS.Xeven 1 h1M χ hχ], ← weightedSum_apply,
      map_sub, map_sub, map_sub, map_sub, map_add, map_add, map_add,
      weightedSum_single wt hS.memχ₀, weightedSum_single wt hS.memχ₁,
      weightedSum_single wt hS.memχ₂, weightedSum_single wt hS.memχ₃,
      weightedSum_single wt hP0, weightedSum_single wt hP1, weightedSum_single wt hQ0,
      weightedSum_single wt hQ1, hwt χ₀ hS.memχ₀, hwt χ₁ hS.memχ₁, hwt χ₂ hS.memχ₂,
      hwt χ₃ hS.memχ₃, hwt _ hP0, hwt _ hP1, hwt _ hQ0, hwt _ hQ1, v₀, v₁, v₂, v₃, vP, vP,
      vQ, vQ, dP0, dP1, dQ0, dQ1] at hEX
    exact hEX
  have h1 := weighted_first hε sβ s₀ s₁ s₂ s₃ hf₀.ne' hf₁.ne' hf₂.ne' hf₃.ne' E1
  have h2 := weighted_second hε s₀ s₁ s₂ s₃ hf₀.ne' hf₁.ne' hf₂.ne' hf₃.ne' E2
  have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have hcases := flat_alternatives hq3' hε hf₀ hf₁ hf₂ hf₃ hf₄ hD hΔ s₀ s₁ s₂ s₃ s₄ sα sγ hlin1
    hlin2 h4 hgΔ h1 h2
  have hexcl : deg χ₀ = (q : ℤ) ^ 3 * deg χ₁ → q * deg χ₀ = deg χ₁ → False := by
    intro hc hr
    have h0 : ((q : ℤ) ^ 4 - 1) * deg χ₁ = 0 := by linear_combination -(q : ℤ) * hc + hr
    have h81 : (3 : ℤ) ^ 4 ≤ (q : ℤ) ^ 4 := pow_le_pow_left₀ (by norm_num) hq3' 4
    have hq4 : (0 : ℤ) < (q : ℤ) ^ 4 - 1 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hq4.ne'
    · exact absurd h hf₁.ne'
  rcases hcases with ⟨d₀, d₂, d₃, d₄, e₀, e₂, e₃, e₄, eα, eγ, dD, dΔ⟩ |
      ⟨hdvd, d₀, d₂, d₃, d₄, e₀, e₂, e₃, e₄, eα, eγ, dD, dΔ⟩
  · refine Or.inl ⟨⟨⟨d₀, d₂, d₃, d₄⟩, ⟨e₀, e₂, e₃, e₄, eα, eγ⟩, dD, fun h hh => ?_,
      fun r hr er => ?_, dΔ, fun I hI => ?_⟩, fun hR => hexcl d₀ hR.2.1.1⟩
    · rw [hdξ h hh, dD]
    · rw [(hdPQ r hr er).1, (hdPQ r hr er).2, d₂, d₃]
      exact ⟨rfl, rfl⟩
    · rw [hdψ I hI, dΔ]
  · refine Or.inr ⟨⟨hdvd, ⟨d₀, d₂, d₃, d₄⟩, ⟨e₀, e₂, e₃, e₄, eα, eγ⟩, dD, fun h hh => ?_,
      fun r hr er => ?_, dΔ, fun I hI => ?_⟩, fun hC => hexcl hC.1.1 d₀⟩
    · rw [hdξ h hh, dD]
    · rw [(hdPQ r hr er).1, (hdPQ r hr er).2, d₂, d₃]
      exact ⟨rfl, rfl⟩
    · rw [hdψ I hI, dΔ]

theorem chi_one_base [NeZero m] {A : Type*} [Group A] [Fintype A] {σ υ : A} {ζ : ℂ}
    (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m)
    (hυ : orderOf υ = m) (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥)
    (hζ : IsPrimitiveRoot ζ m) {lamU : ZMod m → ZMod m → A →* ℂ}
    (hlamU : ∀ i j, lamU i j σ = ζ ^ i.val ∧ lamU i j υ = ζ ^ j.val) (χ : A → ℂ)
    (Fs : ZMod m → ι → ℂ) (q₀ : ℂ)
    (hcdef : ∀ i j, c i j χ₁ = (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lamU 0 0 x)) -
      (Nat.card A : ℂ)⁻¹ * (∑ x : A, χ x * conj (lamU i j x)) +
        q₀ * (Fs i χ₁ + Fs j χ₁ + Fs (-i - j) χ₁))
    (hrecon : ∀ j : ZMod m, X j χ₁ + 2 * Fs j χ₁ =
      ∑ i : ZMod m, c i (0 - i) χ₁ - ∑ i : ZMod m, c i (-j - i) χ₁)
    (hF0 : Fs 0 χ₁ = 0) {u : A} (hu : u ≠ 1) : χ u = -δ₁ := by
  have hFs := hS.fs_core_one Fs hrecon hF0
  refine eq_neg_of_multiplicity hc hgen hσ hυ hint hζ hlamU χ δ₁ (fun i j hij => ?_) hu
  have h := (hS.c_core (i, j)).2.1
  rw [ite_eq_right hij] at h
  have h' := hcdef i j
  rw [hFs, hFs, hFs] at h'
  linear_combination h' - h

end Support

end CFSG.Wreathed.FlatRelative
