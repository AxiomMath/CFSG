module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Core
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Chevalley
open scoped MatrixGroups

variable {F : Type} [Field F] {K : Type} [Group K]

theorem linAct_conj3 {Φ : SL2 F →* K} {x : K} (g : K) (h : LinAct Φ x) :
    LinAct ((MulAut.conj g).toMonoidHom.comp Φ) (g * x * g⁻¹) := by
  obtain ⟨D, hD⟩ := h
  refine ⟨D, fun A => ?_⟩
  show g * x * g⁻¹ * (g * Φ A * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * Φ (glConjSL D A) * g⁻¹
  rw [← hD A]
  group

variable [Finite F]

theorem eq_of_sylow_le_normalizer_of_chart3 (hodd : Odd (Nat.card F)) {Φ₀ : SL2 F →* K}
    (hΦ₀ : Function.Injective Φ₀)
    (H1₀ : ∀ x : K, x * Φ₀ (-1) = Φ₀ (-1) * x → LinAct Φ₀ x)
    (HS : ∀ Ψ : SL2 F →* K, Function.Injective Ψ →
      (∀ A, Ψ A * Φ₀ (-1) = Φ₀ (-1) * Ψ A) → Ψ (-1) = Φ₀ (-1))
    (g₀ g : K) {R : Subgroup K} (hRJ : R ≤ conjSub g (conjSub g₀ Φ₀.range))
    (hR2 : IsPGroup 2 R)
    (hmax : ∀ T : Subgroup K, T ≤ conjSub g (conjSub g₀ Φ₀.range) → IsPGroup 2 T →
      R ≤ T → T = R)
    (hRN : R ≤ Subgroup.normalizer ((conjSub g₀ Φ₀.range : Subgroup K) : Set K)) :
    conjSub g (conjSub g₀ Φ₀.range) = conjSub g₀ Φ₀.range := by
  set Φ : SL2 F →* K := (MulAut.conj g₀).toMonoidHom.comp Φ₀ with hΦ
  set Ψ : SL2 F →* K := (MulAut.conj (g * g₀)).toMonoidHom.comp Φ₀ with hΨ
  have hΦr : Φ.range = conjSub g₀ Φ₀.range := MonoidHom.range_comp _ _
  have hΨr : Ψ.range = conjSub g (conjSub g₀ Φ₀.range) := by
    rw [← conjSub_mul]
    exact MonoidHom.range_comp _ _
  have hΨinj : Function.Injective Ψ := (MulAut.conj (g * g₀)).injective.comp hΦ₀
  have hconjLin : ∀ h x : K, x * (h * Φ₀ (-1) * h⁻¹) = (h * Φ₀ (-1) * h⁻¹) * x →
      LinAct ((MulAut.conj h).toMonoidHom.comp Φ₀) x := by
    intro h x hx
    have h1 : (h⁻¹ * x * h) * Φ₀ (-1) = Φ₀ (-1) * (h⁻¹ * x * h) := by
      calc h⁻¹ * x * h * Φ₀ (-1) = h⁻¹ * (x * (h * Φ₀ (-1) * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * Φ₀ (-1) * h⁻¹) * x) * h := by rw [hx]
        _ = Φ₀ (-1) * (h⁻¹ * x * h) := by group
    have := linAct_conj3 h (H1₀ _ h1)
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [e] at this
  have H1 : ∀ x : K, x * Φ (-1) = Φ (-1) * x → LinAct Φ x := fun x hx => hconjLin g₀ x hx
  have H2 : ∀ x : K, x * Ψ (-1) = Ψ (-1) * x → LinAct Ψ x := fun x hx => hconjLin (g * g₀) x hx
  let P : Sylow 2 (SL2 F) :=
    ⟨R.comap Ψ, hR2.comap_of_injective Ψ hΨinj, fun {T} hT hle => by
      have h1 : T.map Ψ ≤ conjSub g (conjSub g₀ Φ₀.range) := hΨr ▸ Subgroup.map_le_range Ψ T
      have h3 : R ≤ T.map Ψ := by
        intro x hx
        obtain ⟨y, rfl⟩ : x ∈ Ψ.range := hΨr ▸ hRJ hx
        exact ⟨y, hle hx, rfl⟩
      have h5 := hmax _ h1 (hT.map Ψ) h3
      refine le_antisymm (fun y hy => ?_) hle
      show Ψ y ∈ R
      rw [← h5]
      exact ⟨y, hy, rfl⟩⟩
  have hc : IsUniqueInvolution (conjSub g₀ Φ₀.range) (g₀ * Φ₀ (-1) * g₀⁻¹) :=
    (isUniqueInvolution_range_sl2 hodd hΦ₀).conj g₀
  have H5 : ∀ x ∈ (P : Subgroup (SL2 F)), Ψ x * Φ (-1) = Φ (-1) * Ψ x := by
    intro x hx
    have hxR : Ψ x ∈ R := hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (normalizer_le_centralizer hc (hRN hxR))
  have hneg : Ψ (-1) * Φ (-1) = Φ (-1) * Ψ (-1) := H5 (-1) (neg_one_mem_sylow hodd P)
  obtain ⟨D, hD⟩ := H2 (Φ (-1)) hneg.symm
  have hDfix : ∀ x ∈ (P : Subgroup (SL2 F)), glConjSL D x = x := by
    intro x hx
    apply hΨinj
    rw [← hD x, ← H5 x hx]
    group
  have hDall := glConjSL_eq_of_fix_sylow hodd P hDfix
  have hJc : ∀ A, Ψ A * Φ (-1) = Φ (-1) * Ψ A := by
    intro A
    have h1 := hD A
    rw [hDall A] at h1
    calc Ψ A * Φ (-1) = Φ (-1) * Ψ A * (Φ (-1))⁻¹ * Φ (-1) := by rw [h1]
      _ = Φ (-1) * Ψ A := by group
  have hΨ₁inj : Function.Injective ((MulAut.conj g₀⁻¹).toMonoidHom.comp Ψ) :=
    (MulAut.conj g₀⁻¹).injective.comp hΨinj
  have e : Φ₀ (-1) = g₀⁻¹ * Φ (-1) * g₀ := by
    show Φ₀ (-1) = g₀⁻¹ * (g₀ * Φ₀ (-1) * g₀⁻¹) * g₀
    group
  have hΨ₁c : ∀ A, ((MulAut.conj g₀⁻¹).toMonoidHom.comp Ψ) A * Φ₀ (-1) =
      Φ₀ (-1) * ((MulAut.conj g₀⁻¹).toMonoidHom.comp Ψ) A := by
    intro A
    rw [e]
    show g₀⁻¹ * Ψ A * g₀⁻¹⁻¹ * (g₀⁻¹ * Φ (-1) * g₀) =
      g₀⁻¹ * Φ (-1) * g₀ * (g₀⁻¹ * Ψ A * g₀⁻¹⁻¹)
    calc g₀⁻¹ * Ψ A * g₀⁻¹⁻¹ * (g₀⁻¹ * Φ (-1) * g₀) = g₀⁻¹ * (Ψ A * Φ (-1)) * g₀ := by group
      _ = g₀⁻¹ * (Φ (-1) * Ψ A) * g₀ := by rw [hJc A]
      _ = g₀⁻¹ * Φ (-1) * g₀ * (g₀⁻¹ * Ψ A * g₀⁻¹⁻¹) := by group
  have hHS := HS _ hΨ₁inj hΨ₁c
  have hΨΦ : Ψ (-1) = Φ (-1) := by
    have h1 : g₀⁻¹ * Ψ (-1) * g₀⁻¹⁻¹ = Φ₀ (-1) := hHS
    calc Ψ (-1) = g₀ * (g₀⁻¹ * Ψ (-1) * g₀⁻¹⁻¹) * g₀⁻¹ := by group
      _ = g₀ * Φ₀ (-1) * g₀⁻¹ := by rw [h1]
      _ = Φ (-1) := rfl
  have hgc : g * Φ (-1) = Φ (-1) * g := by
    have h1 : g * Φ (-1) * g⁻¹ = Φ (-1) := by
      have : Ψ (-1) = g * Φ (-1) * g⁻¹ := by
        show (g * g₀) * Φ₀ (-1) * (g * g₀)⁻¹ = g * (g₀ * Φ₀ (-1) * g₀⁻¹) * g⁻¹
        group
      rw [← this, hΨΦ]
    calc g * Φ (-1) = g * Φ (-1) * g⁻¹ * g := by group
      _ = Φ (-1) * g := by rw [h1]
  have hgc' : g⁻¹ * Φ (-1) = Φ (-1) * g⁻¹ := by
    calc g⁻¹ * Φ (-1) = g⁻¹ * (Φ (-1) * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * Φ (-1)) * g⁻¹ := by rw [hgc]
      _ = Φ (-1) * g⁻¹ := by group
  obtain ⟨D₁, hD₁⟩ := H1 g hgc
  obtain ⟨D₂, hD₂⟩ := H1 g⁻¹ hgc'
  have hgN : g ∈ Subgroup.normalizer (Φ.range : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨glConjSL D₁ A, (hD₁ A).symm⟩
    · rintro ⟨A, hA⟩
      refine ⟨glConjSL D₂ A, ?_⟩
      have h1 := hD₂ A
      rw [hA] at h1
      rw [← h1]
      group
  rw [← hΦr]
  exact normalizer_iff_conjSub_eq.mp hgN

end CFSG.ClassicalInvolution.Q3.Q3MT
