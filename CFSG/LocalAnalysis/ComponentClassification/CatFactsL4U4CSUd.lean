module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUc
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem mul_conj_mul_inv' {X : Type*} [Group X] (φ : MulAut X) (x : X) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
    map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_mem_CAU_of_normalizes {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    {x : StatedProj (StatedSU 4 (p ^ f) K)} (hx : ∀ y, y ∈ J' ↔ x * y * x⁻¹ ∈ J')
    {g : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hg : g ∈ CAU J') :
    (MulAut.conj x)⁻¹ * g * MulAut.conj x ∈ CAU J' := by
  intro y hy
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hg _ ((hx y).1 hy), ← map_inv,
    MulAut.conj_apply]
  group

theorem eq_one_or_eq_z (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K} {z : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hz : IsCU h A z) (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJeq : J' = (⁅(Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype,
      (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype⁆ :
        Subgroup (unitarySU p f K 4)).map (thU p f K))
    (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J') (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J')
    {τ' : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hτ : τ' ∈ CAU J')
    {x₁ x₂ : StatedProj (StatedSU 4 (p ^ f) K)} (hx₁ : MulAut.conj x₁ * z = z * MulAut.conj x₁)
    (hx₂ : MulAut.conj x₂ * z = z * MulAut.conj x₂) {T : unitarySU p f K 4} {t₁ t₂ : K}
    (hT : cP P T = blk t₁ 0 0 t₂) (hT2 : thU p f K T ^ 2 ≠ 1)
    (h₁ : τ' * MulAut.conj (x₁ * thU p f K T * x₁⁻¹) =
      MulAut.conj (x₁ * thU p f K T * x₁⁻¹) * τ')
    (h₂ : τ' * MulAut.conj (x₂ * thU p f K (sU h P hP) * x₂⁻¹) =
      MulAut.conj (x₂ * thU p f K (sU h P hP) * x₂⁻¹) * τ') :
    τ' = 1 ∨ τ' = z := by
  classical
  have : Finite K := h.finite
  have hfix : ∀ {g : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
      {x : StatedProj (StatedSU 4 (p ^ f) K)}, g * MulAut.conj x = MulAut.conj x * g → g x = x := by
    intro g x hgx
    apply conj_injective_U h hp2
    rw [← mul_conj_mul_inv', hgx, mul_inv_cancel_right]
  have hx₁J := normalizes_of_comm h hp2 hz hJeq hx₁
  have hx₂J := normalizes_of_comm h hp2 hz hJeq hx₂
  set u₁ := x₁ * thU p f K T * x₁⁻¹ with hu₁
  have hTCA := conj_mem_CAU_of_blk h hp2 P hl0 hAP hJeq hT
  have hu₁CA : MulAut.conj u₁ ∈ CAU J' := by
    intro y hy
    have hy' : x₁⁻¹ * y * x₁ ∈ J' := by
      rw [hx₁J]
      have e : x₁ * (x₁⁻¹ * y * x₁) * x₁⁻¹ = y := by group
      rwa [e]
    have hu := hTCA _ hy'
    rw [MulAut.conj_apply] at hu ⊢
    calc u₁ * y * u₁⁻¹ = x₁ * (thU p f K T * (x₁⁻¹ * y * x₁) * (thU p f K T)⁻¹) * x₁⁻¹ := by
          rw [hu₁]; group
      _ = y := by rw [hu]; group
  have hu₁sq : u₁ ^ 2 ≠ 1 := by
    intro h1
    apply hT2
    have e : u₁ ^ 2 = x₁ * thU p f K T ^ 2 * x₁⁻¹ := by rw [hu₁, sq, sq]; group
    rw [e] at h1
    have e2 : thU p f K T ^ 2 = x₁⁻¹ * (x₁ * thU p f K T ^ 2 * x₁⁻¹) * x₁ := by group
    rw [e2, h1]
    group
  obtain ⟨B, φ, hB, hBu, hlift, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2
    (d := 4) (by norm_num) (thU p f K) (thU_surjective)
    (by
      rw [QuotientGroup.ker_mk']
      intro w hw
      exact mem_center_of_mem_scal hw) τ'
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hBu' : uStar h (B : Matrix (Fin 4) (Fin 4) K) * (B : Matrix (Fin 4) (Fin 4) K) = 1 := hBu
  obtain ⟨xb, b, e, yb, hblk, -, hcase⟩ := blk_of_fix h hp2 P hP hμ hBu' hlift
    (hτ _ (hJU 1)) (hτ _ (hJL 1)) (hτ _ (hJU μ))
  have hInn : ∃ B₀ : GL (Fin 4) K, IsCU h B₀ τ' := by
    rcases hcase with ⟨hφ, -, -⟩ | ⟨hφ, hx0, hy0⟩
    · subst hφ
      refine ⟨B, hBu', fun g g' hg => ?_⟩
      rw [← hlift g]
      congr 1
      apply Subtype.ext
      change B * glAut (RingEquiv.refl K) (g : GL (Fin 4) K) * B⁻¹ = (g' : GL (Fin 4) K)
      rw [glAut_refl, hg]
    · exfalso
      rw [hx0, hy0] at hblk
      obtain ⟨U₁, hU₁⟩ := thU_surjective u₁
      have hU₁CA : MulAut.conj (thU p f K U₁) ∈ CAU J' := hU₁ ▸ hu₁CA
      obtain ⟨x', y', hblk', hun'⟩ := blk_of_mem_AU h hp2 P hP hJU hJL (isCU_conj h U₁) hU₁CA
      have hcP : cP P U₁ = blk x' 0 0 y' := by
        rw [← hblk', cP, Units.val_mul, Units.val_mul]
      have hinv := unitaryConjHom_eq_inv_of_bar h P hφ (hB := hB) hblk U₁ hcP hun'
      have h1 : τ' u₁ = u₁⁻¹ := by
        rw [← hU₁, ← hlift U₁, hinv, map_inv]
      have h2 := hfix h₁
      rw [h1] at h2
      apply hu₁sq
      rw [sq]
      nth_rewrite 1 [← h2]
      exact inv_mul_cancel u₁
  obtain ⟨B₀, hB₀⟩ := hInn
  obtain ⟨X₂, hX₂⟩ := thU_surjective x₂
  set τ'' := (MulAut.conj x₂)⁻¹ * τ' * MulAut.conj x₂ with hτ''
  have hτ''CA : τ'' ∈ CAU J' := conj_mem_CAU_of_normalizes hx₂J hτ
  have hX₂C := isCU_conj h X₂
  rw [hX₂] at hX₂C
  have hτ''CU : IsCU h ((X₂ : GL (Fin 4) K)⁻¹ * B₀ * X₂) τ'' :=
    (hX₂C.inv h).mul h hB₀ |>.mul h hX₂C
  have hAU : τ'' ∈ CAU J' ⊓ InnU p f K h := Subgroup.mem_inf.2 ⟨hτ''CA, _, hτ''CU⟩
  obtain ⟨x'', y'', hblk'', -⟩ := blk_of_mem_AU h hp2 P hP hJU hJL hτ''CU hτ''CA
  have hsinv := conj_swap_inv h P hP hτ''CU hblk''
  have hcomm : MulAut.conj (thU p f K (sU h P hP)) * τ'' =
      τ'' * MulAut.conj (thU p f K (sU h P hP)) := by
    have e : MulAut.conj (x₂ * thU p f K (sU h P hP) * x₂⁻¹) =
        MulAut.conj x₂ * MulAut.conj (thU p f K (sU h P hP)) * (MulAut.conj x₂)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [e] at h₂
    calc MulAut.conj (thU p f K (sU h P hP)) * τ''
        = (MulAut.conj x₂)⁻¹ * ((MulAut.conj x₂ * MulAut.conj (thU p f K (sU h P hP)) *
          (MulAut.conj x₂)⁻¹) * τ') * MulAut.conj x₂ := by rw [hτ'']; group
      _ = (MulAut.conj x₂)⁻¹ * (τ' * (MulAut.conj x₂ * MulAut.conj (thU p f K (sU h P hP)) *
          (MulAut.conj x₂)⁻¹)) * MulAut.conj x₂ := by rw [h₂]
      _ = τ'' * MulAut.conj (thU p f K (sU h P hP)) := by rw [hτ'']; group
  have hsq : τ'' ^ 2 = 1 := by
    have e : τ'' = τ''⁻¹ := by rw [← hsinv, hcomm, mul_inv_cancel_right]
    rw [sq]
    nth_rewrite 2 [e]
    exact mul_inv_cancel τ''
  have hback : τ' = MulAut.conj x₂ * τ'' * (MulAut.conj x₂)⁻¹ := by rw [hτ'']; group
  rcases eq_one_or_eq_of_sq_AU h hp2 P hP hl0 hz hAP hJU hJL hAU hsq with h3 | h3
  · left
    rw [hback, h3, mul_one, mul_inv_cancel]
  · right
    rw [hback, h3, hx₂, mul_inv_cancel_right]

end CSU

end CFSG.ComponentClassification.CatFactsL4U4
