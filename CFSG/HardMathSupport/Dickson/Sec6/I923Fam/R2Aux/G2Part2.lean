module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2Part1

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem pinnedX_mem_g2Q {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) (x : K) : X γ x ∈ g2Q K :=
  pinnedX_mem_rootSpan (S := {γ | γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c}) hγ x

theorem exists_pinnedX_r_mul_g2Q_of_mem_posUnipotent {u : ModGL .G2 K}
    (hu : u ∈ posUnipotent .G2 K) : ∃ s : K, ∃ q ∈ g2Q K, u = X g2r s * q := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hu
  refine ⟨A, X g2a B * X g2u C * X g2v D * X g2b E * X g2c F, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (pinnedX_mem_g2Q (Or.inl rfl) B)
      (pinnedX_mem_g2Q (Or.inr (Or.inl rfl)) C)) (pinnedX_mem_g2Q (Or.inr (Or.inr (Or.inl rfl))) D))
      (pinnedX_mem_g2Q (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) E))
      (pinnedX_mem_g2Q (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) F)
  · simp only [g2N, mul_assoc]

theorem exists_mem_mul_of_commute_c [Finite K] {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K)
    {y : K} (hy : y ≠ 0) (hgz : g * X g2c y = X g2c y * g) :
    ∃ q ∈ g2Q K, ∃ l ∈ g2RankOne K g2ir, g = q * l := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_bruhat hg
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := exists_torus_mul_of_mem_borel hb₁
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := exists_torus_mul_of_mem_borel hb₂
  obtain ⟨c₁, hc₁, -⟩ := torus_scale_c hh₁
  obtain ⟨c₂, hc₂, -⟩ := torus_scale_c hh₂
  obtain ⟨ε, hε, hεn⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w isRoot_g2c
  set n := canonicalRep (coxeterSystem .G2) K w with hn
  have hu₁c : ∀ z, u₁ * X g2c z = X g2c z * u₁ := fun z =>
    (commute_pinnedX_c_posUnipotent z hu₁).eq.symm
  have hu₂c : ∀ z, u₂ * X g2c z = X g2c z * u₂ := fun z =>
    (commute_pinnedX_c_posUnipotent z hu₂).eq.symm
  have hgz' : h₁ * u₁ * n * (h₂ * u₂) * X g2c y * (h₁ * u₁ * n * (h₂ * u₂))⁻¹ = X g2c y := by
    rw [hgz, mul_inv_cancel_right]
  have hconj₂ : h₂ * u₂ * X g2c y * (h₂ * u₂)⁻¹ = X g2c (c₂ * y) := by
    calc h₂ * u₂ * X g2c y * (h₂ * u₂)⁻¹ = h₂ * (u₂ * X g2c y) * u₂⁻¹ * h₂⁻¹ := by group
      _ = X g2c (c₂ * y) := by rw [hu₂c, mul_assoc h₂, mul_inv_cancel_right, hc₂]
  have hconj₁ : (h₁ * u₁)⁻¹ * X g2c y * (h₁ * u₁) = X g2c (c₁⁻¹ * y) := by
    have e := hc₁ (c₁⁻¹ * y)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at e
    calc (h₁ * u₁)⁻¹ * X g2c y * (h₁ * u₁) = u₁⁻¹ * (h₁⁻¹ * X g2c y * h₁) * u₁ := by group
      _ = u₁⁻¹ * (h₁⁻¹ * (h₁ * X g2c (c₁⁻¹ * y) * h₁⁻¹) * h₁) * u₁ := by rw [e]
      _ = u₁⁻¹ * (X g2c (c₁⁻¹ * y) * u₁) := by group
      _ = X g2c (c₁⁻¹ * y) := by rw [← hu₁c, inv_mul_cancel_left]
  have hW : X (w • g2c) (ε * (c₂ * y)) = X g2c (c₁⁻¹ * y) := by
    rw [← hεn, ← hconj₂, ← hconj₁]
    calc n * (h₂ * u₂ * X g2c y * (h₂ * u₂)⁻¹) * n⁻¹ =
        (h₁ * u₁)⁻¹ * (h₁ * u₁ * n * (h₂ * u₂) * X g2c y *
          (h₁ * u₁ * n * (h₂ * u₂))⁻¹) * (h₁ * u₁) := by group
      _ = (h₁ * u₁)⁻¹ * X g2c y * (h₁ * u₁) := by rw [hgz']
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
  have hnL : n ∈ g2RankOne K g2ir := by
    rcases weyl_eq_of_pinnedX_c (mul_ne_zero hε0 (mul_ne_zero c₂.ne_zero hy))
      (mul_ne_zero (Units.ne_zero _) hy) hW with rfl | rfl
    · rw [hn, canonicalRep_one]
      exact one_mem _
    · rw [hn, canonicalRep_simple]
      exact weylElt_mem_g2RankOne g2ir 1
  have hc12 : X g2c ((c₁ * c₂ : Kˣ) * y) = X g2c y := by
    rw [← hgz']
    calc X g2c ((c₁ * c₂ : Kˣ) * y) = h₁ * X g2c (c₂ * y) * h₁⁻¹ := by
          rw [hc₁, Units.val_mul, mul_assoc]
      _ = h₁ * (u₁ * (n * X g2c (c₂ * y) * n⁻¹) * u₁⁻¹) * h₁⁻¹ := by
          rw [(commute_g2RankOne_pinnedX_c hnL _).eq, mul_inv_cancel_right, hu₁c,
            mul_inv_cancel_right]
      _ = _ := by rw [← hconj₂]; group
  obtain ⟨c, hc, hcL⟩ := torus_scale_c (mul_mem hh₁ hh₂)
  have hc1 : c = 1 := by
    have e : X g2c ((c : K) * y) = X g2c y := by
      rw [← hc]
      calc h₁ * h₂ * X g2c y * (h₁ * h₂)⁻¹ = h₁ * (h₂ * X g2c y * h₂⁻¹) * h₁⁻¹ := by group
        _ = X g2c ((c₁ * c₂ : Kˣ) * y) := by rw [hc₂, hc₁, Units.val_mul, mul_assoc]
        _ = X g2c y := hc12
    have e' := pinnedX_injective .G2 K _ e
    exact Units.ext (by simpa [hy] using e')
  have hl₂ : h₁ * h₂ ∈ g2RankOne K g2ir := hcL hc1
  have hl₁ : h₁ * n * h₁⁻¹ ∈ g2RankOne K g2ir := torus_conj_mem_g2RankOne_r hh₁ hnL
  obtain ⟨s₁, q₁, hq₁, hu₁'⟩ :=
    exists_pinnedX_r_mul_g2Q_of_mem_posUnipotent (torus_conj_mem_posUnipotent hh₁ hu₁)
  obtain ⟨s₂, q₂, hq₂, rfl⟩ := exists_pinnedX_r_mul_g2Q_of_mem_posUnipotent hu₂
  have hu₁e : u₁ = h₁⁻¹ * (X g2r s₁ * q₁) * h₁ := by rw [← hu₁']; group
  subst hu₁e
  have hxL : ∀ s : K, X g2r s ∈ g2RankOne K g2ir := fun s => by
    rw [← xUnit_g2ir]; exact xUnit_mem_g2RankOne g2ir s
  set l₃ := X g2r s₁ * (h₁ * n * h₁⁻¹) * (h₁ * h₂) * X g2r s₂ with hl₃
  have hl₃L : l₃ ∈ g2RankOne K g2ir :=
    mul_mem (mul_mem (mul_mem (hxL s₁) hl₁) hl₂) (hxL s₂)
  refine ⟨X g2r s₁ * q₁ * (X g2r s₁)⁻¹ * (l₃ * q₂ * l₃⁻¹),
    mul_mem (g2RankOne_normalizes_g2Q (hxL s₁) hq₁) (g2RankOne_normalizes_g2Q hl₃L hq₂), l₃, hl₃L,
    ?_⟩
  rw [hl₃]
  group

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
