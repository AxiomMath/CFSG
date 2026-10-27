module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Group

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


section D4F2BigCell

theorem d4F2_bigCell_conj_borel {τ : Tag} {K : Type} [Field K] {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hlam : entry g (negLabel hθ.1) (rootLabel hθ.1) ≠ 0) :
    ∃ (b : ↥(adjointGroup τ K)) (χ μ : K), b ∈ borelSubD τ K ∧ χ ≠ 0 ∧
      (∀ c : K, b * xPar (rootOperatorFamily τ) θ c * b⁻¹ = xPar (rootOperatorFamily τ) θ (χ * c)) ∧
      (χ⁻¹ * μ = entry g (negLabel hθ.1) (rootLabel hθ.1) ∨
        χ⁻¹ * μ = -entry g (negLabel hθ.1) (rootLabel hθ.1)) ∧
      ∀ c : K, g * xPar (rootOperatorFamily τ) θ c * g⁻¹ =
        b * xPar (rootOperatorFamily τ) (-θ) (μ * c) * b⁻¹ := by
  classical
  obtain ⟨w, b₁, b₂, hb₁, hb₂, hg⟩ := exists_bruhat_decomp_all g
  obtain ⟨χ₁, -, hz₁, hc₁⟩ := borel_stab_all hθ hb₁
  obtain ⟨χ₂, hv₂, -, hc₂⟩ := borel_stab_all hθ hb₂
  obtain ⟨θ', hθ', ε, ε', hε, hε', -, hvw, hxw⟩ := wordProd_stab_all (K := K) hθ w
  have hentry : entry g (negLabel hθ.1) (rootLabel hθ.1) =
      (χ₂ : K) * ε * (((χ₁⁻¹ : Kˣ) : K) * (rootVec τ K θ') (negLabel hθ.1)) := by
    unfold entry
    have hv : (Finsupp.single (rootLabel hθ.1) (1 : K) : RootModule τ K) = rootVec τ K θ :=
      (rootVec_eq_single hθ.1).symm
    rw [hv, hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv₂, map_smul, hvw,
      map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, hz₁]
    simp only [smul_eq_mul]
    ring
  have hθ'eq : θ' = -θ := by
    by_contra hne
    apply hlam
    rw [hentry]
    have : (rootVec τ K θ') (negLabel hθ.1) = 0 := by
      rw [rootVec_eq_single hθ', Finsupp.single_apply, if_neg]
      intro h
      apply hne
      have h' := h
      simp only [negLabel, rootLabel, Sum.inr.injEq, Subtype.mk.injEq] at h'
      exact h'
    rw [this]
    simp
  subst hθ'eq
  have hone : (rootVec τ K (-θ)) (negLabel hθ.1) = 1 := by
    rw [rootVec_eq_single hθ']
    simp [negLabel, rootLabel]
  rw [hone] at hentry
  refine ⟨b₁, (χ₁ : K), (ε' : K) * χ₂, hb₁, Units.ne_zero _, hc₁, ?_, fun c => ?_⟩
  · have hχ : ((χ₁⁻¹ : Kˣ) : K) = (χ₁ : K)⁻¹ := by simp
    have hlamE : entry g (negLabel hθ.1) (rootLabel hθ.1) = (χ₂ : K) * ε * (χ₁ : K)⁻¹ := by
      rw [hentry, hχ]
      ring
    have hχ0 : (χ₁ : K) ≠ 0 := Units.ne_zero _
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
    · left; rw [hlamE]; push_cast; field_simp
    · right; rw [hlamE]; push_cast; field_simp
    · right; rw [hlamE]; push_cast; field_simp
    · left; rw [hlamE]; push_cast; field_simp
  · have e : g * xPar (rootOperatorFamily τ) θ c * g⁻¹ =
        b₁ * (wordProdD τ K w * (b₂ * xPar (rootOperatorFamily τ) θ c * b₂⁻¹) *
          (wordProdD τ K w)⁻¹) * b₁⁻¹ := by
      rw [hg]
      group
    rw [e, hc₂, hxw]
    congr 3
    ring

theorem d4F2_bigCell_conj_Q {K : Type} [Field K] (g : ↥(adjointGroup Tag.D4 K))
    (hlam : entry g (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1) ≠ 0) :
    ∃ q ∈ d4F2_Qgrp K, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      g * xPar (rootOperatorFamily Tag.D4) d4F2Theta c * g⁻¹ =
        q * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) ((ε : K) *
          entry g (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1) * c) * q⁻¹ := by
  obtain ⟨b, χ, μ, hb, -, hbθ, hμ, hg⟩ := d4F2_bigCell_conj_borel d4F2_theta_isMax g hlam
  obtain ⟨q, hq, m, ⟨χm, hm1, hm2⟩, rfl⟩ := d4F2_exists_Q_decomp hb
  have hχm : (χm : K) = χ := by
    have h1 := hbθ 1
    have e : q * m * xPar (rootOperatorFamily Tag.D4) d4F2Theta 1 * (q * m)⁻¹ =
        q * (m * xPar (rootOperatorFamily Tag.D4) d4F2Theta 1 * m⁻¹) * q⁻¹ := by group
    rw [e, hm1 1, (d4F2_commute_Q_theta hq _).eq, mul_inv_cancel_right] at h1
    have := xPar_injective d4F2_isRoot_theta h1
    simpa using this
  refine ⟨q, hq, ?_⟩
  have hε : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ χ⁻¹ * μ = (ε : K) *
      entry g (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1) := by
    rcases hμ with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  obtain ⟨ε, hε1, hε2⟩ := hε
  refine ⟨ε, hε1, fun c => ?_⟩
  have hs : ((χm⁻¹ : Kˣ) : K) * (μ * c) = (ε : K) *
      entry g (negLabel d4F2_theta_isMax.1) (rootLabel d4F2_theta_isMax.1) * c := by
    rw [Units.val_inv_eq_inv_val, hχm, ← hε2]
    ring
  have e : q * m * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) (μ * c) * (q * m)⁻¹ =
      q * (m * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) (μ * c) * m⁻¹) * q⁻¹ := by group
  rw [hg c, e, hm2 (μ * c), hs]

end D4F2BigCell

end CFSG.LieType.SeitzGeneration.ExcWideThree
