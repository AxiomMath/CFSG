module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Unique
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.FromThreeSpaces
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Polarity2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Spans

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem nonempty_iso_hermGraph {c : Γ.Coloring (Fin 2)} {q : ℕ}
    (hΓ : IsThasQuadrangle Γ c q) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (σ : K ≃+* K),
      Fintype.card K = q ^ 2 ∧ σ ≠ 1 ∧ σ * σ = 1 ∧ Nonempty (Γ ≃g HermGraph K σ) := by
  obtain ⟨K, hKfield, hKfintype, ι, hKcard, hι, hsec⟩ :=
    exists_isProjGQ (Γ := Γ) (c := c) (q := q) hΓ
  letI : Field K := hKfield
  letI : Fintype K := hKfintype
  obtain ⟨π, hπ, habs, hlines⟩ :=
    buekenhout_lefevre (Γ := Γ) hΓ.gp hΓ.thick c hΓ.deg ι hι hsec hΓ.two_le
  obtain ⟨σ, hσne, hσsq, hiso⟩ :=
    exists_iso_hermGraph_of_polarity (Γ := Γ) hΓ.gp hΓ.thick hΓ.two_le hKcard hι hsec
      π hπ habs hlines
  exact ⟨K, hKfield, hKfintype, σ, hKcard, hσne, hσsq, hiso⟩

private theorem exists_isThasQuadrangle_of_moufang {V : Type} {Γ : SimpleGraph V} [Fintype V]
    [DecidableRel Γ.Adj] {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V]
    [GraphAction H Γ] {q : ℕ} (hq : 2 ≤ q)
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    (hdegVal : ∀ v, Γ.degree v = q ^ 2 + 1 ∨ Γ.degree v = q ^ 3 + 1)
    (h2 : ∃ v, Γ.degree v = q ^ 2 + 1) (h3 : ∃ v, Γ.degree v = q ^ 3 + 1) :
    ∃ c : Γ.Coloring (Fin 2), IsThasQuadrangle Γ c q := by
  classical
  obtain ⟨c₀⟩ := hP.isBipartite
  obtain ⟨s, t, -, -, -, hdeg₀⟩ := hP.exists_order (by norm_num : 2 ≤ 4) hT c₀
  have hpow : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hdeg_at : ∀ v, Γ.degree v = t + 1 ∨ Γ.degree v = s + 1 := by
    intro v
    by_cases hv : c₀ v = 0
    · exact Or.inl (by simpa [hv] using hdeg₀ v)
    · exact Or.inr (by simpa [hv] using hdeg₀ v)
  obtain ⟨v₂, hv₂⟩ := h2
  obtain ⟨v₃, hv₃⟩ := h3
  have hst : (s = q ^ 2 ∧ t = q ^ 3) ∨ (s = q ^ 3 ∧ t = q ^ 2) := by
    have a := hdeg_at v₂
    have b := hdeg_at v₃
    rw [hv₂] at a
    rw [hv₃] at b
    rcases a with a | a <;> rcases b with b | b
    · omega
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · omega
  rcases hst with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · refine ⟨c₀, isThasQuadrangle_of_moufang hP hT c₀ ?_ hM⟩
    intro v
    simpa [hs, ht] using hdeg₀ v
  · refine ⟨dualColoring c₀, isThasQuadrangle_of_moufang hP hT (dualColoring c₀) ?_ hM⟩
    intro v
    by_cases hv : dualColoring c₀ v = 0
    · have hc : c₀ v = 1 := by
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        have h1 : 1 - c₀ v = 0 := by simpa [dualColoring_apply] using hv
        rcases hfin (c₀ v) with hc | hc
        · exfalso
          rw [hc] at h1
          simp at h1
        · exact hc
      rw [if_pos hv, hdeg₀ v, if_neg (by rw [hc]; decide), hs]
    · have hc : c₀ v = 0 := by
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        have h1 : 1 - c₀ v ≠ 0 := by simpa [dualColoring_apply] using hv
        rcases hfin (c₀ v) with hc | hc
        · exact hc
        · exact absurd (by rw [hc]; decide) h1
      rw [if_neg hv, hdeg₀ v, if_pos hc, ht]

theorem fgqHermitianUnique : FGQHermitianUnique := by
  intro q V₁ V₂ _ _ Γ₁ Γ₂ _ _ H₁ H₂ _ _ _ _ _ _ _ _
    hq hP₁ hT₁ hP₂ hT₂ hM₁ hM₂ hdeg₁ hdeg₂ h2₁ h3₁ h2₂ h3₂
  obtain ⟨c₁, hΓ₁⟩ := exists_isThasQuadrangle_of_moufang (Γ := Γ₁) hq hP₁ hT₁ hM₁ hdeg₁ h2₁ h3₁
  obtain ⟨c₂, hΓ₂⟩ := exists_isThasQuadrangle_of_moufang (Γ := Γ₂) hq hP₂ hT₂ hM₂ hdeg₂ h2₂ h3₂
  obtain ⟨K₁, hK₁field, hK₁fin, σ₁, hcard₁, hσ₁ne, hσ₁sq, ⟨e₁⟩⟩ :=
    nonempty_iso_hermGraph (Γ := Γ₁) hΓ₁
  obtain ⟨K₂, hK₂field, hK₂fin, σ₂, hcard₂, hσ₂ne, hσ₂sq, ⟨e₂⟩⟩ :=
    nonempty_iso_hermGraph (Γ := Γ₂) hΓ₂
  obtain ⟨e₁₂⟩ := hermGraph_iso (hcard₁.trans hcard₂.symm) hσ₁ne hσ₁sq hσ₂ne hσ₂sq
  haveI hfin₁ : Finite (Submodule K₁ (Fin 5 → K₁)) :=
    Finite.of_injective (fun U : Submodule K₁ (Fin 5 → K₁) => (U : Set (Fin 5 → K₁)))
      SetLike.coe_injective
  haveI hfin₂ : Finite (Submodule K₂ (Fin 5 → K₂)) :=
    Finite.of_injective (fun U : Submodule K₂ (Fin 5 → K₂) => (U : Set (Fin 5 → K₂)))
      SetLike.coe_injective
  haveI : ∀ x, Fintype ((HermGraph K₁ σ₁).neighborSet x) :=
    fun x => Fintype.ofFinite ((HermGraph K₁ σ₁).neighborSet x)
  haveI : ∀ x, Fintype ((HermGraph K₂ σ₂).neighborSet x) :=
    fun x => Fintype.ofFinite ((HermGraph K₂ σ₂).neighborSet x)
  refine ⟨e₂.symm.comp (e₁₂.comp e₁), ?_⟩
  intro v
  calc
    Γ₂.degree ((e₂.symm.comp (e₁₂.comp e₁)) v)
        = (HermGraph K₂ σ₂).degree (e₁₂ (e₁ v)) :=
          SimpleGraph.Iso.degree_eq e₂.symm (e₁₂ (e₁ v))
    _ = (HermGraph K₁ σ₁).degree (e₁ v) :=
          SimpleGraph.Iso.degree_eq e₁₂ (e₁ v)
    _ = Γ₁.degree v :=
          SimpleGraph.Iso.degree_eq e₁ v

end CFSG.Geometry.GeneralizedQuadrangles

end
