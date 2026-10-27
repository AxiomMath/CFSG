module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUf
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_id_or_eq_bar (hp2 : p ≠ 2) (τ : K ≃+* K) (hτ : ∀ x ∈ h.fixedField, τ x = x) :
    (∀ x, τ x = x) ∨ ∀ x, τ x = h.bar x := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨t, ht, ht0⟩ := h.exists_mem_traceZero_ne_zero
  have htb : h.bar t = -t := by
    have h1 : h.trace t = 0 := ht
    rw [UnitaryFieldData.trace] at h1
    linear_combination h1
  have ht2 : t ^ 2 ∈ h.fixedField := by
    rw [h.mem_fixedField, map_pow, htb, neg_sq]
  have hτt : τ t = t ∨ τ t = -t := by
    have e : τ t ^ 2 = t ^ 2 := by rw [← map_pow, hτ _ ht2]
    have h1 : (τ t - t) * (τ t + t) = 0 := by linear_combination e
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h3)
  have hdec : ∀ x : K, ∃ a₀ a₁ : K, a₀ ∈ h.fixedField ∧ a₁ ∈ h.fixedField ∧ x = a₀ + t * a₁ :=
    fun x => by
      obtain ⟨hx0, hx1, hx⟩ := scalar_decomp htb ht0 h2 x
      exact ⟨_, _, hx0, hx1, hx⟩
  rcases hτt with h1 | h1
  · left
    intro x
    obtain ⟨a₀, a₁, hx0, hx1, rfl⟩ := hdec x
    rw [map_add, map_mul, hτ _ hx0, hτ _ hx1, h1]
  · right
    intro x
    obtain ⟨a₀, a₁, hx0, hx1, rfl⟩ := hdec x
    rw [map_add, map_mul, hτ _ hx0, hτ _ hx1, h1, map_add, map_mul, h.mem_fixedField.mp hx0,
      h.mem_fixedField.mp hx1, htb]

theorem exists_anti_form (hp2 : p ≠ 2) {φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hφ2 : φ ^ 2 = 1) (hφ : φ ∉ InnU p f K h) :
    ∃ (A : GL (Fin 4) K) (ψ : unitarySU p f K 4 →* unitarySU p f K 4),
      uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (∀ g, φ (QuotientGroup.mk g) = QuotientGroup.mk (ψ g)) ∧
      (∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
      ∃ c : K, (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
        c • 1 := by
  classical
  have : Finite K := h.finite
  have hker : (thU p f K).ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨A, τ, hA, hAu, hlift, hinv⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2
    (d := 4) (by norm_num) (thU p f K) thU_surjective hker φ
  have hφφ : ∀ x, φ (φ x) = x := fun x => by
    rw [← MulAut.mul_apply, ← pow_two, hφ2, MulAut.one_apply]
  obtain ⟨hτ, hcomp⟩ := hinv hφφ
  have hAU : A ∈ uMat h 4 := (mem_uMat h).2 hAu
  rcases hτ with rfl | hτb
  · exfalso
    apply hφ
    refine ⟨A, hAU, fun g g' hg => ?_⟩
    rw [← hlift g]
    congr 1
    apply Subtype.ext
    rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, glAut_refl, hg]
  · have hgl : ∀ X : GL (Fin 4) K, ((glAut τ X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (X : Matrix (Fin 4) (Fin 4) K).map h.bar := fun X => by
      ext i j
      exact hτb _
    have hττ : ∀ X : GL (Fin 4) K, glAut τ (glAut τ X) = X := fun X => by
      apply Units.ext
      rw [hgl, hgl, Matrix.map_map]
      ext i j
      exact h.bar_bar _
    refine ⟨A, ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A τ hA, hAu,
      fun g => (hlift g).symm, fun g => ?_, ?_⟩
    · rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, Units.val_mul,
        Units.val_mul, hgl]
    · set M : GL (Fin 4) K := A * glAut τ A with hM
      have hMU : M ∈ uMat h 4 := mul_mem hAU (glAut_mem_uMat h τ hAU)
      have hMg : ∀ g : unitarySU p f K 4, M * (g : GL (Fin 4) K) * M⁻¹ = g := by
        intro g
        have h1 := congrArg (fun χ : unitarySU p f K 4 →* unitarySU p f K 4 =>
          ((χ g : unitarySU p f K 4) : GL (Fin 4) K)) hcomp
        simp only [MonoidHom.comp_apply, MonoidHom.id_apply,
          ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, map_mul, map_inv,
          hττ] at h1
        refine Eq.trans ?_ h1
        rw [hM]
        group
      have hM1 : IsCU h M 1 := ⟨hMU, fun g g' hg => by
        rw [MulAut.one_apply]
        congr 1
        apply Subtype.ext
        rw [hg, hMg]⟩
      obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 hM1
      refine ⟨c, ?_⟩
      rw [← hc, hM, Units.val_mul, hgl]

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
