module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUGraph

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_of_mk_eq_of_trace (h4 : (4 : K) ≠ 0) {u g : unitarySU p f K 4}
    (h1 : (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) = QuotientGroup.mk g)
    (hu : ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4) : u = g := by
  rw [QuotientGroup.eq] at h1
  obtain ⟨c, hc⟩ := val_of_mem_scal h1
  have hgm : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((c : K) • 1) := by
    rw [← hc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hc1 : (c : K) = 1 := by
    have := congrArg Matrix.trace hgm
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, hu, hg, smul_eq_mul] at this
    have h5 : (4 : K) * (1 - c) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd h6 h4
    · linear_combination -h6
  rw [hc1, one_smul, Matrix.mul_one] at hgm
  exact (ext_val hgm).symm

include h in
theorem exists_steinberg_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))) (hα2 : α ^ 2 = 1) :
    ∃ (A : GL (Fin 4) K) (ψ : unitarySU p f K 4 →* unitarySU p f K 4),
      uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (∀ g, (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) =
        α (QuotientGroup.mk g)) ∧
      (((∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
        ∃ c : K, (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = c • 1) ∨
      ((∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (A : Matrix (Fin 4) (Fin 4) K) *
            ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
        ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1 ∧
          (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K) ∨
         (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 ∧
          (A : Matrix (Fin 4) (Fin 4) K)ᵀ = (A : Matrix (Fin 4) (Fin 4) K)))) := by
  classical
  have : Finite K := h.finite
  have hαα : ∀ x, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, ← sq, hα2, MulAut.one_apply]
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  have hq5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    ClassicalInvolution.ModelFacts.UnitaryAut.exists_lift_unitarySU h hp2 hq5 (d := 4)
      (by norm_num) θ hθ hker α
  obtain ⟨hφ, hcomp⟩ := hinv hαα
  set ψ := ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA with hψdef
  have hcomp' : ∀ g : unitarySU p f K 4, ψ (ψ g) = g := fun g => by
    have := congrArg (fun F : unitarySU p f K 4 →* unitarySU p f K 4 => F g) hcomp
    exact this
  refine ⟨A, ψ, hAu, hlift, ?_⟩
  rcases hφ with hφ1 | hφb
  · left
    subst hφ1
    have hgl1 : ∀ Y : GL (Fin 4) K, glAut (RingEquiv.refl K) Y = Y := fun Y => by
      change glAut 1 Y = Y
      rw [map_one]
      rfl
    refine ⟨fun g => ?_, ?_⟩
    · rw [hψdef, ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hgl1,
        Units.val_mul, Units.val_mul]
    · apply eq_smul_one_of_comm h hp2 hq
      intro g
      have e1 := congrArg (fun Y : unitarySU p f K 4 => (Y : GL (Fin 4) K)) (hcomp' g)
      simp only [hψdef, ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hgl1] at e1
      have e2 : A * A * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (A * A) := by
        calc A * A * (g : GL (Fin 4) K) =
            (A * (A * (g : GL (Fin 4) K) * A⁻¹) * A⁻¹) * (A * A) := by group
          _ = (g : GL (Fin 4) K) * (A * A) := by rw [e1]
      have e3 := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e2
      simpa only [Units.val_mul, Matrix.mul_assoc] using e3
  · right
    have hφb' : (φ : K → K) = h.bar := funext hφb
    have hφφ : φ * φ = 1 := RingEquiv.ext fun c => by
      change φ (φ c) = c
      rw [hφb, hφb, h.bar_bar]
    have hglφ : ∀ Y : GL (Fin 4) K, glAut φ (glAut φ Y) = Y := fun Y => by
      have := congrArg (fun χ : MulAut (GL (Fin 4) K) => χ Y)
        (show glAut φ * glAut φ = 1 by rw [← map_mul, hφφ, map_one])
      exact this
    have hcommA : ∀ g : unitarySU p f K 4,
        (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar) := by
      intro g
      have e1 := congrArg (fun Y : unitarySU p f K 4 => (Y : GL (Fin 4) K)) (hcomp' g)
      simp only [hψdef, ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, map_mul,
        map_inv, hglφ] at e1
      have e2 : A * glAut φ A * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (A * glAut φ A) := by
        calc A * glAut φ A * (g : GL (Fin 4) K) =
            (A * (glAut φ A * (g : GL (Fin 4) K) * (glAut φ A)⁻¹) * A⁻¹) * (A * glAut φ A) := by
              group
          _ = (g : GL (Fin 4) K) * (A * glAut φ A) := by rw [e1]
      have e3 := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e2
      simp only [Units.val_mul, coe_glAut] at e3
      rw [hφb'] at e3
      simpa only [Matrix.mul_assoc] using e3
    refine ⟨fun g => ?_, ?_⟩
    · rw [hψdef, ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, Units.val_mul,
        Units.val_mul, coe_glAut, hφb']
    · obtain ⟨ε, hε, hAA, hAt⟩ := symm_or_alt_of_graph h hp2 hq hAu hcommA
      rcases hε with rfl | rfl
      · right
        exact ⟨by rw [hAA, one_smul], by rw [hAt, one_smul]⟩
      · left
        exact ⟨by rw [hAA, neg_one_smul], by rw [hAt, neg_one_smul]⟩

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
