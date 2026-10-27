module

public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabU
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal mem_center_of_mem_scal)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (unitaryConjHom coe_unitaryConjHom)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem eq_smul_of_comm {M : Matrix (Fin 4) (Fin 4) K}
    (hM : ∀ g : unitarySU p f K 4, M * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * M) :
    ∃ c : K, M = c • 1 := by
  have hq : 2 ≤ p ^ f := by
    have := h.prime.two_le
    calc 2 ≤ p := this
      _ ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
  refine RankThree.PartOne.KCUnitary.exists_smul_one_of_commute_gramSU h (by norm_num) hq
    fun A hA => ?_
  rw [← unitarySU_eq_gramSU h] at hA
  exact (hM ⟨A, hA⟩).symm

theorem exists_lift (hp2 : p ≠ 2) (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (hα : ∀ x, α (α x) = x) :
    ∃ (A : GL (Fin 4) K) (ψ : unitarySU p f K 4 →* unitarySU p f K 4),
      uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (∀ g, α (QuotientGroup.mk g) = QuotientGroup.mk (ψ g)) ∧
      (((∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
        ∃ c : K, (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = c • 1) ∨
      ((∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (A : Matrix (Fin 4) (Fin 4) K) *
            ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
        ∃ c : K, (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
          c • 1)) := by
  classical
  have : Finite K := h.finite
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 4) (by norm_num) θ hθ hker α
  obtain ⟨hφ, hcomp⟩ := hinv hα
  set ψ := unitaryConjHom A φ hA with hψdef
  have hcomp' : ∀ g : unitarySU p f K 4, ψ (ψ g) = g := fun g => by
    have := congrArg (fun F : unitarySU p f K 4 →* unitarySU p f K 4 => F g) hcomp
    exact this
  refine ⟨A, ψ, hAu, fun g => (hlift g).symm, ?_⟩
  rcases hφ with hφ1 | hφb
  · left
    subst hφ1
    have hgl1 : ∀ Y : GL (Fin 4) K, glAut (RingEquiv.refl K) Y = Y := fun Y => by
      change glAut 1 Y = Y
      rw [map_one]
      rfl
    refine ⟨fun g => ?_, ?_⟩
    · rw [hψdef, coe_unitaryConjHom, hgl1, Units.val_mul, Units.val_mul]
    · apply eq_smul_of_comm h
      intro g
      have e1 := congrArg (fun Y : unitarySU p f K 4 => (Y : GL (Fin 4) K)) (hcomp' g)
      simp only [hψdef, coe_unitaryConjHom, hgl1] at e1
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
    refine ⟨fun g => ?_, ?_⟩
    · rw [hψdef, coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut, hφb']
    · apply eq_smul_of_comm h
      intro g
      have e1 := congrArg (fun Y : unitarySU p f K 4 => (Y : GL (Fin 4) K)) (hcomp' g)
      simp only [hψdef, coe_unitaryConjHom, map_mul, map_inv, hglφ] at e1
      have e2 : A * glAut φ A * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (A * glAut φ A) := by
        calc A * glAut φ A * (g : GL (Fin 4) K) =
            (A * (glAut φ A * (g : GL (Fin 4) K) * (glAut φ A)⁻¹) * A⁻¹) * (A * glAut φ A) := by
              group
          _ = (g : GL (Fin 4) K) * (A * glAut φ A) := by rw [e1]
      have e3 := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e2
      simp only [Units.val_mul, coe_glAut] at e3
      rw [hφb'] at e3
      simpa only [Matrix.mul_assoc] using e3

end Catalog7U4

end CFSG.ComponentClassification.GSThmB
