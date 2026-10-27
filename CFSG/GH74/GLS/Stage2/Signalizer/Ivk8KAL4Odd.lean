module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Def

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

theorem ka_pl4_sq_fixed {G : Type*} [Group G] (θ : MulAut G) {Z : Subgroup G}
    (hZ : Z ≤ center G) (hθ2 : ∀ x, θ (θ x) = x) (hZθ : ∀ z ∈ Z, θ z = z) {g : G}
    (hg : g⁻¹ * θ g ∈ Z) : θ (g * g) = g * g := by
  obtain ⟨t, htdef⟩ : ∃ t : G, t = g⁻¹ * θ g := ⟨_, rfl⟩
  have ht : t ∈ Z := htdef ▸ hg
  have hθg : θ g = g * t := by rw [htdef]; group
  have hθt : θ t = t := hZθ t ht
  have htc : ∀ x : G, x * t = t * x := fun x => Subgroup.mem_center_iff.mp (hZ ht) x
  have h1 : g = g * t * t := by
    calc g = θ (θ g) := (hθ2 g).symm
      _ = θ (g * t) := congrArg θ hθg
      _ = θ g * θ t := map_mul θ g t
      _ = g * t * t := by rw [hθg, hθt]
  have htt : t * t = 1 := by
    refine mul_left_cancel (a := g) ?_
    rw [mul_one, ← mul_assoc]
    exact h1.symm
  rw [map_mul, hθg]
  calc g * t * (g * t) = g * (t * g) * t := by group
    _ = g * (g * t) * t := by rw [← htc g]
    _ = g * g * (t * t) := by group
    _ = g * g := by rw [htt, mul_one]

theorem ka_pl4_slConj_scalar {F : Type} [Field F] (A : GL (Fin 4) F) {t : SL(4, F)}
    (ht : t ∈ scalars 4 F) : CatalogueBHigherLinearAction.slConjugation 4 F A t = t := by
  obtain ⟨u, -, hu⟩ := mem_scalars.mp ht
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation]
  have h1 : Matrix.SpecialLinearGroup.toGL t = GeneralLinearGroup.scalar (Fin 4) u :=
    Units.ext hu
  rw [h1, ← GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]

theorem ka_odd_mem_map_cent_pl4 {F : Type} [Field F] [Finite F] (A : GL (Fin 4) F) (c : Fˣ)
    (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c) {y : projectiveSL 4 F}
    (hy : conjAut 4 F A y = y) (ho : Odd (orderOf y)) : y ∈ (kaSlCent A).map (proj 4 F) := by
  obtain ⟨g, rfl⟩ := proj_surjective 4 F y
  have hθ2 : ∀ x : SL(4, F),
      CatalogueBHigherLinearAction.slConjugation 4 F A
        (CatalogueBHigherLinearAction.slConjugation 4 F A x) = x := by
    intro x
    have h1 : CatalogueBHigherLinearAction.slConjugation 4 F A *
        CatalogueBHigherLinearAction.slConjugation 4 F A = 1 := by
      rw [← map_mul (CatalogueBHigherLinearAction.slConjugation 4 F) A A, hA,
        CatalogueBHigherLinearAction.slConjugation_scalar]
    exact congrArg (fun e : MulAut SL(4, F) => e x) h1
  have hy' : proj 4 F (CatalogueBHigherLinearAction.slConjugation 4 F A g) = proj 4 F g := by
    rw [← conjAut_proj]
    exact hy
  have hg : g⁻¹ * CatalogueBHigherLinearAction.slConjugation 4 F A g ∈ scalars 4 F :=
    proj_eq_proj_iff.mp hy'.symm
  have hfix := ka_pl4_sq_fixed (CatalogueBHigherLinearAction.slConjugation 4 F A)
    (scalars_le_center 4 F) hθ2 (fun _ hz => ka_pl4_slConj_scalar A hz) hg
  have hmem : g * g ∈ kaSlCent A := by
    show Matrix.SpecialLinearGroup.toGL (g * g) ∈ Subgroup.centralizer ({A} : Set (GL (Fin 4) F))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h1 := CatalogueBHigherLinearAction.toGL_slConjugation 4 F A (g * g)
    rw [hfix] at h1
    calc A * Matrix.SpecialLinearGroup.toGL (g * g)
        = A * Matrix.SpecialLinearGroup.toGL (g * g) * A⁻¹ * A := by group
      _ = Matrix.SpecialLinearGroup.toGL (g * g) * A := by rw [← h1]
  have hsq : proj 4 F g * proj 4 F g ∈ (kaSlCent A).map (proj 4 F) := by
    rw [← map_mul]
    exact ⟨g * g, hmem, rfl⟩
  exact ka_odd_mem_of_sq_mem hsq ho

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
