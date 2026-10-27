module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreLink
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreGlue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Good

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Link
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Glue

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem actZ_smul (A : GL (Fin 2) F4) (s : F4) (c : Fin 2 → F4) :
    actZ A (s • c) = s • actZ A c := by
  rw [actZ_apply, actZ_apply]
  exact map_smul (F4lin A) s c

theorem psiOf_pow {X : Submodule (ZMod 2) V} {ρ : V ≃ₗ[ZMod 2] V} {w : V} (hw : w ∈ X)
    (hinv : ∀ x ∈ X, ρ x ∈ X) (hquad : ∀ x ∈ X, ρ (ρ x) + ρ x + x = 0) (n : ℕ) (a : F4) :
    (ρ ^ n) (psiOf w ρ a) = psiOf w ρ (Model.omega ^ n * a) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    calc (ρ ^ (n + 1)) (psiOf w ρ a) = ρ ((ρ ^ n) (psiOf w ρ a)) := by
          rw [pow_succ', LinearEquiv.mul_apply]
      _ = ρ (psiOf w ρ (Model.omega ^ n * a)) := by rw [ih]
      _ = psiOf w ρ (Model.omega * (Model.omega ^ n * a)) :=
          psiOf_compat hw hinv hquad (fun x _ => rfl) _
      _ = psiOf w ρ (Model.omega ^ (n + 1) * a) := by rw [pow_succ', mul_assoc]

theorem TA_phi {U : Submodule (ZMod 2) V} (φ : (Fin 2 → Model.F4) ≃ₗ[ZMod 2] U)
    (A : GL (Fin 2) Model.F4) (c : Fin 2 → Model.F4) :
    ((TA φ A (φ c) : U) : V) = ((φ (actZ A c) : U) : V) := by
  simp only [TA, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem TA_comm_scalar {U : Submodule (ZMod 2) V} (φ : (Fin 2 → Model.F4) ≃ₗ[ZMod 2] U)
    (A : GL (Fin 2) Model.F4) (f : V ≃ₗ[ZMod 2] V) (s : Model.F4)
    (hf : ∀ c, f (φ c : V) = ((φ (s • c) : U) : V)) (u u' : U) (hu' : (u' : V) = f (u : V)) :
    f ((TA φ A u : U) : V) = ((TA φ A u' : U) : V) := by
  obtain ⟨c, rfl⟩ := φ.surjective u
  have hu'c : u' = φ (s • c) := Subtype.ext (by rw [hu', hf c])
  rw [hu'c, TA_phi, TA_phi, hf (actZ A c), actZ_smul]

theorem glueA_comm_f {U Uc : Submodule (ZMod 2) V} (hc : IsCompl U Uc)
    (φ : (Fin 2 → Model.F4) ≃ₗ[ZMod 2] U) (A : GL (Fin 2) Model.F4) (f : V ≃ₗ[ZMod 2] V)
    (s : Model.F4) (hf : ∀ c, f (φ c : V) = ((φ (s • c) : U) : V))
    (hfU : ∀ u ∈ U, f u ∈ U) (hfUc : ∀ u ∈ Uc, f u ∈ Uc) (x : V) :
    f (glueA hc φ A x) = glueA hc φ A (f x) := by
  obtain ⟨u, u', rfl⟩ := exists_decomp_glue hc x
  have hv : f (u : V) ∈ U := hfU _ u.2
  have hv' : f (u' : V) ∈ Uc := hfUc _ u'.2
  have key := TA_comm_scalar φ A f s hf u ⟨f u, hv⟩ rfl
  have h1 : glueA hc φ A (f (u : V)) = ((TA φ A ⟨f u, hv⟩ : U) : V) :=
    glueA_apply_left hc φ A ⟨f u, hv⟩
  have h2 : glueA hc φ A (f (u' : V)) = f (u' : V) :=
    glueA_apply_right hc φ A ⟨f u', hv'⟩
  rw [map_add, map_add, map_add, glueA_apply_left, glueA_apply_right, map_add, h1, h2,
    key]

theorem commutant_on_U {U : Submodule (ZMod 2) V} (φ : (Fin 2 → Model.F4) ≃ₗ[ZMod 2] U)
    {f₁ : V ≃ₗ[ZMod 2] V} (hf1 : ∀ c, f₁ (φ c : V) = ((φ (Model.omega • c) : U) : V))
    (g : V ≃ₗ[ZMod 2] V) (hgcomm : g * f₁ = f₁ * g)
    (hgU : ∀ u ∈ U, g u ∈ U) (hginvU : ∀ u ∈ U, g⁻¹ u ∈ U) :
    ∃ B : GL (Fin 2) Model.F4, ∀ u : U, g (u : V) = ((TA φ B u : U) : V) := by
  have hUmap : U.map (g : V →ₗ[ZMod 2] V) = U := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hgU x hx
    · intro u hu
      refine ⟨g⁻¹ u, hginvU u hu, ?_⟩
      show g (g.symm u) = u
      exact g.apply_symm_apply u
  let gU : U ≃ₗ[ZMod 2] U := LinearEquiv.ofSubmodules g U U hUmap
  have hgU_apply : ∀ u : U, ((gU u : U) : V) = g (u : V) := fun u => rfl
  let hU : (Fin 2 → Model.F4) ≃ₗ[ZMod 2] (Fin 2 → Model.F4) := φ.trans (gU.trans φ.symm)
  have hφhU : ∀ c, φ (hU c) = gU (φ c) := fun c => by
    simp [hU]
  have hcomm : ∀ x : V, g (f₁ x) = f₁ (g x) := fun x => by
    have := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) hgcomm
    simpa [LinearEquiv.mul_apply] using this
  have hω : ∀ c, hU (Model.omega • c) = Model.omega • hU c := by
    intro c
    apply φ.injective
    apply Subtype.ext
    rw [hφhU, hgU_apply, ← hf1 c, hcomm, ← hgU_apply, ← hφhU]
    show _ = ((φ (Model.omega • hU c) : U) : V)
    rw [← hf1 (hU c), hφhU]
  obtain ⟨B, hB⟩ := commutant_lemma hU hω
  refine ⟨B, fun u => ?_⟩
  obtain ⟨c, rfl⟩ := φ.surjective u
  rw [TA_phi, hB, hφhU, hgU_apply]

theorem glueA_conj {U Uc : Submodule (ZMod 2) V} (hc : IsCompl U Uc)
    (φ : (Fin 2 → Model.F4) ≃ₗ[ZMod 2] U) (g : V ≃ₗ[ZMod 2] V) (B A : GL (Fin 2) Model.F4)
    (hginvU : ∀ u ∈ U, g⁻¹ u ∈ U) (hginvUc : ∀ u ∈ Uc, g⁻¹ u ∈ Uc)
    (hB : ∀ u : U, g (u : V) = ((TA φ B u : U) : V)) (x : V) :
    (g * glueA hc φ A * g⁻¹) x = glueA hc φ (B * A * B⁻¹) x := by
  obtain ⟨u, u', rfl⟩ := exists_decomp_glue hc x
  have hBinv : ∀ w : U, ((TA φ B⁻¹ w : U) : V) = g⁻¹ (w : V) := by
    intro w
    have h1 := hB (TA φ B⁻¹ w)
    have h2 : TA φ B (TA φ B⁻¹ w) = w := by
      rw [← TA_mul, mul_inv_cancel]
      exact TA_one φ w
    rw [h2] at h1
    rw [← h1]
    exact (g.symm_apply_apply _).symm
  let a : U := ⟨g⁻¹ (u : V), hginvU _ u.2⟩
  let b : Uc := ⟨g⁻¹ (u' : V), hginvUc _ u'.2⟩
  have ha : a = TA φ B⁻¹ u := Subtype.ext (by rw [hBinv])
  have hTAconj : TA φ (B * A * B⁻¹) u = TA φ B (TA φ A (TA φ B⁻¹ u)) := by
    rw [TA_mul, TA_mul]
  have e1 : glueA hc φ A (g⁻¹ ((u : V) + (u' : V))) = ((TA φ A a : U) : V) + (b : V) := by
    rw [map_add]
    have h1 : g⁻¹ (u : V) = (a : V) := rfl
    have h2 : g⁻¹ (u' : V) = (b : V) := rfl
    rw [map_add, h1, h2, glueA_apply_left, glueA_apply_right]
  have e2 : g (((TA φ A a : U) : V)) = ((TA φ B (TA φ A a) : U) : V) := hB _
  have e3 : g (b : V) = (u' : V) := by
    show g (g⁻¹ (u' : V)) = (u' : V)
    exact g.apply_symm_apply _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, map_add, e2, e3]
  rw [map_add, glueA_apply_left, glueA_apply_right, hTAconj, ha]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Good

end
