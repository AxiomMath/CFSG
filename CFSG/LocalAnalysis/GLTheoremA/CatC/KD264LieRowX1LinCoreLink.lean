module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Link

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem neg_eq_self_V (y : V) : -y = y :=
  neg_eq_of_add_eq_zero_left (by
    rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul])

@[expose] noncomputable def psiOf (w : V) (ρ : V ≃ₗ[ZMod 2] V) : Model.F4 →ₗ[ZMod 2] V :=
  Model.basisF4.constr (ZMod 2) ![w, ρ w]

theorem psiOf_apply (w : V) (ρ : V ≃ₗ[ZMod 2] V) (a : Model.F4) :
    psiOf w ρ a = Model.basisF4.repr a 0 • w + Model.basisF4.repr a 1 • ρ w := by
  rw [psiOf, Module.Basis.constr_apply_fintype, Fin.sum_univ_two]
  simp

theorem psiOf_one (w : V) (ρ : V ≃ₗ[ZMod 2] V) : psiOf w ρ 1 = w := by
  rw [← Model.basisF4_zero, psiOf, Module.Basis.constr_basis]
  simp

theorem psiOf_omega (w : V) (ρ : V ≃ₗ[ZMod 2] V) : psiOf w ρ Model.omega = ρ w := by
  rw [← Model.basisF4_one, psiOf, Module.Basis.constr_basis]
  simp

theorem li_plane {X : Submodule (ZMod 2) V} {ρ : V ≃ₗ[ZMod 2] V} {w : V} (hw : w ∈ X)
    (hw0 : w ≠ 0) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x) (hfix : ∀ x ∈ X, ρ x = x → x = 0)
    (hquad : ∀ x ∈ X, ρ (ρ x) + ρ x + x = 0) (hinv : ∀ x ∈ X, ρ x ∈ X) :
    LinearIndependent (ZMod 2) ![w, ρ w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hZ : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hZ s with rfl | rfl <;> rcases hZ t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso
    simp only [zero_smul, one_smul, zero_add] at hst
    apply hw0
    rw [← hρ3 w, hst, map_zero, map_zero]
  · exfalso
    simp only [one_smul, zero_smul, add_zero] at hst
    exact hw0 hst
  · exfalso
    simp only [one_smul] at hst
    have h2 : ∀ y : V, y + y = 0 := fun y => by
      rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul]
    have hρw : ρ w = w := by
      calc ρ w = ρ w + (w + w) := by rw [h2 w, add_zero]
        _ = (w + ρ w) + w := by abel
        _ = w := by rw [hst, zero_add]
    exact hw0 (hfix w hw hρw)

theorem psiOf_injective {w : V} {ρ : V ≃ₗ[ZMod 2] V}
    (hli : LinearIndependent (ZMod 2) ![w, ρ w]) : Function.Injective (psiOf w ρ) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro a ha
  rw [LinearMap.mem_ker, psiOf_apply] at ha
  have h := (LinearIndependent.pair_iff.1 hli) (Model.basisF4.repr a 0) (Model.basisF4.repr a 1) ha
  rw [Submodule.mem_bot]
  calc a = ∑ i, Model.basisF4.repr a i • Model.basisF4 i := (Model.basisF4.sum_repr a).symm
    _ = 0 := by rw [Fin.sum_univ_two, h.1, h.2]; simp

theorem psiOf_range {X : Submodule (ZMod 2) V} {ρ : V ≃ₗ[ZMod 2] V} {w : V} (hw : w ∈ X)
    (hinv : ∀ x ∈ X, ρ x ∈ X) (hfr : Module.finrank (ZMod 2) X = 2)
    (hli : LinearIndependent (ZMod 2) ![w, ρ w]) :
    LinearMap.range (psiOf w ρ) = X := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨a, rfl⟩
    rw [psiOf_apply]
    exact X.add_mem (X.smul_mem _ hw) (X.smul_mem _ (hinv w hw))
  · rw [LinearMap.finrank_range_of_inj (psiOf_injective hli), Model.finrank_F4, hfr]

theorem psiOf_compat {X : Submodule (ZMod 2) V} {ρ : V ≃ₗ[ZMod 2] V} {w : V} (hw : w ∈ X)
    (hinv : ∀ x ∈ X, ρ x ∈ X)
    (hquad : ∀ x ∈ X, ρ (ρ x) + ρ x + x = 0)
    {f : V ≃ₗ[ZMod 2] V} (hf : ∀ x ∈ X, f x = ρ x) (a : Model.F4) :
    f (psiOf w ρ a) = psiOf w ρ (Model.omega * a) := by
  have hlin : (f : V →ₗ[ZMod 2] V).comp (psiOf w ρ) =
      (psiOf w ρ).comp (LinearMap.mulLeft (ZMod 2) Model.omega) := by
    apply Module.Basis.ext Model.basisF4
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, LinearMap.comp_apply, LinearMap.coe_coe,
        LinearMap.mulLeft_apply, LinearEquiv.coe_coe]
      rw [Model.basisF4_zero, mul_one, psiOf_one, hf w hw, psiOf_omega]
    · simp only [Fin.mk_one, Fin.isValue, LinearMap.comp_apply, LinearMap.coe_coe,
        LinearMap.mulLeft_apply, LinearEquiv.coe_coe]
      rw [Model.basisF4_one, psiOf_omega, hf _ (hinv w hw)]
      have hmul : Model.omega * Model.omega = Model.omega + 1 := by rw [← sq]; exact Model.omega_sq
      rw [hmul, map_add, psiOf_omega, psiOf_one]
      have hrr : ρ (ρ w) + (ρ w + w) = 0 := by rw [← add_assoc]; exact hquad w hw
      rw [eq_neg_of_add_eq_zero_left hrr, neg_add, neg_eq_self_V, neg_eq_self_V]
  have := congrArg (fun L : Model.F4 →ₗ[ZMod 2] V => L a) hlin
  simpa using this

@[expose] noncomputable def phiOf (ψ₁ ψ₂ : Model.F4 →ₗ[ZMod 2] V) :
    (Fin 2 → Model.F4) →ₗ[ZMod 2] V :=
  ψ₁ ∘ₗ (LinearMap.proj 0) + ψ₂ ∘ₗ (LinearMap.proj 1)

theorem phiOf_apply (ψ₁ ψ₂ : Model.F4 →ₗ[ZMod 2] V) (c : Fin 2 → Model.F4) :
    phiOf ψ₁ ψ₂ c = ψ₁ (c 0) + ψ₂ (c 1) := rfl

theorem phiOf_injective {ψ₁ ψ₂ : Model.F4 →ₗ[ZMod 2] V} (h₁ : Function.Injective ψ₁)
    (h₂ : Function.Injective ψ₂)
    (hdisj : Disjoint (LinearMap.range ψ₁) (LinearMap.range ψ₂)) :
    Function.Injective (phiOf ψ₁ ψ₂) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker, phiOf_apply] at hc
  have hneg : ψ₁ (c 0) = -ψ₂ (c 1) := eq_neg_of_add_eq_zero_left hc
  have hmem : ψ₁ (c 0) ∈ LinearMap.range ψ₁ ⊓ LinearMap.range ψ₂ := by
    refine ⟨LinearMap.mem_range_self _ _, ?_⟩
    rw [hneg]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self _ _)
  rw [disjoint_iff.1 hdisj, Submodule.mem_bot] at hmem
  have hc0 : c 0 = 0 := h₁ (by rw [hmem, map_zero])
  have hc1 : c 1 = 0 := h₂ (by
    rw [map_zero]
    have : ψ₂ (c 1) = 0 := by
      have h' : ψ₁ (c 0) = 0 := hmem
      rw [h'] at hneg
      exact neg_eq_zero.1 hneg.symm
    exact this)
  rw [Submodule.mem_bot]
  funext i
  fin_cases i
  · exact hc0
  · exact hc1

theorem phiOf_range (ψ₁ ψ₂ : Model.F4 →ₗ[ZMod 2] V) :
    LinearMap.range (phiOf ψ₁ ψ₂) = LinearMap.range ψ₁ ⊔ LinearMap.range ψ₂ := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [phiOf_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      refine ⟨Pi.single 0 a, ?_⟩
      rw [phiOf_apply]
      simp
    · rintro _ ⟨a, rfl⟩
      refine ⟨Pi.single 1 a, ?_⟩
      rw [phiOf_apply]
      simp

theorem phiOf_compat {ψ₁ ψ₂ : Model.F4 →ₗ[ZMod 2] V} {f₁ : V ≃ₗ[ZMod 2] V}
    (h₁ : ∀ a, f₁ (ψ₁ a) = ψ₁ (Model.omega * a)) (h₂ : ∀ a, f₁ (ψ₂ a) = ψ₂ (Model.omega * a))
    (c : Fin 2 → Model.F4) :
    f₁ (phiOf ψ₁ ψ₂ c) = phiOf ψ₁ ψ₂ (Model.omega • c) := by
  rw [phiOf_apply, phiOf_apply, map_add, h₁, h₂]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Link

end
