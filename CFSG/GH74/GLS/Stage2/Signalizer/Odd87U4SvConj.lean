module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section HypConj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem glAut_refl (g : GL (HypIndex 2 0) K) :
    (glAut (RingEquiv.refl K) : MulAut (GL (HypIndex 2 0) K)) g = g := by
  refine Units.ext ?_
  ext i j
  rfl

theorem hypSim_mem (P : ↥(hypUnitary h 2 0)) :
    (⟨(P : GL (HypIndex 2 0) K), RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈
      semilinearSimilitudes h 2 0 :=
  ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact P.2⟩

@[expose] noncomputable def hypSimHom : ↥(hypUnitary h 2 0) →* ↥(semilinearSimilitudes h 2 0) :=
  ((SemidirectProduct.inl : GL (HypIndex 2 0) K →* SemiGL (HypIndex 2 0) K).comp
    (hypUnitary h 2 0).subtype).codRestrict _ (fun P => hypSim_mem h P)

@[expose] noncomputable def hypPhi : ↥(hypUnitary h 2 0) →* MulAut (hypPSU h 2 0) :=
  (semilinearAutHom h (by norm_num) (by norm_num)).comp (hypSimHom h)

@[expose] noncomputable def hypConjFun (P : ↥(hypUnitary h 2 0)) (g : ↥(hypSU h 2 0)) :
    ↥(hypSU h 2 0) :=
  ⟨(P : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K) * (P : GL (HypIndex 2 0) K)⁻¹, by
    have := conj_mem_hypSU (hypSim_mem h P) g
    rwa [glAut_refl] at this⟩

theorem coe_hypConjFun (P : ↥(hypUnitary h 2 0)) (g : ↥(hypSU h 2 0)) :
    ((hypConjFun h P g : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) =
      (P : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K) * (P : GL (HypIndex 2 0) K)⁻¹ :=
  rfl

theorem hypConjFun_inv_conj (P : ↥(hypUnitary h 2 0)) (g : ↥(hypSU h 2 0)) :
    hypConjFun h P⁻¹ (hypConjFun h P g) = g := by
  refine Subtype.ext ?_
  rw [coe_hypConjFun, coe_hypConjFun, Subgroup.coe_inv, inv_inv]
  group

theorem hypConjFun_conj_inv (P : ↥(hypUnitary h 2 0)) (g : ↥(hypSU h 2 0)) :
    hypConjFun h P (hypConjFun h P⁻¹ g) = g := by
  refine Subtype.ext ?_
  rw [coe_hypConjFun, coe_hypConjFun, Subgroup.coe_inv, inv_inv]
  group

@[expose] noncomputable def hypConj : ↥(hypUnitary h 2 0) →* MulAut ↥(hypSU h 2 0) where
  toFun P :=
    { toFun := hypConjFun h P
      invFun := hypConjFun h P⁻¹
      left_inv := fun g => hypConjFun_inv_conj h P g
      right_inv := fun g => hypConjFun_conj_inv h P g
      map_mul' := fun a b => by
        refine Subtype.ext ?_
        rw [coe_hypConjFun, Subgroup.coe_mul, Subgroup.coe_mul, coe_hypConjFun, coe_hypConjFun]
        group }
  map_one' := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.one_apply]
    change ((1 : ↥(hypUnitary h 2 0)) : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K) *
      ((1 : ↥(hypUnitary h 2 0)) : GL (HypIndex 2 0) K)⁻¹ = g
    rw [Subgroup.coe_one, inv_one, one_mul, mul_one]
  map_mul' P Q := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [MulAut.mul_apply]
    change (((P * Q : ↥(hypUnitary h 2 0)) : GL (HypIndex 2 0) K)) * (g : GL (HypIndex 2 0) K) *
      ((P * Q : ↥(hypUnitary h 2 0)) : GL (HypIndex 2 0) K)⁻¹ =
        (P : GL (HypIndex 2 0) K) * ((Q : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K) *
          (Q : GL (HypIndex 2 0) K)⁻¹) * (P : GL (HypIndex 2 0) K)⁻¹
    rw [Subgroup.coe_mul]
    group

theorem coe_hypConj (P : ↥(hypUnitary h 2 0)) (g : ↥(hypSU h 2 0)) :
    ((hypConj h P g : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) =
      (P : GL (HypIndex 2 0) K) * (g : GL (HypIndex 2 0) K) * (P : GL (HypIndex 2 0) K)⁻¹ :=
  rfl

theorem hypConj_conj_inv (P : ↥(hypUnitary h 2 0)) (g : ↥(hypSU h 2 0)) :
    hypConj h P (hypConj h P⁻¹ g) = g :=
  hypConjFun_conj_inv h P g

theorem hypProj_hypConj (P : ↥(hypUnitary h 2 0)) (g : ↥(hypSU h 2 0)) :
    hypProj h 2 0 (hypConj h P g) = hypPhi h P (hypProj h 2 0 g) := by
  change hypProj h 2 0 (hypConj h P g) =
    semilinearAutHom h (by norm_num) (by norm_num) (hypSimHom h P) (hypProj h 2 0 g)
  rw [semilinearAutHom_apply]
  congr 1

theorem fixed_conj_iff {Y : Type*} [Group Y] {α α₀ φ : MulAut Y}
    (hα₀ : α₀ = φ * α * φ⁻¹) (y : Y) : α₀ y = y ↔ α (φ⁻¹ y) = φ⁻¹ y := by
  have h1 : α₀ y = φ (α (φ⁻¹ y)) := by rw [hα₀]; rfl
  rw [h1]
  constructor
  · intro hy
    have := congrArg (fun z => φ⁻¹ z) hy
    simpa [MulAut.inv_apply_self] using this
  · intro hy
    rw [hy, MulAut.apply_inv_self]

theorem mem_fixSub_hypConj {α α₀ : MulAut (hypPSU h 2 0)} {P : ↥(hypUnitary h 2 0)}
    (hα₀ : α₀ = hypPhi h P * α * (hypPhi h P)⁻¹) (g : ↥(hypSU h 2 0)) :
    hypProj h 2 0 (hypConj h P g) ∈ fixSub α₀ ↔ hypProj h 2 0 g ∈ fixSub α := by
  rw [mem_fixSub, mem_fixSub, fixed_conj_iff hα₀, hypProj_hypConj, MulAut.inv_apply_self]

theorem mem_fixSub_hypConj_inv {α α₀ : MulAut (hypPSU h 2 0)} {P : ↥(hypUnitary h 2 0)}
    (hα₀ : α₀ = hypPhi h P * α * (hypPhi h P)⁻¹) (g : ↥(hypSU h 2 0)) :
    hypProj h 2 0 (hypConj h P⁻¹ g) ∈ fixSub α ↔ hypProj h 2 0 g ∈ fixSub α₀ := by
  rw [← mem_fixSub_hypConj h hα₀, hypConj_conj_inv]

theorem hyp_irred_transport {α α₀ : MulAut (hypPSU h 2 0)} (P : ↥(hypUnitary h 2 0))
    (hα₀ : α₀ = hypPhi h P * α * (hypPhi h P)⁻¹)
    (h₀ : ∀ W₀ : Submodule K (HypIndex 2 0 → K),
      (∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α₀ → ∀ w ∈ W₀,
        ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W₀) →
      W₀ = ⊥ ∨ W₀ = ⊤)
    (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  set Pm : Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
    ((P : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) with hPm
  set Pi : Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
    (((P : GL (HypIndex 2 0) K)⁻¹ : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let W₀ : Submodule K (HypIndex 2 0 → K) := W.map (Matrix.mulVecLin Pm)
  have hmem : ∀ v, v ∈ W₀ ↔ Pi *ᵥ v ∈ W := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      show Pi *ᵥ (Pm *ᵥ w) ∈ W
      rw [Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
      exact hw
    · intro hv
      refine ⟨Pi *ᵥ v, hv, ?_⟩
      show Pm *ᵥ (Pi *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hPPi, Matrix.one_mulVec]
  have hinv : ∀ A₀ : ↥(hypSU h 2 0), hypProj h 2 0 A₀ ∈ fixSub α₀ → ∀ w ∈ W₀,
      ((A₀ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W₀ := by
    intro A₀ hA₀ w hw
    rw [hmem] at hw ⊢
    have hA : hypProj h 2 0 (hypConj h P⁻¹ A₀) ∈ fixSub α :=
      (mem_fixSub_hypConj_inv h hα₀ A₀).2 hA₀
    have h1 := hW _ hA _ hw
    have hmat : (((hypConj h P⁻¹ A₀ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        Pi * ((A₀ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * Pm := by
      rw [coe_hypConj, Subgroup.coe_inv, inv_inv, Units.val_mul, Units.val_mul]
    rw [hmat] at h1
    have : Pi *ᵥ (((A₀ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w) =
        (Pi * ((A₀ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * Pm) *ᵥ
          (Pi *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPPi,
        Matrix.mul_one]
    rw [this]
    exact h1
  rcases h₀ W₀ hinv with h2 | h2
  · left
    rw [eq_bot_iff]
    intro w hw
    have : Pm *ᵥ w ∈ W₀ := ⟨w, hw, rfl⟩
    rw [h2, Submodule.mem_bot] at this
    have h3 : w = Pi *ᵥ (Pm *ᵥ w) := by rw [Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
    rw [Submodule.mem_bot, h3, this, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have : Pm *ᵥ w ∈ W₀ := by rw [h2]; exact Submodule.mem_top
    rw [hmem, Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec] at this
    exact this

theorem hyp_cent_transport_fix {H : Type} [Group H] {α α₀ : MulAut (hypPSU h 2 0)}
    (P : ↥(hypUnitary h 2 0)) (hα₀ : α₀ = hypPhi h P * α * (hypPhi h P)⁻¹)
    (h₀ : ∀ x₀ : ↥(hypSU h 2 0),
      (∀ ι : H →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α₀) →
        ∀ g, x₀ * ι g = ι g * x₀) → α₀ (hypProj h 2 0 x₀) = hypProj h 2 0 x₀)
    (x : ↥(hypSU h 2 0))
    (hx : ∀ ι : H →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
      ∀ g, x * ι g = ι g * x) :
    α (hypProj h 2 0 x) = hypProj h 2 0 x := by
  have h1 := h₀ (hypConj h P x) (fun ι₀ hι₀ g => by
    have hι : ∀ g, hypProj h 2 0 (((hypConj h P⁻¹).toMonoidHom.comp ι₀) g) ∈ fixSub α :=
      fun g => (mem_fixSub_hypConj_inv h hα₀ _).2 (hι₀ g)
    have h2 := congrArg (hypConj h P) (hx _ hι g)
    simpa [map_mul, hypConj_conj_inv] using h2)
  have h2 := (fixed_conj_iff hα₀ _).1 h1
  rwa [hypProj_hypConj, MulAut.inv_apply_self] at h2

theorem hyp_cent3_transport_fix {α α₀ : MulAut (hypPSU h 2 0)} (P : ↥(hypUnitary h 2 0))
    (hα₀ : α₀ = hypPhi h P * α * (hypPhi h P)⁻¹)
    (h₀ : ∀ x₀ : ↥(hypSU h 2 0), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x₀ ^ (r ^ n) = 1) →
      (∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α₀ → hypProj h 2 0 b ∈ fixSub α₀ →
        x₀ * ⁅a, b⁆ = ⁅a, b⁆ * x₀) → α₀ (hypProj h 2 0 x₀) = hypProj h 2 0 x₀)
    (x : ↥(hypSU h 2 0)) (hx : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (hc : ∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α → hypProj h 2 0 b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    α (hypProj h 2 0 x) = hypProj h 2 0 x := by
  obtain ⟨r, n, hr, hr5, hxm⟩ := hx
  have h1 := h₀ (hypConj h P x) ⟨r, n, hr, hr5, by rw [← map_pow, hxm, map_one]⟩
    (fun a₀ b₀ ha₀ hb₀ => by
      have ha : hypProj h 2 0 (hypConj h P⁻¹ a₀) ∈ fixSub α :=
        (mem_fixSub_hypConj_inv h hα₀ _).2 ha₀
      have hb : hypProj h 2 0 (hypConj h P⁻¹ b₀) ∈ fixSub α :=
        (mem_fixSub_hypConj_inv h hα₀ _).2 hb₀
      have h2 := congrArg (hypConj h P) (hc _ _ ha hb)
      simpa [map_mul, map_inv, commutatorElement_def, hypConj_conj_inv] using h2)
  have h2 := (fixed_conj_iff hα₀ _).1 h1
  rwa [hypProj_hypConj, MulAut.inv_apply_self] at h2

end HypConj

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
