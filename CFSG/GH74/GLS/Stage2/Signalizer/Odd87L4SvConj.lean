module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section Conj

variable {F : Type} [Field F]

@[expose] noncomputable def slConj (P : GL (Fin 4) F) : MulAut SL(4, F) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F P

theorem proj_slConj (P : GL (Fin 4) F) (g : SL(4, F)) :
    proj 4 F (slConj P g) = conjAut 4 F P (proj 4 F g) :=
  (conjAut_proj P g).symm

theorem slConj_mul_inv (P : GL (Fin 4) F) (g : SL(4, F)) : slConj P (slConj P⁻¹ g) = g := by
  have h : slConj P * slConj P⁻¹ = 1 := by
    rw [slConj, slConj, ← map_mul, mul_inv_cancel, map_one]
  exact congrArg (fun e : MulAut SL(4, F) => e g) h

theorem slConj_inv_mul (P : GL (Fin 4) F) (g : SL(4, F)) : slConj P⁻¹ (slConj P g) = g := by
  have h : slConj P⁻¹ * slConj P = 1 := by
    rw [slConj, slConj, ← map_mul, inv_mul_cancel, map_one]
  exact congrArg (fun e : MulAut SL(4, F) => e g) h

theorem conjAut_inv_apply (P : GL (Fin 4) F) (y : projectiveSL 4 F) :
    conjAut 4 F P (conjAut 4 F P⁻¹ y) = y := by
  have h : conjAut 4 F P * conjAut 4 F P⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg (fun e : MulAut (projectiveSL 4 F) => e y) h

theorem conjAut_apply_inv (P : GL (Fin 4) F) (y : projectiveSL 4 F) :
    conjAut 4 F P⁻¹ (conjAut 4 F P y) = y := by
  have h : conjAut 4 F P⁻¹ * conjAut 4 F P = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  exact congrArg (fun e : MulAut (projectiveSL 4 F) => e y) h

theorem fix_conj_iff {α α₀ : MulAut (projectiveSL 4 F)} {P : GL (Fin 4) F}
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹) (y : projectiveSL 4 F) :
    α₀ y = y ↔ α (conjAut 4 F P⁻¹ y) = conjAut 4 F P⁻¹ y := by
  have hinv : (conjAut 4 F P)⁻¹ = conjAut 4 F P⁻¹ := (map_inv _ P).symm
  have h1 : α₀ y = conjAut 4 F P (α (conjAut 4 F P⁻¹ y)) := by
    rw [hα₀, hinv]
    rfl
  rw [h1]
  constructor
  · intro h
    have := congrArg (conjAut 4 F P⁻¹) h
    rwa [conjAut_apply_inv] at this
  · intro h
    rw [h, conjAut_inv_apply]

theorem mem_fixSub_conj {α α₀ : MulAut (projectiveSL 4 F)} {P : GL (Fin 4) F}
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹) (g : SL(4, F)) :
    proj 4 F (slConj P g) ∈ fixSub α₀ ↔ proj 4 F g ∈ fixSub α := by
  rw [mem_fixSub, mem_fixSub, fix_conj_iff hα₀, proj_slConj, conjAut_apply_inv]

theorem mem_fixSub_conj_inv {α α₀ : MulAut (projectiveSL 4 F)} {P : GL (Fin 4) F}
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹) (g : SL(4, F)) :
    proj 4 F (slConj P⁻¹ g) ∈ fixSub α ↔ proj 4 F g ∈ fixSub α₀ := by
  rw [← mem_fixSub_conj hα₀, slConj_mul_inv]

theorem irred_transport {α α₀ : MulAut (projectiveSL 4 F)} (P : GL (Fin 4) F)
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹)
    (h₀ : ∀ W₀ : Submodule F (Fin 4 → F),
      (∀ A : SL(4, F), proj 4 F A ∈ fixSub α₀ → ∀ w ∈ W₀, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W₀) →
      W₀ = ⊥ ∨ W₀ = ⊤)
    (W : Submodule F (Fin 4 → F))
    (hW : ∀ A : SL(4, F), proj 4 F A ∈ fixSub α → ∀ w ∈ W,
      (A : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  set Pm : Matrix (Fin 4) (Fin 4) F := ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPm
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let W₀ : Submodule F (Fin 4 → F) := W.map (Matrix.mulVecLin Pm)
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
  have hinv : ∀ A₀ : SL(4, F), proj 4 F A₀ ∈ fixSub α₀ → ∀ w ∈ W₀,
      (A₀ : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W₀ := by
    intro A₀ hA₀ w hw
    rw [hmem] at hw ⊢
    have hA : proj 4 F (slConj P⁻¹ A₀) ∈ fixSub α := (mem_fixSub_conj_inv hα₀ A₀).2 hA₀
    have h1 := hW _ hA _ hw
    have hmat : ((slConj P⁻¹ A₀ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Pi * (A₀ : Matrix (Fin 4) (Fin 4) F) * Pm := by
      have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation P⁻¹ A₀
      simpa [slConj, hPi, hPm] using this
    rw [hmat] at h1
    have : Pi *ᵥ ((A₀ : Matrix (Fin 4) (Fin 4) F) *ᵥ w) =
        (Pi * (A₀ : Matrix (Fin 4) (Fin 4) F) * Pm) *ᵥ (Pi *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPPi,
        Matrix.mul_one]
    rw [this]
    exact h1
  rcases h₀ W₀ hinv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have : Pm *ᵥ w ∈ W₀ := ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at this
    have h2 : w = Pi *ᵥ (Pm *ᵥ w) := by rw [Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
    rw [Submodule.mem_bot, h2, this, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have : Pm *ᵥ w ∈ W₀ := by rw [h]; exact Submodule.mem_top
    rw [hmem, Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec] at this
    exact this

theorem slConj_mem_scalars (Q : GL (Fin 4) F) {z : SL(4, F)} (hz : z ∈ scalars 4 F) :
    slConj Q z ∈ scalars 4 F := by
  rw [scalars_eq_center] at hz ⊢
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have h1 := hz (slConj Q⁻¹ g)
  have h2 := congrArg (slConj Q) h1
  rw [map_mul, map_mul, slConj_mul_inv] at h2
  exact h2

theorem mem_scalars_of_slConj (P : GL (Fin 4) F) {x : SL(4, F)} (hx : slConj P x ∈ scalars 4 F) :
    x ∈ scalars 4 F := by
  have := slConj_mem_scalars P⁻¹ hx
  rwa [slConj_inv_mul] at this

theorem cent_transport_fix {α α₀ : MulAut (projectiveSL 4 F)} (P : GL (Fin 4) F)
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹)
    (h₀ : ∀ x₀ : SL(4, F), (∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α₀) →
        ∀ g, x₀ * ι g = ι g * x₀) → α₀ (proj 4 F x₀) = proj 4 F x₀)
    (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) → ∀ g, x * ι g = ι g * x) :
    α (proj 4 F x) = proj 4 F x := by
  have h1 := h₀ (slConj P x) (fun ι₀ hι₀ g => by
    have hι : ∀ g, proj 4 F ((slConj P⁻¹).toMonoidHom.comp ι₀ g) ∈ fixSub α :=
      fun g => (mem_fixSub_conj_inv hα₀ _).2 (hι₀ g)
    have h2 := congrArg (slConj P) (h _ hι g)
    simpa [map_mul, slConj_mul_inv] using h2)
  have h2 := (fix_conj_iff hα₀ _).1 h1
  rwa [proj_slConj, conjAut_apply_inv] at h2

theorem cent_transport_scalars {α α₀ : MulAut (projectiveSL 4 F)} (P : GL (Fin 4) F)
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹)
    (h₀ : ∀ x₀ : SL(4, F), (∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α₀) →
        ∀ g, x₀ * ι g = ι g * x₀) → x₀ ∈ scalars 4 F)
    (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) → ∀ g, x * ι g = ι g * x) :
    x ∈ scalars 4 F := by
  refine mem_scalars_of_slConj P (h₀ (slConj P x) (fun ι₀ hι₀ g => ?_))
  have hι : ∀ g, proj 4 F ((slConj P⁻¹).toMonoidHom.comp ι₀ g) ∈ fixSub α :=
    fun g => (mem_fixSub_conj_inv hα₀ _).2 (hι₀ g)
  have h2 := congrArg (slConj P) (h _ hι g)
  simpa [map_mul, slConj_mul_inv] using h2

theorem cent3_transport_fix {α α₀ : MulAut (projectiveSL 4 F)} (P : GL (Fin 4) F)
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹)
    (h₀ : ∀ x₀ : SL(4, F), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x₀ ^ (r ^ n) = 1) →
      (∀ a b : SL(4, F), proj 4 F a ∈ fixSub α₀ → proj 4 F b ∈ fixSub α₀ →
        x₀ * ⁅a, b⁆ = ⁅a, b⁆ * x₀) → α₀ (proj 4 F x₀) = proj 4 F x₀)
    (x : SL(4, F)) (hx : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    α (proj 4 F x) = proj 4 F x := by
  obtain ⟨r, n, hr, hr5, hxm⟩ := hx
  have h1 := h₀ (slConj P x) ⟨r, n, hr, hr5, by rw [← map_pow, hxm, map_one]⟩ (fun a₀ b₀ ha₀ hb₀ => by
    have ha : proj 4 F (slConj P⁻¹ a₀) ∈ fixSub α := (mem_fixSub_conj_inv hα₀ _).2 ha₀
    have hb : proj 4 F (slConj P⁻¹ b₀) ∈ fixSub α := (mem_fixSub_conj_inv hα₀ _).2 hb₀
    have h2 := congrArg (slConj P) (h _ _ ha hb)
    simpa [map_mul, map_inv, commutatorElement_def, slConj_mul_inv] using h2)
  have h2 := (fix_conj_iff hα₀ _).1 h1
  rwa [proj_slConj, conjAut_apply_inv] at h2

theorem cent3_transport_scalars {α α₀ : MulAut (projectiveSL 4 F)} (P : GL (Fin 4) F)
    (hα₀ : α₀ = conjAut 4 F P * α * (conjAut 4 F P)⁻¹)
    (h₀ : ∀ x₀ : SL(4, F), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x₀ ^ (r ^ n) = 1) →
      (∀ a b : SL(4, F), proj 4 F a ∈ fixSub α₀ → proj 4 F b ∈ fixSub α₀ →
        x₀ * ⁅a, b⁆ = ⁅a, b⁆ * x₀) → x₀ ∈ scalars 4 F)
    (x : SL(4, F)) (hx : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    x ∈ scalars 4 F := by
  obtain ⟨r, n, hr, hr5, hxm⟩ := hx
  refine mem_scalars_of_slConj P (h₀ (slConj P x) ⟨r, n, hr, hr5, by rw [← map_pow, hxm, map_one]⟩
    (fun a₀ b₀ ha₀ hb₀ => ?_))
  have ha : proj 4 F (slConj P⁻¹ a₀) ∈ fixSub α := (mem_fixSub_conj_inv hα₀ _).2 ha₀
  have hb : proj 4 F (slConj P⁻¹ b₀) ∈ fixSub α := (mem_fixSub_conj_inv hα₀ _).2 hb₀
  have h2 := congrArg (slConj P) (h _ _ ha hb)
  simpa [map_mul, map_inv, commutatorElement_def, slConj_mul_inv] using h2

end Conj

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
