module

public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

theorem matrix_eq_one_of_mulVec_eq_self {F : Type*} [Field F] {M : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ v : Fin 2 → F, M.mulVec v = v) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem fix_mem_span_of_ne_one {F : Type*} [Field F] (M : Matrix.SpecialLinearGroup (Fin 2) F)
    (hM : M ≠ 1) {v₀ : Fin 2 → F} (hv₀ : v₀ ≠ 0)
    (h₀ : (M : Matrix (Fin 2) (Fin 2) F).mulVec v₀ = v₀) {v : Fin 2 → F}
    (hv : (M : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : ∃ c : F, v = c • v₀ := by
  classical
  let f : (Fin 2 → F) →ₗ[F] (Fin 2 → F) := Matrix.mulVecLin ((M : Matrix (Fin 2) (Fin 2) F) - 1)
  have hker : ∀ w, w ∈ LinearMap.ker f ↔ (M : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
    intro w
    rw [LinearMap.mem_ker]
    show ((M : Matrix (Fin 2) (Fin 2) F) - 1).mulVec w = 0 ↔ _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hrange : LinearMap.range f ≠ ⊥ := by
    intro h
    apply hM
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    refine matrix_eq_one_of_mulVec_eq_self fun w => ?_
    have h1 : f w ∈ LinearMap.range f := LinearMap.mem_range_self f w
    rw [h, Submodule.mem_bot] at h1
    have := (hker w).mp
    simp only [f, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    exact sub_eq_zero.mp h1
  have hrk : 1 ≤ Module.finrank F (LinearMap.range f) := Submodule.one_le_finrank_iff.mpr hrange
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  have hdim : Module.finrank F (Fin 2 → F) = 2 := by simp
  have hkerle : Module.finrank F (LinearMap.ker f) ≤ 1 := by omega
  have hspan : Submodule.span F {v₀} ≤ LinearMap.ker f := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (hker v₀).mpr h₀
  have hspan1 : Module.finrank F (Submodule.span F {v₀}) = 1 := finrank_span_singleton hv₀
  have heq : Submodule.span F {v₀} = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_le hspan (by omega)
  have hvmem : v ∈ Submodule.span F {v₀} := by
    rw [heq]
    exact (hker v).mpr hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvmem
  exact ⟨c, hc.symm⟩

section SLFix

variable {W : Type} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F] [CharP F 2]
  {E : Subgroup (MulAut W)}

omit [CharP F 2] in
theorem fixV_le_of_ne_one (D : SLNatData E F) (hF : 2 ≤ Nat.card F) {U : Subgroup (MulAut W)}
    (hUE : U ≤ E) (hUne : U ≠ ⊥) (hcardU : Nat.card U = Nat.card F)
    (hW : Nat.card W = Nat.card U * Nat.card (fixV U)) {x : MulAut W} (hx : x ∈ U) (hx1 : x ≠ 1)
    {w : W} (hw : x w = w) : w ∈ fixV U := by
  classical
  obtain ⟨v₀, hv₀, hline⟩ := exists_line_beta_fixV D hF hUE hUne hcardU hW
  set e : ↥E := ⟨x, hUE hx⟩ with he
  have hMne : D.θ e ≠ 1 := fun h =>
    hx1 (congrArg Subtype.val (D.θ.injective (h.trans (map_one D.θ).symm)))
  have hfixβ : ∀ w' : W, x w' = w' →
      (D.θ e : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (D.β w')) =
        Multiplicative.toAdd (D.β w') := by
    intro w' hw'
    have h1 := D.equivar' e w'
    have : (e : MulAut W) w' = w' := hw'
    rw [this] at h1
    rw [Matrix.SpecialLinearGroup.smul_def] at h1
    exact h1.symm
  obtain ⟨w₁, hw₁U, hw₁⟩ := hline 1
  have hv₁ : Multiplicative.toAdd (D.β w₁) = v₀ := by rw [hw₁]; simp
  have h₀ : (D.θ e : Matrix (Fin 2) (Fin 2) F).mulVec v₀ = v₀ := by
    rw [← hv₁]
    exact hfixβ w₁ (hw₁U x hx)
  obtain ⟨c, hc⟩ := fix_mem_span_of_ne_one (D.θ e) hMne hv₀ h₀ (hfixβ w hw)
  obtain ⟨w₂, hw₂U, hw₂⟩ := hline c
  have hβ : D.β w = D.β w₂ := by
    rw [hw₂]
    exact Multiplicative.toAdd.injective (by simpa using hc)
  have hker : w * w₂⁻¹ ∈ fixV E := D.ker_fix _ (by rw [map_mul, map_inv, hβ, mul_inv_cancel])
  have hker' : w * w₂⁻¹ ∈ fixV U := fun u hu => hker u (hUE hu)
  have hdec : w = (w * w₂⁻¹) * w₂ := by group
  rw [hdec]
  exact (fixV U).mul_mem hker' hw₂U

end SLFix

end CFSG.CGT.PushingUpLit.CGT6
