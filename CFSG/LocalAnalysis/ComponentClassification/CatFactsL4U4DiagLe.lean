module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
open scoped commutatorElement

section Abstract

variable {M : Type*} [Group M] {G A : Subgroup M}

theorem pow_commutator_eq_one (hn : ∀ g ∈ G, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {m : ℕ} {z : M} (hz : ∀ g ∈ G, g * z = z * g)
    (hpow : ∀ a ∈ A, a ^ m = 1 ∨ a ^ m = z)
    (hidx : ∀ g ∈ G, ∀ h ∈ G, g ∉ A → h ∉ A → g⁻¹ * h ∈ A) :
    ∀ g ∈ G, ∀ h ∈ G, ⁅g, h⁆ ^ m = 1 := by
  have key : ∀ a ∈ A, ∀ h ∈ G, ⁅a, h⁆ ^ m = 1 := by
    intro a ha h hh
    have h1 : h * a⁻¹ * h⁻¹ ∈ A := hn h hh _ (inv_mem ha)
    have h2 : ⁅a, h⁆ = a * (h * a⁻¹ * h⁻¹) := by rw [commutatorElement_def]; group
    have hc : Commute a (h * a⁻¹ * h⁻¹) := hcomm _ ha _ h1
    rw [h2, hc.mul_pow, conj_pow, inv_pow]
    rcases hpow a ha with h4 | h4
    · rw [h4]; group
    · rw [h4]
      have hz' : Commute h z⁻¹ := (show Commute h z from hz h hh).inv_right
      rw [hz'.eq, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel]
  have key' : ∀ a ∈ A, ∀ h ∈ G, ⁅h, a⁆ ^ m = 1 := by
    intro a ha h hh
    rw [← commutatorElement_inv, inv_pow, key a ha h hh, inv_one]
  intro g hg h hh
  by_cases hgA : g ∈ A
  · exact key g hgA h hh
  by_cases hhA : h ∈ A
  · exact key' h hhA g hg
  have ha := hidx g hg h hh hgA hhA
  have h1 : ⁅g, h⁆ = g * ⁅g, g⁻¹ * h⁆ * g⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]; group
  rw [h1, conj_pow, key' _ ha g hg, mul_one, mul_inv_cancel]

theorem not_mem_commutator_of_pow (hn : ∀ g ∈ G, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {m : ℕ} {z : M} (hz : ∀ g ∈ G, g * z = z * g)
    (hpow : ∀ a ∈ A, a ^ m = 1 ∨ a ^ m = z)
    (hidx : ∀ g ∈ G, ∀ h ∈ G, g ∉ A → h ∉ A → g⁻¹ * h ∈ A)
    (hcA : ∀ g ∈ G, ∀ h ∈ G, ⁅g, h⁆ ∈ A) (hzm : z ^ m ≠ 1) : z ∉ ⁅G, G⁆ := by
  let T : Subgroup M :=
    { carrier := {x | x ∈ A ∧ x ^ m = 1}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [(show Commute x y from hcomm x hx.1 y hy.1).mul_pow, hx.2, hy.2, mul_one]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hT : ⁅G, G⁆ ≤ T := Subgroup.commutator_le.2 fun g hg h hh =>
    ⟨hcA g hg h hh, pow_commutator_eq_one hn hcomm hz hpow hidx g hg h hh⟩
  exact fun hzG => hzm (hT hzG).2

theorem sq_eq_one_of_pow_two_pow (h4 : ∀ a ∈ A, a ^ 4 = 1 → a ^ 2 = 1) :
    ∀ k : ℕ, ∀ a ∈ A, a ^ (2 ^ k) = 1 → a ^ 2 = 1 := by
  intro k
  induction k with
  | zero => intro a _ h; rw [pow_zero, pow_one] at h; rw [h, one_pow]
  | succ k ih =>
    intro a ha h
    rcases k with _ | k
    · simpa using h
    · apply ih a ha
      have h1 : (a ^ 2 ^ k) ^ 4 = 1 := by
        rw [← pow_mul, show 2 ^ k * 4 = 2 ^ (k + 1 + 1) by ring]; exact h
      have h2 := h4 _ (pow_mem ha _) h1
      rw [← pow_mul] at h2
      rwa [show 2 ^ (k + 1) = 2 ^ k * 2 by ring]

end Abstract

variable {F : Type} [Field F]

variable (F) in
@[expose] noncomputable def CA {l : F} (hl : l ≠ 0) : Subgroup (MulAut (projectiveSL 4 F)) where
  carrier := {g | ∀ x ∈ JK F hl, g x = x}
  mul_mem' := fun {a b} ha hb x hx => by rw [MulAut.mul_apply, hb x hx, ha x hx]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha x hx => by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact (ha x hx).symm

theorem coe_eq_of_proj_eq_of_trace (h4 : (4 : F) ≠ 0) {X u : SpecialLinearGroup (Fin 4) F}
    (h : proj 4 F X = proj 4 F u) (hX : (X : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (hu : (u : Matrix (Fin 4) (Fin 4) F).trace = 4) :
    (X : Matrix (Fin 4) (Fin 4) F) = u := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  have h1 : (u : Matrix (Fin 4) (Fin 4) F) = (c : F) • (X : Matrix (Fin 4) (Fin 4) F) := by
    have e : u = X * (X⁻¹ * u) := by group
    rw [e, Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have h2 : (c : F) = 1 := by
    have e := congrArg Matrix.trace h1
    rw [Matrix.trace_smul, hu, hX, smul_eq_mul] at e
    have e' : ((c : F) - 1) * 4 = 0 := by linear_combination -e
    exact sub_eq_zero.1 ((mul_eq_zero.1 e').resolve_right h4)
  rw [h1, h2, one_smul]

theorem mul_map_eq_of_fix (h4 : (4 : F) ≠ 0) (B : GL (Fin 4) F) (σ : F ≃+* F)
    (u : SpecialLinearGroup (Fin 4) F) (hu : (u : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (hσu : ((u : Matrix (Fin 4) (Fin 4) F).map σ).trace = 4)
    (h : (conjAut 4 F B * fieldAut 4 F σ) (proj 4 F u) = proj 4 F u) :
    (B : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F).map σ = u * B := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h
  have hBB : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : ((CatalogueBHigherLinearAction.slConjugation 4 F B
      (SpecialLinearGroup.map σ.toRingHom u) : SpecialLinearGroup (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F).trace = 4 := by
    rw [coe_slConjugation, Matrix.trace_mul_cycle, hBB, Matrix.one_mul,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    exact hσu
  have e := coe_eq_of_proj_eq_of_trace h4 h htr hu
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at e
  calc (B : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F).map σ =
      (B : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F).map σ.toRingHom *
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B := by
          rw [Matrix.mul_assoc _ _ (B : Matrix (Fin 4) (Fin 4) F), hBB, Matrix.mul_one]; rfl
    _ = u * B := by rw [e]

theorem trace_map_uK (σ : F ≃+* F) (l a b : F) : ((uK l a b).map σ).trace = 4 := by
  simp only [uK, Matrix.trace, Fin.sum_univ_four, Matrix.diag_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, map_one]
  norm_num

theorem trace_map_lK (σ : F ≃+* F) (l a b : F) : ((lK l a b).map σ).trace = 4 := by
  simp only [lK, Matrix.trace, Fin.sum_univ_four, Matrix.diag_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, map_one]
  norm_num

theorem trace_uK (l a b : F) : (uK l a b).trace = 4 := by
  simpa using trace_map_uK (RingEquiv.refl F) l a b

theorem trace_lK (l a b : F) : (lK l a b).trace = 4 := by
  simpa using trace_map_lK (RingEquiv.refl F) l a b

theorem eq_of_mem_CA (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1) (B : GL (Fin 4) F)
    (σ : F ≃+* F) (hg : conjAut 4 F B * fieldAut 4 F σ ∈ CA F hl) :
    (∀ c, σ c = c) ∧ (B : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) 0 0 • 1 + (B : Matrix (Fin 4) (Fin 4) F) 1 0 • kZero l := by
  have hU : ∀ a b : F, (B : Matrix (Fin 4) (Fin 4) F) * (uK l a b).map σ = uK l a b * B :=
    fun a b => mul_map_eq_of_fix h4 B σ (slUK l a b) (trace_uK l a b) (trace_map_uK σ l a b)
      (hg _ ⟨_, slUK_mem_SK hl hl1 a b, rfl⟩)
  have hL : ∀ a b : F, (B : Matrix (Fin 4) (Fin 4) F) * (lK l a b).map σ = lK l a b * B :=
    fun a b => mul_map_eq_of_fix h4 B σ (slLK l a b) (trace_lK l a b) (trace_map_lK σ l a b)
      (hg _ ⟨_, slLK_mem_SK hl hl1 a b, rfl⟩)
  exact eq_of_semilinear_comm_uK hl ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit)
    (σ : F →+* F) (hU 1 0) (hL 1 0) (hU 0 1) (fun c => hU c 0)

theorem mem_range_of_mem_CA (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    {g : MulAut (projectiveSL 4 F)} (hg : g ∈ CA F hl) (hgE : g ∈ semilinearAutGroup 4 F) :
    g ∈ (conjAut 4 F).range := by
  obtain ⟨B, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hgE
  obtain ⟨hσ, -⟩ := eq_of_mem_CA h4 hl hl1 B σ hg
  have h1 : σ = 1 := RingEquiv.ext hσ
  exact ⟨B, by rw [h1, map_one, mul_one]⟩

variable [Finite F]

theorem mem_or_exists_mul_dualAut (g : MulAut (projectiveSL 4 F)) :
    g ∈ semilinearAutGroup 4 F ∨ ∃ e ∈ semilinearAutGroup 4 F, g = e * dualAut 4 F := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen g
  have he : conjAut 4 F A * fieldAut 4 F σ ∈ semilinearAutGroup 4 F :=
    mem_semilinearAutGroup_iff.2 ⟨A, σ, rfl⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · left
    rwa [pow_zero, mul_one]
  · right
    exact ⟨_, he, by rw [pow_one]⟩

theorem inv_mul_mem_of_not_mem (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    {g h : MulAut (projectiveSL 4 F)} (hg : g ∈ CA F hl) (hh : h ∈ CA F hl)
    (hgA : g ∉ (conjAut 4 F).range) (hhA : h ∉ (conjAut 4 F).range) :
    g⁻¹ * h ∈ (conjAut 4 F).range := by
  obtain ⟨-, -, -, hδδ, -, -, -⟩ := standard_automorphism_transport (K := F) (n := 4)
  have hδinv : (dualAut 4 F)⁻¹ = dualAut 4 F := inv_eq_of_mul_eq_one_right hδδ
  have hgh : g⁻¹ * h ∈ CA F hl := mul_mem (inv_mem hg) hh
  apply mem_range_of_mem_CA h4 hl hl1 hgh
  rcases mem_or_exists_mul_dualAut g with hgE | ⟨e₁, he₁, rfl⟩
  · exact absurd (mem_range_of_mem_CA h4 hl hl1 hg hgE) hgA
  rcases mem_or_exists_mul_dualAut h with hhE | ⟨e₂, he₂, rfl⟩
  · exact absurd (mem_range_of_mem_CA h4 hl hl1 hh hhE) hhA
  have e : (e₁ * dualAut 4 F)⁻¹ * (e₂ * dualAut 4 F) =
      dualAut 4 F * (e₁⁻¹ * e₂) * dualAut 4 F := by
    rw [_root_.mul_inv_rev, hδinv]; group
  rw [e]
  exact dualAut_mul_mul_dualAut_mem (mul_mem (inv_mem he₁) he₂)

end DiagL

end CFSG.ComponentClassification.CatFactsL4U4
