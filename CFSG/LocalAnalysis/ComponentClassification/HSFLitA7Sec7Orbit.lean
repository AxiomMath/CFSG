module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Q1

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_conj_map (H : Subgroup X) (a b : X) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite X] in
theorem mem_map_conj {H : Subgroup X} {a x : X} :
    x ∈ H.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨a⁻¹ * x * a, h, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite X] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup X} {n : X}
    (hn : n ∈ normalizer (H : Set X)) : H.map (MulAut.conj n).toMonoidHom = H := by
  ext x
  rw [mem_map_conj]
  have := mem_normalizer_iff.mp (inv_mem hn) x
  rw [inv_inv] at this
  exact this.symm

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem S₁_le_normalizer_Q₁ : C.D₁.S₁ ≤ normalizer (C.D₁.Q₁ : Set X) := by
  intro s hs
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨q, hq, rfl⟩
  have hq' := hq
  rw [C.D₁.Q₁_eq] at hq'
  show s * q * s⁻¹ ∈ C.D₁.Q₁
  rw [C.D₁.Q₁_eq]
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hs (Subgroup.mem_inf.mp hq').1) (inv_mem hs),
    conj_mem_oddTwoCoreIn (C.D₁.S₁_le hs) (Subgroup.mem_inf.mp hq').2⟩

theorem Q₁_le_S₁ : C.D₁.Q₁ ≤ C.D₁.S₁ := by rw [C.D₁.Q₁_eq]; exact inf_le_left

theorem u_mem_S₁ : C.D₁.u ∈ C.D₁.S₁ := by rw [C.D₁.S₁_eq]; exact mem_sup_right (mem_zpowers _)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
