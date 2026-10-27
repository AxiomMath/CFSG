module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapMat

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

@[expose] def Umat : Matrix (Fin 3) (Fin 3) (ZMod 4) := !![3, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def Dmat : Matrix (Fin 3) (Fin 3) (ZMod 4) := !![1, 0, 0; 0, 1, 0; 0, 0, 3]

theorem Umat_mulVec (a : Fin 3 → ZMod 4) : Umat *ᵥ a = MB.uvec a := by
  have h3 : (3 : ZMod 4) = -1 := by decide
  funext i
  fin_cases i <;> simp [Umat, MB.uvec, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h3]
  ring

theorem Umat_sq : Umat * Umat = 1 := by decide

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

theorem t_mem_NA : S.t ∈ A.NA := A.S₁_le_normalizer (A.ι_t ▸ A.range_ι ▸ ⟨_, rfl⟩)

theorem u_mem_NA : A.D₁.u ∈ A.NA := A.S₁_le_normalizer (A.ι_u ▸ A.range_ι ▸ ⟨_, rfl⟩)

theorem AA_le_NA : A.AA ≤ A.NA := A.AA_le_S₁.trans A.S₁_le_normalizer

theorem mat_t : A.mat ⟨S.t, A.t_mem_NA⟩ = -1 :=
  A.mat_eq_of fun a => by rw [A.t_conj_Φ, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem mat_u : A.mat ⟨A.D₁.u, A.u_mem_NA⟩ = Umat :=
  A.mat_eq_of fun a => by rw [A.u_conj_Φ, Umat_mulVec]

theorem mat_of_AA {g : X} (hg : g ∈ A.AA) : A.mat ⟨g, A.AA_le_NA hg⟩ = 1 :=
  (A.mat_eq_one_iff _).mpr (mem_centralizer_iff.mpr fun _ hh => A.AA_comm hh hg)

@[expose] def L4set : Set (Matrix (Fin 3) (Fin 3) (ZMod 4)) := {1, -1, Umat, -Umat}

theorem L4set_mul {M N : Matrix (Fin 3) (Fin 3) (ZMod 4)} (hM : M ∈ L4set) (hN : N ∈ L4set) :
    M * N ∈ L4set := by
  simp only [L4set, Set.mem_insert_iff, Set.mem_singleton_iff] at hM hN ⊢
  rcases hM with rfl | rfl | rfl | rfl <;> rcases hN with rfl | rfl | rfl | rfl <;>
    simp [Umat_sq]

@[expose] noncomputable def L4pre : Subgroup X where
  carrier := {g | ∃ h : g ∈ A.NA, A.mat ⟨g, h⟩ ∈ L4set}
  mul_mem' := by
    rintro a b ⟨ha, hma⟩ ⟨hb, hmb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [show (⟨a * b, mul_mem ha hb⟩ : A.NA) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, A.mat_mul]
    exact L4set_mul hma hmb
  one_mem' := ⟨one_mem _, by
    rw [show (⟨1, one_mem _⟩ : A.NA) = 1 from rfl, A.mat_one]; simp [L4set]⟩
  inv_mem' := by
    rintro a ⟨ha, hma⟩
    refine ⟨inv_mem ha, ?_⟩
    have h1 : A.mat ⟨a⁻¹, inv_mem ha⟩ * A.mat ⟨a, ha⟩ = 1 := by
      rw [← A.mat_mul, show (⟨a⁻¹, inv_mem ha⟩ : A.NA) * ⟨a, ha⟩ = 1 from
        Subtype.ext (inv_mul_cancel a), A.mat_one]
    have hsq : A.mat ⟨a, ha⟩ * A.mat ⟨a, ha⟩ = 1 := by
      simp only [L4set, Set.mem_insert_iff, Set.mem_singleton_iff] at hma
      rcases hma with h | h | h | h <;> rw [h] <;> simp [Umat_sq]
    have : A.mat ⟨a⁻¹, inv_mem ha⟩ = A.mat ⟨a, ha⟩ := by
      calc A.mat ⟨a⁻¹, inv_mem ha⟩ = A.mat ⟨a⁻¹, inv_mem ha⟩ * (A.mat ⟨a, ha⟩ *
            A.mat ⟨a, ha⟩) := by rw [hsq, mul_one]
        _ = A.mat ⟨a, ha⟩ := by rw [← mul_assoc, h1, one_mul]
    rw [this]; exact hma

theorem S₁_le_L4pre : A.D₁.S₁ ≤ A.L4pre := by
  rw [← A.range_ι]
  refine MB.range_le _ fun g hg => ?_
  have hA : ∀ x : MB, A.ι x ∈ A.AA → A.ι x ∈ A.L4pre := fun x hx =>
    ⟨A.AA_le_NA hx, by rw [A.mat_of_AA hx]; simp [L4set]⟩
  have ht : S.t ∈ A.L4pre := ⟨A.t_mem_NA, by rw [A.mat_t]; simp [L4set]⟩
  simp only [MB.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hA _ (A.ι_w₂ ▸ A.Φ_e1 ▸ A.Φ_mem _)
  · rw [A.ι_u]; exact ⟨A.u_mem_NA, by rw [A.mat_u]; simp [L4set]⟩
  · exact hA _ (A.ι_w₁ ▸ A.Φ_e0 ▸ A.Φ_mem _)
  ·
    have hc : S.t * A.V₁.vN ∈ A.L4pre := by
      have := hA (MB.t * MB.v) (by rw [map_mul, A.ι_t, A.ι_v, ← A.Φ_e2]; exact A.Φ_mem _)
      rwa [map_mul, A.ι_t, A.ι_v] at this
    rw [A.ι_v]
    have := mul_mem (inv_mem ht) hc
    rwa [inv_mul_cancel_left] at this
  · exact hA _ (A.ι_z ▸ A.Φ_z ▸ A.Φ_mem _)
  · exact hA _ (A.ι_y ▸ A.Φ_y ▸ A.Φ_mem _)
  · rw [A.ι_t]; exact ht
  · exact hA _ (A.ι_k ▸ A.Φ_k ▸ A.Φ_mem _)

theorem mat_S₁ {g : X} (hg : g ∈ A.D₁.S₁) (hN : g ∈ A.NA) : A.mat ⟨g, hN⟩ ∈ L4set := by
  obtain ⟨_, hm⟩ := A.S₁_le_L4pre hg
  exact hm

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
