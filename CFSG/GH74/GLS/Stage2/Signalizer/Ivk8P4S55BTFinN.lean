module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTNP

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG
open scoped commutatorElement

variable {M : Type*} [Group M]

theorem mul_self_mem_normalizer
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    {J : Subgroup M} (hJ : IsComponent J) (x : M) : x * x ∈ normalizer (J : Set M) := by
  have hcomp : ∀ b : M, IsComponent (J.map (MulAut.conj b).toMonoidHom) := fun b =>
    LocalCores.isComponent_map_mulEquiv (MulAut.conj b) hJ
  have hmap : ∀ b c : M, (J.map (MulAut.conj c).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * c)).toMonoidHom := by
    intro b c
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  by_cases h1 : J.map (MulAut.conj x).toMonoidHom = J
  · have hx := mem_normalizer_of_map_conj_eq h1
    exact Subgroup.mul_mem _ hx hx
  · by_cases h2 : J.map (MulAut.conj (x * x)).toMonoidHom = J
    · exact mem_normalizer_of_map_conj_eq h2
    · exfalso
      have h21 : J.map (MulAut.conj (x * x)).toMonoidHom ≠ J.map (MulAut.conj x).toMonoidHom := by
        intro h21
        apply h1
        have hone : J.map (MulAut.conj (1 : M)).toMonoidHom = J := by
          ext y
          simp
        have := congrArg (fun K => K.map (MulAut.conj x⁻¹).toMonoidHom) h21
        simp only [hmap] at this
        rw [show x⁻¹ * (x * x) = x by group, inv_mul_cancel, hone] at this
        exact this
      exact h3 J _ _ hJ (hcomp x) (hcomp (x * x)) (Ne.symm h1) (Ne.symm h2) (Ne.symm h21)

theorem perfect_le_normalizer
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    {J : Subgroup M} (hJ : IsComponent J) {L : Subgroup M} (hL : ⁅L, L⁆ = L) :
    L ≤ normalizer (J : Set M) := by
  rw [← hL, Subgroup.commutator_le]
  intro a _ c _
  have e : ⁅a, c⁆ = (a * a) * ((a⁻¹ * c) * (a⁻¹ * c)) * (c⁻¹ * c⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mul_self_mem_normalizer h3 hJ a)
    (mul_self_mem_normalizer h3 hJ _)) (mul_self_mem_normalizer h3 hJ _)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
