module

public import CFSG.ClassicalInvolution.Asc77.AscT7MJ

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.Dichotomy
open scoped commutatorElement

theorem e_conj {E : Type*} [Group E] {Y : Type*} [Group Y] (e : E →* Y) (g₁ g₂ : E) :
    e g₁ * e g₂ * (e g₁)⁻¹ = e (g₁ * g₂ * g₁⁻¹) := by
  rw [map_mul, map_mul, map_inv]

variable {X : Type} [Group X] [Finite X]

theorem alphaOf_klein_outer_of_oddCore (L : Subgroup X) [L.Normal] {z y : X} (hz2 : z * z = 1)
    (hy2 : y * y = 1) (hzy : z * y = y * z) (hz1 : z ≠ 1) (hy1 : y ≠ 1) (hzy1 : z * y ≠ 1)
    {P₁ P₂ : Subgroup X}
    (d₁ : LayerData L (Subgroup.closure ({z, y} : Set X)) y P₁)
    (d₂ : LayerData L (Subgroup.closure ({z, y} : Set X)) (z * y) P₂)
    (hz : ∀ n ∈ involutionOddCore z, n = 1) :
    alphaOf (Subgroup.closure ({z, y} : Set X)) = ⊥ := by
  classical
  set B : Subgroup X := Subgroup.closure ({z, y} : Set X) with hB
  have hBmem := fun {b : X} (hb : b ∈ B) => klein_mem_closure hz2 hy2 hzy hb
  have hzB : z ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyB : y ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzyB : z * y ∈ B := B.mul_mem hzB hyB
  have hcover : ∀ {a : X} {P : Subgroup X}, B ≤ Subgroup.zpowers a ⊔ P →
      ∀ n : X, n * a = a * n → (∀ p ∈ P, n * p = p * n) → ∀ b ∈ B, n * b = b * n := by
    intro a P hBP n hna hnP b hb
    have hle : Subgroup.zpowers a ⊔ P ≤ Subgroup.centralizer ({n} : Set X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y' hy'
        rw [Set.mem_singleton_iff] at hy'
        subst hy'
        exact hna
      · intro p hp
        rw [Subgroup.mem_centralizer_iff]
        intro y' hy'
        rw [Set.mem_singleton_iff] at hy'
        subst hy'
        exact hnP p hp
    have := hle (hBP hb)
    rw [Subgroup.mem_centralizer_iff] at this
    exact this n rfl
  have hcent_y : ∀ n ∈ involutionOddCore y, ∀ b ∈ B, n * b = b * n := fun n hn =>
    hcover d₁.cover n (Subgroup.mem_centralizer_singleton_iff.mp
      (involutionOddCore_le_centralizer' y hn))
      (fun p hp => d₁.commutes_of_oddCore hn hp)
  have hcent_zy : ∀ n ∈ involutionOddCore (z * y), ∀ b ∈ B, n * b = b * n := fun n hn =>
    hcover d₂.cover n (Subgroup.mem_centralizer_singleton_iff.mp
      (involutionOddCore_le_centralizer' (z * y) hn))
      (fun p hp => d₂.commutes_of_oddCore hn hp)
  have hcent_z : ∀ n ∈ involutionOddCore z, ∀ b ∈ B, n * b = b * n := fun n hn b _ => by
    rw [hz n hn, one_mul, mul_one]
  refine (alphaOf_eq_bot_iff B).mpr ⟨?_, ?_⟩
  · intro a ha ha1
    rcases hBmem ha with rfl | rfl | rfl | rfl
    · exact absurd rfl ha1
    · exact commutator_eq_bot_of_comm fun g hg b hb => hcent_z g hg b hb
    · exact commutator_eq_bot_of_comm fun g hg b hb => hcent_y g hg b hb
    · exact commutator_eq_bot_of_comm fun g hg b hb => hcent_zy g hg b hb
  · refine eq_bot_iff.mpr fun x hx => ?_
    rw [Subgroup.mem_bot]
    have hxz : x ∈ involutionOddCore z := by
      have := Subgroup.mem_iInf.mp hx z
      have := Subgroup.mem_iInf.mp this hzB
      exact (Subgroup.mem_iInf.mp this hz1)
    exact hz x hxz

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
