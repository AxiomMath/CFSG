module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32c

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem SCert.SE.invRep_zero : SE.invRep 0 = SE.gen 0 := by decide

theorem SCert.SE.invRepCent_le_of_ne_zero : ∀ i : Fin 9, i ≠ 0 → SE.invRepCent i ≤ 256 := by
  decide

theorem SCert.SE.invRepCent_le_of_two_le : ∀ i : Fin 9, i ≠ 0 → i ≠ 1 → SE.invRepCent i ≤ 128 := by
  decide

theorem SCert.SE.invRepCent_le_of_three_le : ∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 2 →
    SE.invRepCent i ≤ 64 := by
  decide

namespace GHSylow

variable (D : GHSylow G)

theorem isSylowOf_of_classes {u : G}
    (hu : u ∈ (D.S : Subgroup G)) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hb : ∀ i : Fin 9, (∃ g : G, g⁻¹ * u * g = D.toG (SE.invRep i)) →
      SE.invRepCent i ≤ Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({u} : Set G))) :
    IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G)) := by
  refine isSylowOf_of_card_le (isSylowOf_top D.S) hu fun g hg => ?_
  have h2 : g⁻¹ * u * g * (g⁻¹ * u * g) = 1 := by
    rw [show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu2]; group
  have h1 : g⁻¹ * u * g ≠ 1 := fun h => hu1 (by
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨i, c, hcS, hc⟩ := D.exists_conj_invRep_G hg h2 h1
  rw [← D.card_inf_centralizer_conj hcS, hc, D.card_centralizer_invRep_G]
  exact hb i ⟨g * c, by rw [← hc]; group⟩

omit [Finite G] in
theorem card_Ct : Nat.card D.Ct = 256 := by
  have h := D.card_centralizer_invRep_G 1
  rw [show SE.invRepCent 1 = 256 from rfl] at h
  exact h

omit [Finite G] in
theorem card_X : Nat.card D.X = 64 := by
  have h := D.card_centralizer_invRep_G 5
  rw [show SE.invRepCent 5 = 64 from rfl] at h
  exact h

theorem isSylowOf_t_of_not_conj_z
    (htz : ¬ ∃ g : G, g⁻¹ * D.t * g = D.z) :
    IsSylowOf 2 D.Ct (centralizer ({D.t} : Set G)) := by
  refine D.isSylowOf_of_classes D.t_mem_S D.t_mul_t D.t_ne_one fun i hi' => ?_
  rw [D.card_Ct]
  by_cases hi : i = 0
  · subst hi
    rw [SE.invRep_zero] at hi'
    exact absurd hi' htz
  · exact SE.invRepCent_le_of_ne_zero i hi

theorem not_conj_x_t :
    ¬ ∃ g : G, g⁻¹ * D.x * g = D.t := by
  rintro ⟨g, hg⟩
  have hxz := D.not_conj_x_z
  have ht : IsSylowOf 2 D.Ct (centralizer ({D.t} : Set G)) :=
    D.isSylowOf_t_of_not_conj_z fun ⟨h, hh⟩ => hxz ⟨g * h, by
      rw [show (g * h)⁻¹ * D.x * (g * h) = h⁻¹ * (g⁻¹ * D.x * g) * h by group, hg, hh]⟩
  obtain ⟨g₁, hg₁, hX⟩ := exists_conj_extremal D.S.isPGroup' ht
    (show g⁻¹⁻¹ * D.t * g⁻¹ = D.x by rw [← hg]; group)
  set w := g₁⁻¹ * D.z * g₁ with hw
  have hw4 : w = (g₁⁻¹ * D.ay * g₁) ^ 4 := by rw [conj_pow_inv, D.ay_pow_four]
  have hw1 : w ≠ 1 := fun h => D.z_ne_one (by
    calc D.z = g₁ * w * g₁⁻¹ := by rw [hw]; group
      _ = 1 := by rw [h]; group)
  have hwt : w ≠ D.t := fun h => D.x_ne_z (by
    calc D.x = g₁ * (g₁⁻¹ * D.x * g₁) * g₁⁻¹ := by group
      _ = g₁ * w * g₁⁻¹ := by rw [hg₁, h]
      _ = D.z := by rw [hw]; group)
  have hwtz : w ≠ D.t * D.z := by
    intro h
    apply hxz
    refine ⟨D.toG (SE.gen 2) * g₁, ?_⟩
    have hxz' : (D.toG (SE.gen 2))⁻¹ * D.x * D.toG (SE.gen 2) = D.x * D.z := by
      rw [← map_inv, ← map_mul, ← map_mul, SE.conj_x_xz, map_mul]
    rw [show (D.toG (SE.gen 2) * g₁)⁻¹ * D.x * (D.toG (SE.gen 2) * g₁) =
        g₁⁻¹ * ((D.toG (SE.gen 2))⁻¹ * D.x * D.toG (SE.gen 2)) * g₁ by group, hxz',
      show g₁⁻¹ * (D.x * D.z) * g₁ = (g₁⁻¹ * D.x * g₁) * w by rw [hw]; group, hg₁, h,
      ← mul_assoc, D.t_mul_t, one_mul]
  rcases D.pow_four_cases_S (mem_inf.mp (hX _ D.ay_mem_X)).1 with h | h | h | h <;>
    rw [← hw4] at h
  · exact hw1 h
  · exact D.false_of_conj_X_Ct (h := g₁) (fun c hc => hX c hc) h
  · exact hwt h
  · exact hwtz h

end GHSylow

end CFSG.ComponentClassification.GHarris
