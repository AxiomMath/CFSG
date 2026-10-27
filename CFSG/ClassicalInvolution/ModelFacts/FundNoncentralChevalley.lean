module

public import CFSG.ClassicalInvolution.WeakCT.WeylSigns

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section SL2

variable {K : Type*} [Group K] {F : Type} [Field F]

theorem eq_one_or_eq_map_sq_of_mem_center {φ : SL(2, F) →* K} (hφ : Function.Injective φ) {r : K}
    (hrc : r ∈ Subgroup.center K) (hr : r ∈ φ.range) : r = 1 ∨ r = φ (wS (1 : Fˣ) * wS (1 : Fˣ)) := by
  obtain ⟨a, rfl⟩ := hr
  have ha : a ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hφ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hrc (φ b)
  rcases eq_one_or_eq_sq_of_mem_center ha with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

theorem wS_one_mul_self_eq_one (h2 : (2 : F) = 0) : wS (1 : Fˣ) * wS (1 : Fˣ) = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, wS,
    coe_sl2Upper, coe_sl2Lower, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals linear_combination (-1 : F) * h2

theorem eq_one_of_mem_center_of_param {φ : SL(2, F) →* K} (hφ : Function.Injective φ)
    (hz : (2 : F) ≠ 0 → φ (wS (1 : Fˣ) * wS (1 : Fˣ)) ∉ Subgroup.center K) {r : K}
    (hrc : r ∈ Subgroup.center K) (hr : r ∈ φ.range) : r = 1 := by
  rcases eq_one_or_eq_map_sq_of_mem_center hφ hrc hr with h | h
  · exact h
  · by_cases h2 : (2 : F) = 0
    · rw [h, wS_one_mul_self_eq_one h2, map_one]
    · exact absurd (h ▸ hrc) (hz h2)

end SL2

section Chevalley

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem weylElement_sq_not_commute (hE : Steinberg.ChevalleyExtras D F x C O) (h2 : (2 : F) ≠ 0)
    {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots)
    (hodd : Odd (∑ j, D.cartan k j * β j)) :
    ¬ Commute (Steinberg.weylElement x k 1 ^ 2) (x β 1) := by
  intro hc
  have hk : D.cartan k k = 2 := D.isFiniteType.apply_self k
  have hβ' : reflection D.cartan k β ∈ D.roots := reflection_mem_roots k hβ
  have hss : reflection D.cartan k (reflection D.cartan k β) = β := by
    have := congrArg (fun f => f β) (reflection_mul_self hk)
    simpa using this
  have h1 := weyl_conj_one hE (k := k) hβ 1
  have h3 := weyl_conj_one hE (k := k) hβ' (wsign hE k β * 1)
  rw [hss, wsign_reflection hE hβ hodd] at h3
  have hsq := wsign_mul_self hE (k := k) hβ
  have h4 : Steinberg.weylElement x k 1 * (Steinberg.weylElement x k 1 * x β 1 *
      (Steinberg.weylElement x k 1)⁻¹) * (Steinberg.weylElement x k 1)⁻¹ = x β (-1) := by
    rw [h1, h3]
    congr 1
    linear_combination (-1 : F) * hsq
  have h5 : Steinberg.weylElement x k 1 * (Steinberg.weylElement x k 1 * x β 1 *
      (Steinberg.weylElement x k 1)⁻¹) * (Steinberg.weylElement x k 1)⁻¹ = x β 1 := by
    have hc' := hc.eq
    rw [pow_two] at hc'
    calc Steinberg.weylElement x k 1 * (Steinberg.weylElement x k 1 * x β 1 *
          (Steinberg.weylElement x k 1)⁻¹) * (Steinberg.weylElement x k 1)⁻¹
        = (Steinberg.weylElement x k 1 * Steinberg.weylElement x k 1) * x β 1 *
          (Steinberg.weylElement x k 1 * Steinberg.weylElement x k 1)⁻¹ := by group
      _ = x β 1 := by rw [hc']; group
  have h6 := (hE.param _ hβ).2.2 (h4.symm.trans h5)
  apply h2
  linear_combination -h6

theorem eq_one_of_mem_center_of_mem_rankOne_chevalley
    (hE : Steinberg.ChevalleyExtras D F x C O) {k : Fin D.rank} {β : Fin D.rank → ℤ}
    (hβ : β ∈ D.roots) (hodd : Odd (∑ j, D.cartan k j * β j)) {r : K}
    (hrc : r ∈ Subgroup.center K) (hrk : r ∈ rankOne D.rootGroup k) : r = 1 := by
  obtain ⟨φ, hφ, hup, hlow⟩ := hE.rankOne k
  have hα : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Or.inl ⟨1, k, by simp⟩
  have hα' : -(Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hα
  have hrange : r ∈ φ.range := by
    refine (sup_le ?_ ?_ : rankOne D.rootGroup k ≤ φ.range) hrk
    · intro g hg
      obtain ⟨c, rfl⟩ := ((hE.param _ hα).1 g).1 hg
      exact ⟨Steinberg.sl2Upper c, hup c⟩
    · intro g hg
      obtain ⟨c, rfl⟩ := ((hE.param _ hα').1 g).1 hg
      exact ⟨Steinberg.sl2Lower c, hlow c⟩
  refine eq_one_of_mem_center_of_param hφ (fun h2 hcen => ?_) hrc hrange
  have hw : φ (wS (1 : Fˣ) * wS (1 : Fˣ)) = Steinberg.weylElement x k 1 ^ 2 := by
    rw [pow_two, map_mul, weylElement_eq_map hup hlow]
  rw [hw] at hcen
  exact weylElement_sq_not_commute hE h2 hβ hodd
    (Subgroup.mem_center_iff.mp hcen (x β 1)).symm

end Chevalley

end CFSG.ClassicalInvolution.ModelFacts
