module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement

theorem specialRho_injective_of_charTwo {K : Type*} [Field K] [CharP K 2] :
    Function.Injective (specialRho (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨c, hc, h1, h2⟩ := (specialRho_eq_one_iff z).mp hz
  have hc1 : c = 1 := by
    apply Units.ext
    have hcK : (c : K) ^ 2 = 1 := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hc
    have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hzero : ((c : K) - 1) ^ 2 = 0 := by
      linear_combination hcK - ((c : K) - 1) * h2K
    exact sub_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero : (2 : ℕ) ≠ 0)).mp hzero)
  subst hc1
  rw [map_one] at h1 h2
  exact Prod.ext (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h1))
    (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h2))

theorem nonempty_commutator_orthogonalGroup_mulEquiv_specialLinear_prod {K W : Type*} [Field K]
    [Finite K] [CharP K 2] [AddCommGroup W] [Module K W] (R : QuadraticForm K W)
    (hR : R.polarBilin.Nondegenerate) (h4 : finrank K W = 4)
    (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) (hK4 : 4 ≤ Nat.card K) :
    Nonempty (↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  obtain ⟨-, e, -, -, hcomm, -⟩ :=
    (@orthogonal_low_dimensional_fixed_derived_component_coverage K W _ _ _ _
      (FiniteDimensional.of_finrank_pos (by omega)) R hR
      (Or.inr (Or.inr ⟨h4, hS⟩))).2.2.2.1 h4 hS hK2 hK3
  have hcomm' : commutator (TauCeti.QuadraticMap.orthogonalGroup R) =
      (specialImage K).map e.symm.toMonoidHom := by
    rw [hcomm, ← Subgroup.map_sup, determinantFactors_sup]
  exact ⟨(MulEquiv.subgroupCongr hcomm').trans
    ((e.symm.subgroupMap (specialImage K)).symm.trans
      (MonoidHom.ofInjective (specialRho_injective_of_charTwo (K := K))).symm)⟩

theorem commute_of_isComponentOf_of_mulEquiv_prod {G H₁ H₂ : Type*} [Group G] [Finite G]
    [Group H₁] [Group H₂] {N J : Subgroup G} (Θ : ↥N ≃* H₁ × H₂)
    (hJ : CFSG.Assembly.IsComponentOf J N) :
    (∀ g : ↥N, (Θ g).1 = 1 → ∀ j ∈ J, (g : G) * j = j * g) ∨
      (∀ g : ↥N, (Θ g).2 = 1 → ∀ j ∈ J, (g : G) * j = j * g) := by
  obtain ⟨hJN, hJs, hJq⟩ := hJ
  let F₁ : Subgroup ↥N := ((MonoidHom.snd H₁ H₂).comp Θ.toMonoidHom).ker
  have hF₁ : ∀ g : ↥N, g ∈ F₁ ↔ (Θ g).2 = 1 := fun _ => Iff.rfl
  have hJcomp : CFSG.IsComponent (J.subgroupOf N) :=
    (isComponentOf_iff_isComponent_subgroupOf hJN).mp ⟨hJN, hJs, hJq⟩
  rcases component_normal_subgroup hJcomp (show F₁.Normal from inferInstance) with hle | hbot
  · left
    intro g hg j hj
    have hjn : (⟨j, hJN hj⟩ : ↥N) ∈ J.subgroupOf N := hj
    have hjF : (Θ (⟨j, hJN hj⟩ : ↥N)).2 = 1 := (hF₁ _).mp (hle hjn)
    have hcommN : g * ⟨j, hJN hj⟩ = ⟨j, hJN hj⟩ * g := by
      apply Θ.injective
      ext <;> simp [hg, hjF]
    simpa using congrArg (fun x : ↥N => (x : G)) hcommN
  · right
    intro g hg j hj
    have hgF : g ∈ F₁ := (hF₁ g).mpr hg
    have hjn : (⟨j, hJN hj⟩ : ↥N) ∈ J.subgroupOf N := hj
    have hmem : ⁅(⟨j, hJN hj⟩ : ↥N), g⁆ ∈ ⁅J.subgroupOf N, F₁⁆ :=
      Subgroup.commutator_mem_commutator hjn hgF
    rw [hbot, Subgroup.mem_bot] at hmem
    have hcommN : (⟨j, hJN hj⟩ : ↥N) * g = g * ⟨j, hJN hj⟩ :=
      commutatorElement_eq_one_iff_mul_comm.mp hmem
    simpa using (congrArg (fun x : ↥N => (x : G)) hcommN).symm

theorem le_card_ker_of_card_eq_sq {p : ℕ} [Fact p.Prime] {T H : Type*} [CommGroup T] [Finite T]
    [Group H] (hT : Nat.card T = p ^ 2) (hexp : ∀ t : T, t ^ p = 1)
    (hH : ∀ F : Subgroup H, CFSG.Open.IsElemAbelian p F → Nat.card F ≤ p) (φ : T →* H) :
    p ≤ Nat.card φ.ker := by
  have hE : CFSG.Open.IsElemAbelian p φ.range := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [← map_pow, hexp t, map_one]
  have hle : Nat.card φ.range ≤ p := hH _ hE
  have hq : Nat.card (T ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hcard : Nat.card T = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hq]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmain : p * p ≤ p * Nat.card φ.ker := by
    calc p * p = Nat.card T := by rw [hT, pow_two]
      _ = Nat.card φ.range * Nat.card φ.ker := hcard
      _ ≤ p * Nat.card φ.ker := Nat.mul_le_mul_right _ hle
  exact Nat.le_of_mul_le_mul_left hmain hp

end CFSG.LocalAnalysis.ComponentInitial

end
