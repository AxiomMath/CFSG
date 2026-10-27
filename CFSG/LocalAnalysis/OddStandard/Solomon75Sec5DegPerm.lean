module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DegGrp

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup Equiv.Perm.OnCycleFactors

theorem degPerm_conj_cycle_ne {α : Type*} [Fintype α] [DecidableEq α] {t σ c : Perm α} {k : ℕ}
    (ht : t * t = 1) (htk : t.support.card = 2 * k) (hσ : σ * σ = t)
    (hc : c ∈ t.cycleFactorsFinset) : σ * c * σ⁻¹ ≠ c := by
  intro h
  have h2 := AhatData.card_support_eq_two_of_mem_cycleFactorsFinset ht htk hc
  obtain ⟨x, y, hxy, rfl⟩ := Equiv.Perm.card_support_eq_two.1 h2
  have hct := (mem_cycleFactorsFinset_iff.1 hc).2
  have htx : t x = y := by
    rw [← hct x (by rw [support_swap hxy]; simp), swap_apply_left]
  have hσσ : ∀ a, σ (σ a) = t a := fun a => by rw [← hσ, Perm.mul_apply]
  have h1 : σ x ≠ x := fun h' => hxy (by have := hσσ x; rwa [h', h', htx] at this)
  have h1' : σ x ≠ y := fun h' => hxy (σ.injective (by
    have := hσσ x
    rw [h', htx] at this
    rw [h', this]))
  have h3 : swap (σ x) (σ y) (σ x) = swap x y (σ x) := by rw [swap_apply_apply, h]
  rw [swap_apply_left, swap_apply_of_ne_of_ne h1 h1'] at h3
  exact hxy (σ.injective h3.symm)

theorem exists_hom_solvable_ker {n k : ℕ} {t σ : Perm (Fin n)} (ht : t * t = 1)
    (htk : t.support.card = 2 * k) (hfix : n ≤ 2 * k + 4) (hk2 : Even k) (hσ : σ * σ = t)
    {B : Type*} [Group B] (T : B →* Perm (Fin n)) (hTt : ∀ b, T b * t = t * T b)
    (hTσ : ∀ b, T b * σ = σ * T b) (hker : Group.IsSolvable T.ker) :
    ∃ (Ξ : Type) (_ : Fintype Ξ) (_ : DecidableEq Ξ) (Θ : B →* Perm Ξ),
      Fintype.card Ξ * 2 = k ∧ Group.IsSolvable Θ.ker := by
  classical
  obtain ⟨r, hr⟩ := hk2
  have hσt : σ ∈ centralizer {t} := mem_centralizer_singleton_iff.2 (by rw [← hσ, mul_assoc])
  set π : Perm ↥t.cycleFactorsFinset := toPermHom t ⟨σ, hσt⟩ with hπ
  have hππ : π * π = 1 := by
    rw [hπ, ← map_mul]
    refine (MonoidHom.mem_ker).1 ((mem_ker_toPermHom_iff t _).2 fun c hc => ?_)
    show Commute (σ * σ) c
    rw [hσ]
    exact (self_mem_cycle_factors_commute hc).symm
  have hπfix : ∀ c, π c ≠ c := fun c h =>
    degPerm_conj_cycle_ne ht htk hσ c.2 ((coe_toPermHom t _ c).symm.trans (congrArg Subtype.val h))
  have hsupp : π.support.card = 2 * r := by
    have : π.support = Finset.univ :=
      Finset.eq_univ_of_forall fun c => Perm.mem_support.2 (hπfix c)
    rw [this, Finset.card_univ, AhatData.card_cycleFactorsFinset_of_involution ht htk]
    omega
  have hfixt : Nat.card (Function.fixedPoints t) ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, Fintype.card_fin,
      Equiv.Perm.sum_cycleType, htk]
    omega
  have hfixπ : Nat.card (Function.fixedPoints π) ≤ 4 := by
    have : IsEmpty (Function.fixedPoints π) := ⟨fun c => hπfix c.1 c.2⟩
    rw [Nat.card_of_isEmpty]
    omega
  have hT₁ : ∀ b, T b ∈ centralizer {t} := fun b => mem_centralizer_singleton_iff.2 (hTt b)
  have hT₂ : ∀ b, (toPermHom t).comp (T.codRestrict _ hT₁) b ∈ centralizer {π} := fun b =>
    mem_centralizer_singleton_iff.2
      ((show Commute (T.codRestrict _ hT₁ b) ⟨σ, hσt⟩ from Subtype.ext (hTσ b)).map
        (toPermHom t)).eq
  refine ⟨↥π.cycleFactorsFinset, inferInstance, inferInstance,
    (toPermHom π).comp (((toPermHom t).comp (T.codRestrict _ hT₁)).codRestrict _ hT₂), ?_, ?_⟩
  · rw [AhatData.card_cycleFactorsFinset_of_involution hππ hsupp]
    omega
  · refine isSolvable_ker_comp _ (toPermHom π) ?_ (solvable_ker_toPermHom π hfixπ)
    rw [MonoidHom.ker_codRestrict]
    refine isSolvable_ker_comp _ (toPermHom t) ?_ (solvable_ker_toPermHom t hfixt)
    rw [MonoidHom.ker_codRestrict]
    exact hker

end CFSG.OddStandard.Solomon75
