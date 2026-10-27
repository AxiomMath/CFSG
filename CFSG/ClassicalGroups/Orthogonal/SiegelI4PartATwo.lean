module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolTwo
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Order

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {F : Type} [Field F] [Finite F] [CharP F 2]
  {N : Type*} [AddCommGroup N] [Module F N] {BN : LinearMap.BilinForm F N}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem injective_Gsp_of_apply_ne_one_of_six_le (h6 : 6 ≤ finrank F N) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (ρ : Gsp BN →* (V ≃ₗ[K] V)) {t₀ : Gsp BN} (h : ρ t₀ ≠ 1) :
    Function.Injective ρ := by
  have := isSimpleGroup_Gsp_of_six_le hBN hBNnd h6
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hker | hker
  · exact (MonoidHom.ker_eq_bot_iff ρ).mp hker
  · exact absurd (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top t₀)) h

theorem exists_lineElt_of_six_le_finrank (h6 : 6 ≤ finrank F N) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (t₀ : Gsp BN) (ht₀ : t₀ * t₀ = 1) (ht₀1 : t₀ ≠ 1)
    (hsieg : finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0)
    (hT : finrank F (LinearMap.range
      (((t₀ : LinearMap.GeneralLinearGroup F N) : N →ₗ[F] N) - 1)) ≠ 1) :
    ∃ a c, BN a c = 0 ∧ LinearIndependent F ![a, c] ∧ t₀ = lineElt hBN a c := by
  have hs₀ : IsLongRootElement Qf (ρ t₀) :=
    (isLongRootElement_iff hnd).mpr ⟨fun v => hρQ t₀ v, hsieg.1, hsieg.2⟩
  have hρ1 : ρ t₀ ≠ 1 := by
    intro h1
    have h0 := hsieg.1
    have hmv : movedSpace (1 : V ≃ₗ[K] V) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      simp
    rw [h1, hmv, finrank_bot] at h0
    exact absurd h0 (by norm_num)
  have hinj : Function.Injective ρ := injective_Gsp_of_apply_ne_one_of_six_le h6 hBN hBNnd ρ hρ1
  have hlong : ∀ g : Gsp BN, IsLongRootElement Qf (ρ (g * t₀ * g⁻¹)) := by
    intro g
    rw [map_mul, map_mul, map_inv]
    exact IsLongRootElement.conj (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)) hs₀
  by_contra hnot
  obtain ⟨g, hg⟩ := exists_conj_orderOf_eq_six_of_six_le h6 hBN hBNnd ht₀ ht₀1 hT hnot
  apply orderOf_mul_ne_six hnd hs₀ (hlong g)
  rw [← map_mul, orderOf_injective ρ hinj]
  exact hg

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
