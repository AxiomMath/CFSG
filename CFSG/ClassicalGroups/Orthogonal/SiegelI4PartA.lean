module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolSix
public import CFSG.ClassicalGroups.Alternating.RT1SpFaithful
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Order

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {F : Type} [Field F] [Finite F] [CharP F 2]
  {N : Type*} [AddCommGroup N] [Module F N] [FiniteDimensional F N]
  {BN : LinearMap.BilinForm F N}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite F] [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem injective_Gsp_of_apply_ne_one (hq : 4 ≤ Nat.card F) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hdim : 2 ≤ finrank F N) (ρ : Gsp BN →* (V ≃ₗ[K] V))
    {t₀ : Gsp BN} (h : ρ t₀ ≠ 1) :
    Function.Injective ρ := by
  have := isSimpleGroup_Gsp hq hBN hBNnd hdim
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hker | hker
  · exact (MonoidHom.ker_eq_bot_iff ρ).mp hker
  · exact absurd (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top t₀)) h

theorem six_le_finrank_and_exists_lineElt (hq : 4 ≤ Nat.card F) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hN : 4 ≤ finrank F N) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (t₀ : Gsp BN) (ht₀ : t₀ * t₀ = 1) (ht₀1 : t₀ ≠ 1)
    (hsieg : finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0)
    (hT : finrank F (LinearMap.range
      (((t₀ : LinearMap.GeneralLinearGroup F N) : N →ₗ[F] N) - 1)) ≠ 1)
    (hA2 : finrank F N = 4 → ∃ v : N,
      BN v ((((t₀ : LinearMap.GeneralLinearGroup F N) : N →ₗ[F] N) - 1) v) ≠ 0) :
    6 ≤ finrank F N ∧
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
  have hinj : Function.Injective ρ := injective_Gsp_of_apply_ne_one hq hBN hBNnd (by omega) ρ hρ1
  have hlong : ∀ g : Gsp BN, IsLongRootElement Qf (ρ (g * t₀ * g⁻¹)) := by
    intro g
    rw [map_mul, map_mul, map_inv]
    exact IsLongRootElement.conj (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)) hs₀
  have hA : ∃ a c, BN a c = 0 ∧ LinearIndependent F ![a, c] ∧ t₀ = lineElt hBN a c := by
    by_contra hnot
    obtain ⟨g, hg⟩ := exists_conj_orderOf_eq_six hq hBN hBNnd ht₀ ht₀1 hT hnot
    apply orderOf_mul_ne_six hnd hs₀ (hlong g)
    rw [← map_mul, orderOf_injective ρ hinj]
    exact hg
  refine ⟨?_, hA⟩
  obtain ⟨n, b, hn, -⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hBN hBNnd
  by_contra hlt
  have hd4 : finrank F N = 4 := by omega
  obtain ⟨v, hv⟩ := hA2 hd4
  obtain ⟨a, c, hac, -, rfl⟩ := hA
  apply hv
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : (((lineElt hBN a c : Gsp BN) : LinearMap.GeneralLinearGroup F N) : N →ₗ[F] N) v - v =
      BN v a • c + BN v c • a := by
    change (lineElt hBN a c).app v - v = _
    rw [lineElt_app hBN hac]
    abel
  rw [LinearMap.sub_apply, Module.End.one_apply, e]
  simp only [map_add, map_smul, smul_eq_mul]
  linear_combination (BN v a * BN v c) * h2

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
