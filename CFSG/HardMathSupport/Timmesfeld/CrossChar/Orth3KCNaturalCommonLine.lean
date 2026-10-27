module

public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonLine
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCInnerPlane

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal
open Polynomial Module QuadraticMap CFSG CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
section Layers
variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}
variable {p : ℕ}
theorem natural_fixed_component_fixed3 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (x : orthDerived Q) (hxp : orderOf x = p)
    (hxA : (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A)
    (hx1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1) (κ : MulAut (ProjOrthDerived Q))
    (hcent : ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ)
    (hlist : FixedLayerListed Q (x : V ≃ₗ[K] V)) :
    ∀ j ∈ fixedComponentImage Q (x : V ≃ₗ[K] V), κ j = j := by
  have hinj := conj_injective_projOrthDerived hQ hT
  obtain ⟨-, n, Cs, -, -, hC, hcomp, -⟩ :=
    (orthogonal_inner_plane_local_core_centralization3 hQ hT hp hpne hK4 hpl D hD A hA hAc _ hxA hx1
        x
      rfl hxp).1 hlist
  intro j hj
  rw [← hC] at hj
  refine Subgroup.iSup_induction Cs (C := fun j => κ j = j) hj (fun i y hy => ?_) (map_one κ)
    (fun a b ha hb => ?_)
  · exact fix_of_isComponent hinj D hD _ κ hcent (hcomp i).2.2.1 (hcomp i).2.2.2.2 y hy
  · rw [map_mul, ha, hb]
end Layers
section Line
open CFSG.RankThree.Classical
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}
theorem natural_line_scalar3 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (Ã : Subgroup (orthDerived Q))
    (hÃA : ∀ x ∈ Ã, (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A)
    (hpow : ∀ x ∈ Ã, x ^ p = 1)
    (hinj1 : ∀ x ∈ Ã, (QuotientGroup.mk x : ProjOrthDerived Q) = 1 → x = 1)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ)
    (M : Subgroup Ã) (hM : Nat.card M = p)
    (hker : ∀ a ∈ M, a ≠ 1 →
      LinearMap.ker (((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id) =
        lineFixSpace M)
    (h3 : 3 ≤ finrank K (lineFixSpace M))
    (hq3 : Nat.card K = 3 → finrank K (lineFixSpace M) ≠ 3)
    (hsplit : (Nat.card K = 2 ∨ Nat.card K = 3) →
      ¬ (finrank K (lineFixSpace M) = 4 ∧ ∃ S : Submodule K (lineFixSpace M),
        finrank K S = 2 ∧ ∀ s ∈ S, (Q.comp (lineFixSpace M).subtype) s = 0)) :
    ∃ c : Kˣ, ∀ v ∈ lineFixSpace M, F v = (c : K) • v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2le := hp.two_le
  have hMne : M ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hM
    exact hp.one_lt.ne hM
  obtain ⟨x0, hx0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
  have hxtM : (x0 : Ã) ∈ M := x0.2
  have hxt1 : (x0 : Ã) ≠ 1 := fun h => hx0 (Subtype.ext h)
  have hxÃ : ((x0 : Ã) : orthDerived Q) ∈ Ã := (x0 : Ã).2
  have hx1 : ((x0 : Ã) : orthDerived Q) ≠ 1 := fun h => hxt1 (Subtype.ext h)
  have hxord : orderOf ((x0 : Ã) : orthDerived Q) = p := orderOf_eq_prime (hpow _ hxÃ) hx1
  have hxA := hÃA _ hxÃ
  have hxne : (QuotientGroup.mk ((x0 : Ã) : orthDerived Q) : ProjOrthDerived Q) ≠ 1 :=
    fun h => hx1 (hinj1 _ hxÃ h)
  have hxO := oddOrderIsometry_of_orthDerived hp hpl hQ ((x0 : Ã) : orthDerived Q) hxord
  have hW : fixedSpace (((x0 : Ã) : orthDerived Q) : V ≃ₗ[K] V) = lineFixSpace M :=
    hker (x0 : Ã) hxtM hxt1
  rw [← hW] at h3 hq3 hsplit ⊢
  have hlist : FixedLayerListed Q (((x0 : Ã) : orthDerived Q) : V ≃ₗ[K] V) := by
    refine ⟨h3, ?_⟩
    rintro (⟨h3', h3''⟩ | ⟨⟨h4, S, hS2, hSQ⟩, hq⟩)
    · exact hq3 h3'' h3'
    · exact hsplit hq ⟨h4, S, hS2, hSQ⟩
  have hfix := natural_fixed_component_fixed3 hQ hT hp hpne hK4 hpl D hD A hA hAc _ hxord hxA hxne κ
    (hcent _ hxA hxne) hlist
  obtain ⟨-, c, hc⟩ := hxO.fixedSpace_scalar hQ hT hlist σ F hFσ μ hμ hFQ κ hκF hfix
  exact ⟨c, hc⟩
end Line
end CFSG.RankThree.PartOne.KCOrthogonal