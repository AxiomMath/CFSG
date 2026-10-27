module

public import CFSG.LinearAlgebra.LinearGroups.SLConjugationKer
import CFSG.RankThree.PartTwo.Sec8.Hering418L2

public section

namespace CFSG.LinearGroups

open CFSG.ComponentClassification.CatalogueBHigherLinearAction

private theorem card_eq_card_range_mul_card_ker {G H : Type*} [Group G] [Group H] (θ : G →* H) :
    Nat.card G = Nat.card θ.range * Nat.card θ.ker := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker

private noncomputable def slConjCenterEquivRange (n : ℕ) (K : Type) [Field K] :
    (GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)) ≃* (slConjugation n K).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_slConjugation n K).symm).trans
    (QuotientGroup.quotientKerEquivRange (slConjugation n K))

private noncomputable def slConjQuotHom (n : ℕ) (K : Type) [Field K] :
    (GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)) →*
      MulAut (Matrix.SpecialLinearGroup (Fin n) K) :=
  (slConjugation n K).range.subtype.comp (slConjCenterEquivRange n K).toMonoidHom

private theorem slConjQuotHom_injective (n : ℕ) (K : Type) [Field K] :
    Function.Injective (slConjQuotHom n K) :=
  (slConjugation n K).range.subtype_injective.comp (slConjCenterEquivRange n K).injective

private theorem slConjQuotHom_range (n : ℕ) (K : Type) [Field K] :
    (slConjQuotHom n K).range = (slConjugation n K).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((slConjCenterEquivRange n K) y).2
  · intro hx
    obtain ⟨y, hy⟩ := (slConjCenterEquivRange n K).surjective ⟨x, hx⟩
    refine ⟨y, ?_⟩
    change ((slConjCenterEquivRange n K) y : MulAut (Matrix.SpecialLinearGroup (Fin n) K)) = x
    rw [hy]

private theorem range_comm {G H : Type*} [Group G] [Group H] (θ : G →* H)
    (hcomm : ∀ x y : G, x * y = y * x) :
    ∀ x ∈ θ.range, ∀ y ∈ θ.range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, hcomm a b]

private theorem range_pow_eq_one {G H : Type*} [Group G] [Group H] (θ : G →* H) (p : ℕ)
    (hexp : ∀ x : G, x ^ p = 1) :
    ∀ x ∈ θ.range, x ^ p = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow, hexp a, map_one]

private theorem comap_comm_of_le_range {G H P : Type*} [Group G] [Group H] [Group P]
    (ψ : G →* H) (hψ : Function.Injective ψ) (θ : P →* H)
    (hcomm : ∀ x ∈ θ.range, ∀ y ∈ θ.range, x * y = y * x) :
    ∀ x ∈ θ.range.comap ψ, ∀ y ∈ θ.range.comap ψ, x * y = y * x := by
  intro x hx y hy
  apply hψ
  rw [map_mul, map_mul]
  exact hcomm (ψ x) hx (ψ y) hy

private theorem comap_pow_eq_one_of_le_range {G H P : Type*} [Group G] [Group H] [Group P]
    (ψ : G →* H) (hψ : Function.Injective ψ) (θ : P →* H) (p : ℕ)
    (hexp : ∀ x ∈ θ.range, x ^ p = 1) :
    ∀ x ∈ θ.range.comap ψ, x ^ p = 1 := by
  intro x hx
  apply hψ
  rw [map_pow, map_one]
  exact hexp (ψ x) hx

private theorem card_comap_of_le_range {G H P : Type*} [Group G] [Group H] [Group P]
    (ψ : G →* H) (hψ : Function.Injective ψ) (θ : P →* H) (hθ : θ.range ≤ ψ.range) :
    Nat.card (θ.range.comap ψ) = Nat.card θ.range := by
  rw [← Subgroup.card_map_of_injective (K := θ.range.comap ψ) hψ,
    Subgroup.map_comap_eq_self hθ]

theorem card_le_nine_mul_card_ker_of_range_le_slConjugation {K : Type} [Field K]
    (h3 : (3 : K) ≠ 0) {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E) (θ : ↥E →* MulAut (Matrix.SpecialLinearGroup (Fin 3) K))
    (hθ : θ.range ≤ (slConjugation 3 K).range) : Nat.card E ≤ 9 * Nat.card θ.ker := by
  classical
  have hcomm : ∀ x y : ↥E, x * y = y * x := isMulCommutative_iff.mp hE.1
  have hexp : ∀ x : ↥E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 (x : G) x.2)
  have hψ : Function.Injective (slConjQuotHom 3 K) := slConjQuotHom_injective 3 K
  have hθ' : θ.range ≤ (slConjQuotHom 3 K).range := hθ.trans (slConjQuotHom_range 3 K).ge
  have hcs : Subgroup.center (GL (Fin 3) K) =
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
    rw [CFSG.Assembly.LowTwoRank.StatedScalars,
      Matrix.GeneralLinearGroup.center_eq_range_scalar]
  let e := QuotientGroup.quotientMulEquivOfEq hcs
  have hR'comm : ∀ x ∈ (θ.range.comap (slConjQuotHom 3 K)).map e.toMonoidHom,
      ∀ y ∈ (θ.range.comap (slConjQuotHom 3 K)).map e.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul,
      comap_comm_of_le_range (slConjQuotHom 3 K) hψ θ (range_comm θ hcomm) x hx y hy]
  have hR'exp : ∀ x ∈ (θ.range.comap (slConjQuotHom 3 K)).map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, comap_pow_eq_one_of_le_range (slConjQuotHom 3 K) hψ θ 3
      (range_pow_eq_one θ 3 hexp) x hx, map_one]
  have hbound : Nat.card θ.range ≤ 9 := by
    have h := CFSG.RankThree.PartTwo.Sec4.card_le_nine_of_pgl3 h3
      ((θ.range.comap (slConjQuotHom 3 K)).map e.toMonoidHom) hR'comm hR'exp
    calc Nat.card θ.range = Nat.card (θ.range.comap (slConjQuotHom 3 K)) :=
          (card_comap_of_le_range (slConjQuotHom 3 K) hψ θ hθ').symm
      _ = Nat.card ((θ.range.comap (slConjQuotHom 3 K)).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
      _ ≤ 9 := h
  rw [card_eq_card_range_mul_card_ker θ]
  exact Nat.mul_le_mul_right _ hbound

theorem card_le_three_mul_card_ker_of_range_le_slConjugation_two {K : Type} [Field K]
    [Finite K] (h3 : ringChar K ≠ 3) (h4 : 4 ≤ Nat.card K) {G : Type*} [Group G]
    {E : Subgroup G} [Finite E] (hE : CFSG.Open.IsElemAbelian 3 E)
    (θ : ↥E →* MulAut (Matrix.SpecialLinearGroup (Fin 2) K))
    (hθ : θ.range ≤ (slConjugation 2 K).range) : Nat.card E ≤ 3 * Nat.card θ.ker := by
  classical
  have hcomm : ∀ x y : ↥E, x * y = y * x := isMulCommutative_iff.mp hE.1
  have hexp : ∀ x : ↥E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 (x : G) x.2)
  have hψ : Function.Injective (slConjQuotHom 2 K) := slConjQuotHom_injective 2 K
  have hθ' : θ.range ≤ (slConjQuotHom 2 K).range := hθ.trans (slConjQuotHom_range 2 K).ge
  have hRcomm : ∀ x ∈ θ.range.comap (slConjQuotHom 2 K),
      ∀ y ∈ θ.range.comap (slConjQuotHom 2 K), x * y = y * x :=
    comap_comm_of_le_range (slConjQuotHom 2 K) hψ θ (range_comm θ hcomm)
  have hRexp : ∀ x ∈ θ.range.comap (slConjQuotHom 2 K), x ^ 3 = 1 :=
    comap_pow_eq_one_of_le_range (slConjQuotHom 2 K) hψ θ 3 (range_pow_eq_one θ 3 hexp)
  have hbound : Nat.card θ.range ≤ 3 := by
    have h := CFSG.RankThree.PartTwo.Sec4.Hering418L2.card_le_three_of_pgl2 (K := K) h3 h4
      (θ.range.comap (slConjQuotHom 2 K)) hRcomm hRexp
    calc Nat.card θ.range = Nat.card (θ.range.comap (slConjQuotHom 2 K)) :=
          (card_comap_of_le_range (slConjQuotHom 2 K) hψ θ hθ').symm
      _ ≤ 3 := h
  rw [card_eq_card_range_mul_card_ker θ]
  exact Nat.mul_le_mul_right _ hbound

end CFSG.LinearGroups
