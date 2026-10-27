module

public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
import CFSG.LocalAnalysis.StandardType.GGKGTwMultBridge
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.LieType.Universal.IrreducibleQuadratic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Module QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  (exists_mulEquiv_elementaryGroup_of_lieModel)

private theorem exists_quadMinus_ne_zero {K : Type} [Field K] [Finite K] {m : ℕ}
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : ∃ v, quadMinus m K b c v ≠ 0 := by
  by_contra! h
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  have hx : (Pi.single (Sum.inr (Sum.inr 0)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≠ 0 := by
    simp
  exact hx (eq_zero_of_polar_eq_zero hQ fun y => by simp [polar, h])

private theorem nonempty_statedProj_quadMinus_equiv {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K b c)) ≃*
      elementaryGroup (quadMinus m K b c)) := by
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (coe_quadMinus m K b c) (exists_quadMinus_ne_zero hirr)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans
    (statedOmegaEquiv (coe_quadMinus m K b c) (commutator_orthogonalGroup_quadMinus_of_two_le hm
      hirr))⟩

theorem exists_mulEquiv_elementaryGroup_of_lieModel_POmegaMinus {X : Type} [Group X] {m f : ℕ}
    (h : CFSG.Blueprint.LieModel X .POmegaMinus m 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K), Nat.card K = 2 ^ f ∧
      4 ≤ m ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (X ≃* elementaryGroup (quadMinus m K b c)) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hm⟩, K, hK, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hc
    have hm' : 4 ≤ m := hm
    have : CharP K 2 := by
      let _ := Fintype.ofFinite K
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
    obtain ⟨ε⟩ := nonempty_statedProj_quadMinus_equiv (K := K) (by omega : 2 ≤ m) hirr
    exact ⟨K, hK, hfin, this, b, c, hcard, hm', hirr, ⟨e.trans ε⟩⟩
  all_goals exact absurd ht (by decide)

theorem exists_mulEquiv_elementaryGroup_of_lieModel_PSU_four {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K), Nat.card K = 2 ^ f ∧
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty (X ≃* elementaryGroup (quadMinus 3 K b c)) := by
  obtain ⟨hf, F, _, _, _, hF, ⟨e⟩⟩ :=
    CFSG.StandardType.KGL.exists_mulEquiv_statedSU_of_lieModel_PSU_four h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic (GaloisField 2 f)
  obtain ⟨F', _, _, hF', ⟨θ⟩⟩ :=
    CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_three_mulEquiv hK hirr
  let _ := Fintype.ofFinite F
  let _ := Fintype.ofFinite F'
  have hFF' : Fintype.card F = Fintype.card F' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hF']
  obtain ⟨ε⟩ := nonempty_statedProj_quadMinus_equiv (K := GaloisField 2 f) (m := 3) (by norm_num)
    hirr
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, inferInstance, b, c, hK, hirr,
    ⟨e.trans ((CFSG.Open.StatedSUFieldChange.statedSUEquiv
      (FiniteField.ringEquivOfCardEq hFF') 4 (2 ^ f)).trans (θ.symm.trans ?_))⟩⟩
  exact statedOmegaEquiv (coe_quadMinus 3 (GaloisField 2 f) b c)
    (commutator_orthogonalGroup_quadMinus_of_two_le (by norm_num) hirr)

theorem exists_quadraticSpace_of_rootInvolutionModel {X : Type} [Group X] {m f : ℕ}
    (hΩ : CFSG.Blueprint.LieModel X .POmegaPlus m 2 f ∨
      CFSG.Blueprint.LieModel X .POmegaMinus m 2 f ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel X .PSU 4 2 f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module K V) (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      Nat.card K = 2 ^ f ∧ (polarBilin Q).Nondegenerate ∧ finrank K V = 2 * m ∧ 3 ≤ m ∧
        Nonempty (X ≃* elementaryGroup Q) := by
  rcases hΩ with h | h | ⟨rfl, h⟩
  · obtain ⟨K, _, _, _, hK, hm, ⟨e⟩⟩ := exists_mulEquiv_elementaryGroup_of_lieModel h
    refine ⟨K, inferInstance, inferInstance, inferInstance, Fin m ⊕ Fin m → K, inferInstance,
      inferInstance, inferInstance, quadPlus m K, hK, nondegenerate_polarBilin_quadPlus m K, ?_,
      by omega, ⟨e⟩⟩
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  · obtain ⟨K, _, _, _, b, c, hK, hm, hirr, ⟨e⟩⟩ :=
      exists_mulEquiv_elementaryGroup_of_lieModel_POmegaMinus h
    exact ⟨K, inferInstance, inferInstance, inferInstance, Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      inferInstance, inferInstance, inferInstance, quadMinus m K b c, hK,
      nondegenerate_polarBilin_quadMinus_of_finite m K hirr,
      CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (by omega), by omega, ⟨e⟩⟩
  · obtain ⟨K, _, _, _, b, c, hK, hirr, ⟨e⟩⟩ :=
      exists_mulEquiv_elementaryGroup_of_lieModel_PSU_four h
    exact ⟨K, inferInstance, inferInstance, inferInstance, Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
      inferInstance, inferInstance, inferInstance, quadMinus 3 K b c, hK,
      nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr,
      CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (by omega), le_rfl, ⟨e⟩⟩

private theorem closure_involutions_comap {X G : Type*} [Group X] [Group G] {ψ : X →* G}
    (hψ : Function.Injective ψ) {P : Subgroup G} (hPψ : P ≤ ψ.range)
    (hPgen : Subgroup.closure {g | g ∈ P ∧ orderOf g = 2} = P) :
    Subgroup.closure {g : X | g ∈ P.comap ψ ∧ orderOf g = 2} = P.comap ψ := by
  refine Subgroup.map_injective hψ ?_
  rw [MonoidHom.map_closure, Subgroup.map_comap_eq_self hPψ]
  conv_rhs => rw [← hPgen]
  congr 1
  ext g
  constructor
  · rintro ⟨y, ⟨hy, hyo⟩, rfl⟩
    exact ⟨hy, by rw [orderOf_injective ψ hψ]; exact hyo⟩
  · rintro ⟨hg, hgo⟩
    obtain ⟨y, rfl⟩ := hPψ hg
    exact ⟨y, ⟨hg, by rw [← orderOf_injective ψ hψ]; exact hgo⟩, rfl⟩

theorem exists_rootRadical_of_injective {X G : Type*} [Group X] [Group G] {ψ : X →* G}
    (hψ : Function.Injective ψ) {t : X} {P R : Subgroup G} (hPψ : P ≤ ψ.range)
    (hPt : P ≤ Subgroup.centralizer {ψ t})
    (hPgen : Subgroup.closure {g | g ∈ P ∧ orderOf g = 2} = P) (hRP : R ≤ P)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hR2 : IsPGroup 2 R) (hRc : R ≤ ⁅P, P⁆) {n : ℕ}
    (hC : Nat.card ↥(Subgroup.centralizer (R : Set G) ⊓ ψ.range) = n) :
    ∃ P' R' : Subgroup X, P' ≤ Subgroup.centralizer {t} ∧
      Subgroup.closure {g : X | g ∈ P' ∧ orderOf g = 2} = P' ∧ R' ≤ P' ∧
      (∀ p ∈ P', ∀ r ∈ R', p * r * p⁻¹ ∈ R') ∧ IsPGroup 2 R' ∧ R' ≤ ⁅P', P'⁆ ∧
      Nat.card (Subgroup.centralizer (R' : Set X)) = n := by
  have hRψ : R ≤ ψ.range := hRP.trans hPψ
  refine ⟨P.comap ψ, R.comap ψ, fun p hp => ?_, closure_involutions_comap hψ hPψ hPgen,
    fun r hr => hRP hr, fun p hp r hr => ?_, hR2.comap_of_injective ψ hψ, fun r hr => ?_, ?_⟩
  · have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPt hp)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hψ (by rw [map_mul, map_mul]; exact h1)
  · show ψ (p * r * p⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hRn _ hp _ hr
  · have h1 : ψ r ∈ ⁅P, P⁆ := hRc hr
    rw [← Subgroup.map_comap_eq_self hPψ, ← Subgroup.map_commutator] at h1
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp h1
    rwa [← hψ hyr]
  · have hC' : Subgroup.centralizer (R.comap ψ : Set X) =
        (Subgroup.centralizer (R : Set G)).comap ψ := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
      constructor
      · intro hx r hr
        obtain ⟨r', rfl⟩ := hRψ hr
        rw [← map_mul, ← map_mul, hx r' hr]
      · intro hx r' hr'
        exact hψ (by rw [map_mul, map_mul, hx _ hr'])
    rw [hC', ← hC, Nat.card_congr (((Subgroup.centralizer (R : Set G)).comap ψ).equivMapOfInjective
      ψ hψ).toEquiv, Subgroup.map_comap_eq, inf_comm]

theorem exists_inv_conj_of_injective {X G : Type*} [Group X] [Group G] {ψ : X →* G}
    (hψ : Function.Injective ψ) {t : X} {g : G} (hg : g ∈ ψ.range) {n : ℕ} (hgn : orderOf g = n)
    (hinv : ψ t * g * (ψ t)⁻¹ = g⁻¹) : ∃ y : X, orderOf y = n ∧ t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨y, rfl⟩ := hg
  refine ⟨y, by rw [← hgn, orderOf_injective ψ hψ], hψ ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, hinv]

theorem forall_orderOf_mul_conj_of_injective {X G : Type*} [Group X] [Group G] {ψ : X →* G}
    (hψ : Function.Injective ψ) {t : X}
    (hord : ∀ g : X, orderOf (t * (g * t * g⁻¹)) ∣ 4 ∨ Odd (orderOf (t * (g * t * g⁻¹)))) :
    ∀ k ∈ ψ.range,
      orderOf (ψ t * (k * ψ t * k⁻¹)) ∣ 4 ∨ Odd (orderOf (ψ t * (k * ψ t * k⁻¹))) := by
  rintro _ ⟨g, rfl⟩
  have h : ψ t * (ψ g * ψ t * (ψ g)⁻¹) = ψ (t * (g * t * g⁻¹)) := by
    rw [map_mul, map_mul, map_mul, map_inv]
  rw [h, orderOf_injective ψ hψ]
  exact hord g

end CFSG.ClassicalGroups.Orthogonal
