module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalRigid
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.ComponentClassification.RankTwoHypIIOrthogonal

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoHypIIY CFSG.ComponentClassification.RankTwoHypIIClassical
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

theorem oddCore_eq_bot_of_normal {W : Type*} [Group W] [Finite W] {N G : Subgroup W}
    (hNG : N ≤ G) (hn : (N.subgroupOf G).Normal) (hG : CFSG.oddCore ↥G = ⊥) :
    CFSG.oddCore ↥N = ⊥ := by
  have hconj : ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N := fun g hg x hx => by
    have h1 := hn.conj_mem ⟨x, hNG hx⟩ (mem_subgroupOf.mpr hx) ⟨g, hg⟩
    rwa [mem_subgroupOf] at h1
  set R := (CFSG.oddCore ↥N).map N.subtype with hR
  have hRG : ∀ g ∈ G, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    obtain ⟨m, hm, rfl⟩ := hr
    set c : ↥N →* ↥N :=
      { toFun := fun x => ⟨g * x * g⁻¹, hconj g hg x x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp only [coe_mul]; group) } with hc
    have hcs : Function.Surjective c := fun y =>
      ⟨⟨g⁻¹ * y * g⁻¹⁻¹, hconj g⁻¹ (G.inv_mem hg) y y.2⟩, Subtype.ext (by
        simp only [hc, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv]; group)⟩
    have hle : (CFSG.oddCore ↥N).map c ≤ CFSG.oddCore ↥N :=
      CFSG.ABGLocalTools.le_oddCore_of_normal ((CFSG.oddCore_normal ↥N).map c hcs)
        (Odd.of_dvd_nat CFSG.ABGLocalTools.odd_card_oddCore (Subgroup.card_map_dvd _ c))
    exact ⟨c m, hle ⟨m, hm, rfl⟩, rfl⟩
  have hRle : R ≤ G := fun r hr => by
    obtain ⟨m, -, rfl⟩ := hr
    exact hNG m.2
  set R' := R.subgroupOf G
  have hR'n : R'.Normal := ⟨fun r hr g => by
    rw [mem_subgroupOf] at hr ⊢
    simpa using hRG g g.2 r hr⟩
  have hR'odd : Odd (Nat.card R') := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRle).toEquiv, hR,
      Subgroup.card_map_of_injective N.subtype_injective]
    exact CFSG.ABGLocalTools.odd_card_oddCore
  have h1 : R' ≤ CFSG.oddCore ↥G := le_sSup ⟨hR'n, hR'odd⟩
  rw [hG, le_bot_iff] at h1
  have h2 : R = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRle hr⟩ : ↥G) ∈ R' := hr
    rw [h1, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
  {Q : QuadraticForm K (Fin (2 * n) → K)}

abbrev isoKappa (Q : QuadraticForm K (Fin (2 * n) → K)) :
    matrixIsometries Q →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)

omit [Finite K] [CharP K 2] in
theorem eq_inclusion_of_right_eq_one {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hright : S.val.right = 1) :
    ∃ A : matrixIsometries Q, matrixIsometryInclusion Q A = S := by
  have hA : S.val.left ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    have h1 := hS v
    rw [coordinateSemilinearMap_apply, hright] at h1
    rw [matrixLinearEquiv_apply]
    simpa using h1
  have hmem : S ∈ matrixIsometryPairs Q := (mem_matrixIsometryPairs_iff Q S).mpr ⟨hA, hright⟩
  exact hmem

section Regular

variable (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)
include hQ hT hE

variable {M E : Subgroup (MulAut (matrixProjectiveDerived Q))}

theorem exists_isometry_of_mem {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (h : HypIIConfig (inner (matrixProjectiveDerived Q)) E M) (hEQ : E ≤ matrixProjectiveImage Q)
    {α : MulAut (matrixProjectiveDerived Q)} (hα : α ∈ E) :
    ∃ A : matrixIsometries Q, isoKappa Q A = α := by
  obtain ⟨S, hS, rfl⟩ := exists_unit_rep (hEQ hα)
  by_cases hright : S.val.right = 1
  · obtain ⟨A, rfl⟩ := eq_inclusion_of_right_eq_one hS hright
    exact ⟨A, rfl⟩
  · exact (false_of_field hQ hT hE hf hK hn h hEQ hS hα hright).elim

theorem two_le_rank_of_mem {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (h : HypIIConfig (inner (matrixProjectiveDerived Q)) E M) (hEQ : E ≤ matrixProjectiveImage Q)
    {A : matrixIsometries Q} (hA : isoKappa Q A ∈ E) (hA1 : A ≠ 1) :
    2 ≤ (((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank := by
  have hd : 1 ≤ 2 * n := by omega
  have hAA : A * A = 1 := by
    apply kappa_inclusion_injective hQ hT hE hd
    rw [map_mul, map_one, ← pow_two]
    exact h.elemAbelian.2 _ hA
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hv, hAv⟩ := OmegaRadical.exists_symmetry_of_rank_le_one hQ A.2
    (congrArg Subtype.val hAA) (fun h1 => hA1 (Subtype.ext h1)) (by omega)
  have hAeq : A = symmetryIsometry Q v := Subtype.ext hAv
  rw [hAeq] at hA
  exact false_of_symmetry hQ hT hE hK hn h hEQ hv hA

theorem oddCore_centralizer_eq_bot {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (h : HypIIConfig (inner (matrixProjectiveDerived Q)) E M) (hEQ : E ≤ matrixProjectiveImage Q)
    {A : matrixIsometries Q} (hA : isoKappa Q A ∈ E) (hA1 : A ≠ 1) :
    CFSG.oddCore ↥(inner (matrixProjectiveDerived Q) ⊓
      centralizer ({isoKappa Q A} : Set (MulAut (matrixProjectiveDerived Q)))) = ⊥ := by
  have := finite_mulAut_PQ (Q := Q)
  have hd : 1 ≤ 2 * n := by omega
  have hψ : Function.Injective (isoKappa Q) := kappa_inclusion_injective hQ hT hE hd
  set α := isoKappa Q A
  have hα1 : α ≠ 1 := fun h1 => hA1 (hψ (h1.trans (map_one _).symm))
  have hord : orderOf α = 2 := orderOf_eq_prime (h.elemAbelian.2 α hA) hα1
  have hinnerQ := matrixProjective_inner_le_image Q
  have hO := OmegaRadical.higherRankOddCore_of_regular hQ hT hE (matrixProjectiveImage Q)
    hinnerQ le_rfl A (hEQ hA) hord (two_le_rank_of_mem hQ hT hE hK hn h hEQ hA hA1)
  set C := centralizer ({α} : Set (MulAut (matrixProjectiveDerived Q)))
  refine oddCore_eq_bot_of_normal (inf_le_inf_right C hinnerQ) ?_ hO
  have hXn := OuterAutomorphisms.inner_normal (matrixProjectiveDerived Q)
  refine ⟨fun y hy g => ?_⟩
  rw [mem_subgroupOf] at hy ⊢
  obtain ⟨hyX, hyC⟩ := mem_inf.mp hy
  obtain ⟨-, hgC⟩ := mem_inf.mp g.2
  exact mem_inf.mpr ⟨hXn.conj_mem _ hyX g, C.mul_mem (C.mul_mem hgC hyC) (C.inv_mem hgC)⟩

theorem false_of_linear (hL : OrthLinearConfigFree) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (h : HypIIConfig (inner (matrixProjectiveDerived Q)) E M) (hEQ : E ≤ matrixProjectiveImage Q) :
    False := by
  have := finite_mulAut_PQ (Q := Q)
  have hd : 1 ≤ 2 * n := by omega
  have hψ : Function.Injective (isoKappa Q) := kappa_inclusion_injective hQ hT hE hd
  set F₀ : Subgroup (matrixIsometries Q) := E.comap (isoKappa Q) with hF₀
  set F : Subgroup (GL (Fin (2 * n)) K) := F₀.map (matrixIsometries Q).subtype with hF
  have hmemF : ∀ A : matrixIsometries Q, (A : GL (Fin (2 * n)) K) ∈ F ↔ isoKappa Q A ∈ E := by
    intro A
    constructor
    · rintro ⟨B, hB, hBA⟩
      rwa [Subtype.ext hBA] at hB
    · intro hA
      exact ⟨A, hA, rfl⟩
  have hFO : F ≤ matrixIsometries Q := by
    rintro _ ⟨A, -, rfl⟩
    exact A.2
  have hmap : F₀.map (isoKappa Q) = E := by
    apply le_antisymm (Subgroup.map_comap_le _ _)
    intro α hα
    obtain ⟨A, rfl⟩ := exists_isometry_of_mem hQ hT hE hf hK hn h hEQ hα
    exact ⟨A, hα, rfl⟩
  have hcardF : Nat.card F = Nat.card E := by
    rw [hF, Subgroup.card_map_of_injective (matrixIsometries Q).subtype_injective, ← hmap,
      Subgroup.card_map_of_injective hψ]
  have hFel : IsElemAbelian 2 F := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨A, hA, hAa⟩ := a.2
      obtain ⟨B, hB, hBb⟩ := b.2
      have hc : A * B = B * A := hψ (by rw [map_mul, map_mul]; exact h.commute hA hB)
      have hc' := congrArg Subtype.val hc
      rw [coe_mul, coe_mul, ← hAa, ← hBb]
      simpa using hc'
    · rintro _ ⟨A, hA, rfl⟩
      have h2 : A ^ 2 = 1 := hψ (by rw [map_pow, map_one]; exact h.elemAbelian.2 _ hA)
      exact congrArg Subtype.val h2
  have hFD : ¬ F ≤ matrixDerived Q := by
    intro hle
    apply h.not_le
    intro α hα
    obtain ⟨A, rfl⟩ := exists_isometry_of_mem hQ hT hE hf hK hn h hEQ hα
    have hAD : (A : GL (Fin (2 * n)) K) ∈ matrixDerived Q := hle ((hmemF A).mpr hα)
    refine ⟨matrixProjectiveProjection Q ⟨A, hAD⟩, ?_⟩
    rw [← kappa_derived_eq_conj]
    rfl
  have hFr : ∀ s ∈ F, s ≠ 1 →
      2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank := by
    rintro _ ⟨A, hA, rfl⟩ hs1
    exact two_le_rank_of_mem hQ hT hE hK hn h hEQ hA (fun h1 => hs1 (by rw [h1]; rfl))
  have hFN : ∀ x ∈ F, x ≠ 1 → matrixDerived Q ⊓ centralizer ({x} : Set (GL (Fin (2 * n)) K)) ≤
      normalizer (F : Set (GL (Fin (2 * n)) K)) := by
    rintro _ ⟨A, hA, rfl⟩ hx1 g ⟨hgD, hgx⟩
    have hA1 : A ≠ 1 := fun h1 => hx1 (by rw [h1]; rfl)
    set g' : matrixIsometries Q := ⟨g, matrixDerived_le_isometries Q hgD⟩
    have hgX : isoKappa Q g' ∈ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
      ⟨matrixProjectiveProjection Q ⟨g, hgD⟩, by rw [← kappa_derived_eq_conj]; rfl⟩
    have hgc : g' * A = A * g' := Subtype.ext (mem_centralizer_singleton_iff.mp hgx)
    have hgC : isoKappa Q g' ∈ centralizer ({isoKappa Q A} : Set _) :=
      mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hgc])
    have hgN := h.centralizer_le_normalizer (OuterAutomorphisms.inner_normal _) hA
      (fun h1 => hA1 (hψ (h1.trans (map_one _).symm)))
      (oddCore_centralizer_eq_bot hQ hT hE hK hn h hEQ hA hA1) ⟨hgX, hgC⟩
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hmem := (mem_normalizer_iff.mp hgN (isoKappa Q B)).mp hB
      refine ⟨g' * B * g'⁻¹, ?_, rfl⟩
      change isoKappa Q (g' * B * g'⁻¹) ∈ E
      rwa [map_mul, map_mul, map_inv]
    · intro hy
      obtain ⟨B, hB, hBy⟩ := hy
      have hyO : y ∈ matrixIsometries Q := by
        have h1 : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [h1, ← hBy]
        exact (matrixIsometries Q).mul_mem ((matrixIsometries Q).mul_mem
          ((matrixIsometries Q).inv_mem g'.2) B.2) g'.2
      refine ⟨⟨y, hyO⟩, ?_, rfl⟩
      have hB' : g' * ⟨y, hyO⟩ * g'⁻¹ = B := Subtype.ext (by simpa using hBy.symm)
      have hmem := (mem_normalizer_iff.mp hgN (isoKappa Q ⟨y, hyO⟩)).mpr (by
        rw [← map_inv, ← map_mul, ← map_mul, hB']
        exact hB)
      exact hmem
  exact hL K n hn Q hQ hT hE F hFO hFel (by rw [hcardF]; exact h.four_le_card) hFD hFr hFN

end Regular

end CFSG.ComponentClassification.RankTwoHypIIOrthogonal
