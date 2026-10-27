module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Fam
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S8

open Matrix CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped commutatorElement Pointwise

theorem mul_comm_of_card_le_four {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 4)
    (a b : G) : a * b = b * a := by
  have h0 : 0 < Nat.card G := Nat.card_pos
  obtain h1 | h1 | h1 | h1 : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by
    omega
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card h1
    exact (IsCyclic.isMulCommutative (α := G)).is_comm.comm a b
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := isCyclic_of_prime_card h1
    exact (IsCyclic.isMulCommutative (α := G)).is_comm.comm a b
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (by rw [h1]; norm_num)).is_comm.comm a b

theorem commutator_mem_of_relIndex_le_four {A : Type*} [Group A] {N M : Subgroup A} [N.Normal]
    (h4 : N.relIndex M ≤ 4) (h0 : N.relIndex M ≠ 0) {x y : A} (hx : x ∈ M) (hy : y ∈ M) :
    ⁅x, y⁆ ∈ N := by
  have : Finite (M ⧸ N.subgroupOf M) := Nat.finite_of_card_ne_zero h0
  have key := mul_comm_of_card_le_four (G := M ⧸ N.subgroupOf M) h4
    (QuotientGroup.mk' _ ⟨x, hx⟩) (QuotientGroup.mk' _ ⟨y, hy⟩)
  have h1 : ⁅(⟨x, hx⟩ : M), ⟨y, hy⟩⁆ ∈ N.subgroupOf M := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact key
  rw [Subgroup.mem_subgroupOf] at h1
  simpa [commutatorElement_def] using h1

variable (K : Type) [Field K]

local notation "κ" => matrixProjectiveConjugationHom (coordinateQuadPlus 4 K)
local notation "P" => matrixProjectiveDerived (coordinateQuadPlus 4 K)
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner
  (matrixProjectiveDerived (coordinateQuadPlus 4 K))

theorem inner_smul_of_mem {Y : Set (Subgroup P)}
    (hY : Y = plusCX 4 K ∨ Y = plusCXstar 4 K (by norm_num)) {c : MulAut P} (hc : c ∈ Inn) :
    c • Y = Y := by
  obtain ⟨g, rfl⟩ := hc
  rcases hY with rfl | rfl
  · exact conj_conjugacyFamily _ g
  · exact conj_conjugacyFamily _ g

theorem commutator_mem_inner_of_smul_eq [Finite K] (h2 : ringChar K ≠ 2)
    (hnd : (QuadraticMap.polarBilin (coordinateQuadPlus 4 K)).Nondegenerate)
    (hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 4)
    {Y : Set (Subgroup P)} (hY : Y = plusCX 4 K ∨ Y = plusCXstar 4 K (by norm_num))
    {a b : MulAut P} (ha : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (haY : a • Y = Y)
    (hb : b ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hbY : b • Y = Y) :
    ⁅a, b⁆ ∈ Inn := by
  have : Finite (MulAut P) :=
    Finite.of_injective (fun e : MulAut P => (e : P → P)) DFunLike.coe_injective
  set D := (linearConjugationHom (coordinateQuadPlus 4 K)).range with hD
  set H := matrixProjectiveImage (coordinateQuadPlus 4 K) ⊓ MulAction.stabilizer (MulAut P) Y
    with hH
  set M := D ⊓ MulAction.stabilizer (MulAut P) Y with hM
  have hDE : D ≤ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  have hMH : M ≤ H := inf_le_inf_right _ hDE
  have hID : Inn ≤ D := by
    rw [inner_eq_map_commutator]
    exact (Subgroup.map_le_range _ _).trans (isometryConjugationHom_range_le _)
  have hIM : Inn ≤ M := fun c hc => ⟨hID hc, inner_smul_of_mem K hY hc⟩
  have hsD : κ (matrixIsometryInclusion _ (swapIso K)) ∈ D :=
    isometryConjugationHom_range_le _ ⟨swapIso K, rfl⟩
  have hsY : κ (matrixIsometryInclusion _ (swapIso K)) • Y ≠ Y := by
    have hne := plusCX_ne_plusCXstar K
    rcases hY with rfl | rfl
    · rw [kappa_swapIso_smul_plusCX]
      exact fun h => hne h.symm
    · rw [kappa_swapIso_smul_plusCXstar]
      exact hne
  have hMD : M ≤ D := inf_le_left
  have h8 : Subgroup.relIndex Inn D ≤ 8 := relIndex_inner_linearRange_le_eight K h2 hnd hQ hab
  have hrel := Subgroup.relIndex_mul_relIndex Inn M D hIM hMD
  have hMD2 : 2 ≤ M.relIndex D := by
    have h0 : M.relIndex D ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : M.relIndex D ≠ 1 := fun h => hsY (Subgroup.relIndex_eq_one.mp h hsD).2
    omega
  have hI0 : Subgroup.relIndex Inn M ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hI4 : Subgroup.relIndex Inn M ≤ 4 := by
    by_contra hlt
    have : 5 * 2 ≤ Subgroup.relIndex Inn M * M.relIndex D := Nat.mul_le_mul (by omega) hMD2
    omega
  have hMab : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ Inn := fun x hx y hy =>
    commutator_mem_of_relIndex_le_four hI4 hI0 hx hy
  have := CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := K ≃+* K)
  set u := κ (fieldPair K σ₀) with hu
  have huY : u • Y = Y := by
    rcases hY with rfl | rfl
    · exact kappa_fieldPair_smul_plusCX K σ₀
    · exact kappa_fieldPair_smul_plusCXstar K σ₀
  have huH : u ∈ H := ⟨⟨_, rfl⟩, huY⟩
  have huS : u ∈ MulAction.stabilizer (MulAut P) Y := huY
  have hcyc : ∀ e ∈ H, ∃ k : ℤ, u ^ k * e ∈ M := by
    rintro e ⟨⟨g, rfl⟩, heY⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hσ₀ g.val.right)
    refine ⟨-j, ?_, (MulAction.stabilizer (MulAut P) Y).mul_mem (zpow_mem huS _) heY⟩
    have hlin : fieldPair K (σ₀ ^ (-j)) * g ∈ linearSimilarityPairs (coordinateQuadPlus 4 K) := by
      rw [mem_linearSimilarityPairs_iff]
      change σ₀ ^ (-j) * g.val.right = 1
      rw [← hj, _root_.zpow_neg, inv_mul_cancel]
    refine ⟨⟨_, hlin⟩, ?_⟩
    change κ (fieldPair K (σ₀ ^ (-j)) * g) = u ^ (-j) * κ g
    rw [map_mul, map_zpow, map_zpow]
  have hcentral : ∀ e ∈ H, ∀ d ∈ M, ⁅e, d⁆ ∈ Inn := by
    intro e he d hd
    obtain ⟨k, hk⟩ := hcyc e he
    have hud : u ∈ commSub Inn d := by
      rw [mem_commSub, ← commutatorElement_inv]
      exact inv_mem (commutator_fieldPair_mem_inner K h2 hnd hQ hab σ₀ (hMD hd))
    have hmd : u ^ k * e ∈ commSub Inn d := by
      rw [mem_commSub]
      exact hMab d hd _ hk
    have he' : e ∈ commSub Inn d := by
      have h := mul_mem (zpow_mem hud (-k)) hmd
      rwa [← mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, one_mul] at h
    rw [mem_commSub, ← commutatorElement_inv] at he'
    simpa using inv_mem he'
  exact CFSG.RankThree.PartOne.KLC.commutator_mem_of_cyclic_quotient Inn H M hMH huH hcyc
    hcentral a ⟨ha, haY⟩ b ⟨hb, hbY⟩

end CFSG.ComponentClassification.HarrisLit.T1.S8
