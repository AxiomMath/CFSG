module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.A2Lemma
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldTorus

set_option linter.unusedSectionVars false

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.SeitzReduction.E6Pilot CFSG.RankThree.PartOne.CTP

section Cube

variable {K : Type} [Field K]

@[expose] def CubeDescent (σ : K ≃+* K) : Prop :=
  ∀ (b : (fixSubfield σ)ˣ) (d : Kˣ),
    Units.map (fixSubfield σ).subtype.toMonoidHom b = d ^ 3 → ∃ y : (fixSubfield σ)ˣ, b = y ^ 3

theorem cubeDescent_of_card_two (σ : K ≃+* K) (h2 : Nat.card (fixSubfield σ) = 2) :
    CubeDescent σ := by
  intro b d _
  refine ⟨1, ?_⟩
  have hb : (((b : (fixSubfield σ)ˣ) : fixSubfield σ) : K) = 1 := by
    rcases CFSG.LieType.SeitzGeneration.ExcOuterLeOne.zero_or_one_of_mem_card_two h2
        (((b : (fixSubfield σ)ˣ) : fixSubfield σ).2) with h | h
    · exact absurd (Subtype.ext h) b.ne_zero
    · exact h
  exact Units.ext (Subtype.ext (by simpa using hb))

end Cube

section Descent

open CFSG.Timmesfeld.ExceptionalOrders (smithE6 smithE6P smithE6P' smithE6Q smithE6Q' smithE6D
  smithE6P'_mul smithE6Q_mul)

variable {K : Type} [Field K]

theorem exists_monomial_eq_of_pow (σ : K ≃+* K) (hcube : CubeDescent σ)
    (a : Fin Tag.E6.rank → (fixSubfield σ)ˣ) (c : Fin Tag.E6.rank → Kˣ)
    (hac : (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (a i)) =
      monomialHom Tag.E6.cartan.transpose c) :
    ∃ s : Fin Tag.E6.rank → (fixSubfield σ)ˣ, monomialHom Tag.E6.cartan.transpose s = a := by
  set ι : (fixSubfield σ)ˣ →* Kˣ := Units.map (fixSubfield σ).subtype.toMonoidHom with hι
  set Dm : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
    Matrix.diagonal (fun i => (smithE6D i : ℤ)) with hDm
  have hA := cartan_transpose_E6
  have hQQ : smithE6Q'.transpose * smithE6Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE6Q_mul, Matrix.transpose_one]
  have hQQ' : smithE6Q.transpose * smithE6Q'.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE6Q'_mul, Matrix.transpose_one]
  have hPP : smithE6P.transpose * smithE6P'.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE6P'_mul, Matrix.transpose_one]
  set b := monomialHom smithE6Q'.transpose a with hbdef
  have hb : (fun i => ι (b i)) = monomialHom Dm (monomialHom smithE6P.transpose c) := by
    rw [hbdef, map_monomialHom ι, hac, monomialHom_mul, hA, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hQQ, Matrix.one_mul, ← monomialHom_mul]
  have h5 : ι (b nodeSixE6) = (monomialHom smithE6P.transpose c nodeSixE6) ^ 3 := by
    rw [show ι (b nodeSixE6) = monomialHom Dm (monomialHom smithE6P.transpose c) nodeSixE6 from
      congrFun hb nodeSixE6, hDm, monomialHom_diagonal, smithE6D_eq]
    simp
  obtain ⟨y, hy⟩ := hcube (b nodeSixE6) _ h5
  set b' := Function.update b nodeSixE6 y with hb'def
  have hb' : monomialHom Dm b' = b := by
    funext i
    rw [hDm, monomialHom_diagonal, smithE6D_eq]
    by_cases hi : i = nodeSixE6
    · subst hi
      simp [hb'def, hy]
    · simp [hb'def, hi]
  refine ⟨monomialHom smithE6P'.transpose b', ?_⟩
  rw [monomialHom_mul, hA, Matrix.mul_assoc, hPP, Matrix.mul_one, ← monomialHom_mul, hb', hbdef,
    monomialHom_mul, hQQ', monomialHom_one]

end Descent

section Torus

variable {K : Type} [Field K]


theorem entrywiseFixedTorus_le_fixedFieldImage_E6_of_pow (σ : K ≃+* K) (hcube : CubeDescent σ) :
    entrywiseFixedTorus .E6 σ ≤ fixedFieldImage .E6 σ := by
  set k := fixSubfield σ with hk
  set ι : k →+* K := k.subtype with hι
  rintro h ⟨hT, hΓ⟩
  obtain ⟨c, rfl⟩ := torusGroup_le_range_rootDiagUnit_monomial (K := K) Tag.E6 hT
  set a := monomialHom Tag.E6.cartan.transpose c with ha
  have hh : ((rootDiagUnitHom Tag.E6 K).comp (monomialHom Tag.E6.cartan.transpose)) c =
      rootDiagUnit Tag.E6 a := rfl
  rw [hh] at hΓ ⊢
  have hσa : ∀ i, σ (a i : K) = a i := by
    have hF : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E6 a) =
        rootDiagUnit Tag.E6 a := hΓ.2
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E6 a) =
        rootDiagUnit Tag.E6 (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 := rootDiagUnit_injective (h0.symm.trans hF)
    intro i
    exact congrArg Units.val (congrFun h1 i)
  set a' : Fin Tag.E6.rank → kˣ := fun i =>
    Units.mk0 ⟨a i, hσa i⟩ fun h0 => (a i).ne_zero (congrArg Subtype.val h0) with ha'def
  have ha' : (fun i => Units.map ι.toMonoidHom (a' i)) = a := funext fun i => Units.ext rfl
  obtain ⟨s, hs⟩ := exists_monomial_eq_of_pow σ hcube a' c ha'
  rw [← ha', ← hs]
  have hprod : rootDiagUnit Tag.E6
      (fun i => Units.map ι.toMonoidHom (monomialHom Tag.E6.cartan.transpose s i)) =
      ((List.finRange Tag.E6.rank).map fun j =>
        torusElt Tag.E6 K j (Units.map ι.toMonoidHom (s j))).prod := by
    rw [list_prod_torusElt_eq_rootDiagUnit]
    congr 1
    funext l
    rw [monomialHom_apply, cartanChar, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, Matrix.transpose_apply]
  rw [hprod]
  have hmem : ((List.finRange Tag.E6.rank).map fun j => torusElt Tag.E6 k j (s j)).prod ∈
      adjointGroup Tag.E6 k := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup j _
  refine ⟨_, hmem, ?_⟩
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => baseChangeGL_torusElt ι j (s j)

end Torus

section Fixed

variable {K : Type} [Field K] [Finite K]


theorem entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow (σ : K ≃+* K) (hcube : CubeDescent σ) :
    entrywiseFixedGroup .E6 σ = fixedFieldImage .E6 σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup .E6 K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup .E6 σ : Set (ModGL .E6 K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  exact mul_mem (entrywiseFixedTorus_le_fixedFieldImage_E6_of_pow σ hcube hh) hj

theorem fixedSubgroup_entrywiseAdjointAut_E6 (σ : K ≃+* K) (hcube : CubeDescent σ) :
    fixedSubgroup (entrywiseAdjointAut .E6 σ) =
      (fixedFieldImage .E6 σ).subgroupOf (adjointGroup .E6 K) := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf,
    ← entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow σ hcube, mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val h
    rwa [coe_entrywiseAdjointAut] at this
  · rintro ⟨-, h⟩
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact h

noncomputable def fixedE6Equiv (σ : K ≃+* K) (hcube : CubeDescent σ) :
    ↥(fixedSubgroup (entrywiseAdjointAut .E6 σ)) ≃* adjointGroup .E6 (fixSubfield σ) :=
  (MulEquiv.subgroupCongr (fixedSubgroup_entrywiseAdjointAut_E6 σ hcube)).trans
    ((Subgroup.subgroupOfEquivOfLe (fun _ hj => (mem_entrywiseFixedGroup.1
      ((Chevalley_coordinate_field_fixed_normal_subgroup .E6 K σ).2.2.2.1 hj)).1)).trans
      (fixedFieldImageEquiv (τ := .E6) σ).symm)

theorem eq_one_of_central_fixed_E6 (σ : K ≃+* K) (hcube : CubeDescent σ) {x : adjointGroup .E6 K}
    (hx : x ∈ fixedSubgroup (entrywiseAdjointAut .E6 σ))
    (hc : ∀ y ∈ fixedSubgroup (entrywiseAdjointAut .E6 σ), x * y = y * x) : x = 1 := by
  have hz : fixedE6Equiv σ hcube ⟨x, hx⟩ ∈
      Subgroup.center (adjointGroup .E6 (fixSubfield σ)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ : ∃ y : ↥(fixedSubgroup (entrywiseAdjointAut .E6 σ)),
        fixedE6Equiv σ hcube y = g := ⟨(fixedE6Equiv σ hcube).symm g, by simp⟩
    rw [← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  have h1 : (⟨x, hx⟩ : ↥(fixedSubgroup (entrywiseAdjointAut .E6 σ))) = 1 :=
    (fixedE6Equiv σ hcube).injective (by rw [hz, map_one])
  exact congrArg Subtype.val h1

end Fixed

end CFSG.LieType.SeitzGeneration.ExcWideThree
