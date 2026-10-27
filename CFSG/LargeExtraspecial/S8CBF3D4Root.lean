module

public import CFSG.LargeExtraspecial.S8CBF3D4Levi
public import CFSG.LieType.Chevalley.PositiveRootCollection
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas
public import CFSG.RankThree.Chevalley.EvenTrialityElementaryNine
public import CFSG.RankThree.Chevalley.EvenFourCommutingSL2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped commutatorElement

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)

theorem commutator_rootSpan_le_heightSeries
    {τ : Tag} (K : Type) [Field K]
    {S : Set (Fin τ.rank → ℤ)} {h : ℤ} (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hcomb : ∀ α ∈ S, ∀ β ∈ S, α ≠ β → ∀ γ, IsRoot τ γ →
      (∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β) → h ≤ height γ ∧ 0 < height γ) :
    ⁅rootSpan τ K S, rootSpan τ K S⁆ ≤ heightSeries τ K h := by
  have hSU : rootSpan τ K S ≤ posUnipotent τ K := rootSpan_mono fun α hα => hS α hα
  rw [rootSpan_eq_closure K S] at hSU ⊢
  refine commutator_closure_le_of_le_normalizer hSU hSU (heightSeries_le_normalizer K h) ?_
  rintro _ ⟨α, hα, c, rfl⟩ _ ⟨β, hβ, d, rfl⟩
  by_cases hab : α = β
  · subst hab
    rw [commutatorElement_eq_one_iff_mul_comm.2 (rootSubgroup_mul_comm K
      (Subgroup.subset_closure ⟨c, rfl⟩) (Subgroup.subset_closure ⟨d, rfl⟩))]
    exact one_mem _
  · have hle := commutator_rootSubgroup_le K (hS α hα).1 (hS β hβ).1 (hS α hα).2 (hS β hβ).2 hab
    refine (hle.trans (iSup₂_le fun γ hγ => ?_)) (commutator_mem_commutator
      (Subgroup.subset_closure ⟨c, rfl⟩) (Subgroup.subset_closure ⟨d, rfl⟩))
    obtain ⟨hhγ, hγp⟩ := hcomb α hα β hβ hab γ hγ.1 hγ.2
    exact le_iSup₂_of_le γ ⟨hγ.1, hγp, hhγ⟩ le_rfl

theorem d4_root_coefficient_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots,
    (0 < l.sum → 0 ≤ l.getD 0 0 ∧ 0 ≤ l.getD 1 0 ∧ 0 ≤ l.getD 2 0 ∧ 0 ≤ l.getD 3 0) ∧
    (2 ≤ l.getD 2 0 → 5 ≤ l.sum) ∧ (2 ≤ l.getD 0 0 + l.getD 1 0 + l.getD 3 0 → 3 ≤ l.sum) := by
  decide

theorem d4_root_coefficients {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) :
    (0 < height α → 0 ≤ α (ν 0) ∧ 0 ≤ α (ν 1) ∧ 0 ≤ α (ν 2) ∧ 0 ≤ α (ν 3)) ∧
    (2 ≤ α (ν 2) → 5 ≤ height α) ∧ (2 ≤ α (ν 0) + α (ν 1) + α (ν 3) → 3 ≤ height α) := by
  have h := d4_root_coefficient_check _ (isRoot_iff_mem_artifactRoots.1 hα)
  have e : ∀ (i : ℕ) (hi : i < TwistTag.D4.tag.rank), (List.ofFn α).getD i 0 = α ⟨i, hi⟩ :=
    fun i hi => by rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), List.sum_ofFn] at h
  exact h

theorem orbitUnion_outer :
    TwistTag.D4.orbitUnion {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} = outerSet := by
  ext i
  rw [mem_orbitUnion_iff_orbitIndex, Set.mem_singleton_iff, mem_outerSet]
  revert i
  decide

theorem orbitUnion_middle :
    TwistTag.D4.orbitUnion {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} = {ν 2} := by
  ext i
  rw [mem_orbitUnion_iff_orbitIndex, Set.mem_singleton_iff, Set.mem_singleton_iff]
  revert i
  decide

theorem commutator_parabolicRadical_outer_le
    (K : Type) [Field K] :
    ⁅parabolicRadical TwistTag.D4.tag K outerSet, parabolicRadical TwistTag.D4.tag K outerSet⁆ ≤
      heightSeries TwistTag.D4.tag K 5 := by
  have hcoef : ∀ α ∈ parabolicRadicalRoots TwistTag.D4.tag outerSet, 1 ≤ α (ν 2) := by
    rintro α ⟨⟨hαr, hαp⟩, hαA⟩
    have h0 := ((d4_root_coefficients hαr).1 hαp).2.2.1
    by_contra hlt
    apply hαA
    refine ⟨⟨hαr, fun i hi => ?_⟩, hαr, hαp⟩
    have hi2 : i = ν 2 := by
      rw [mem_outerSet] at hi
      revert hi
      revert i
      decide
    rw [hi2]
    omega
  refine commutator_rootSpan_le_heightSeries K (fun α hα => hα.1) ?_
  rintro α hα β hβ - γ hγ ⟨a, b, ha, hb, rfl⟩
  have h1 := hcoef α hα
  have h2 := hcoef β hβ
  have hγ2 : 2 ≤ (a • α + b • β) (ν 2) := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have h5 := (d4_root_coefficients hγ).2.1 hγ2
  exact ⟨h5, by omega⟩

theorem commutator_parabolicRadical_middle_le
    (K : Type) [Field K] :
    ⁅parabolicRadical TwistTag.D4.tag K {ν 2}, parabolicRadical TwistTag.D4.tag K {ν 2}⁆ ≤
      heightSeries TwistTag.D4.tag K 3 := by
  have hcoef : ∀ α ∈ parabolicRadicalRoots TwistTag.D4.tag {ν 2},
      1 ≤ α (ν 0) + α (ν 1) + α (ν 3) := by
    rintro α ⟨⟨hαr, hαp⟩, hαA⟩
    obtain ⟨h0, h1, -, h3⟩ := (d4_root_coefficients hαr).1 hαp
    by_contra hlt
    apply hαA
    refine ⟨⟨hαr, fun i hi => ?_⟩, hαr, hαp⟩
    have hi' : i = ν 0 ∨ i = ν 1 ∨ i = ν 3 := by
      rw [Set.mem_singleton_iff] at hi
      revert hi
      revert i
      decide
    rcases hi' with rfl | rfl | rfl <;> omega
  refine commutator_rootSpan_le_heightSeries K (fun α hα => hα.1) ?_
  rintro α hα β hβ - γ hγ ⟨a, b, ha, hb, rfl⟩
  have h1 := hcoef α hα
  have h2 := hcoef β hβ
  have hγ2 : 2 ≤ (a • α + b • β) (ν 0) + (a • α + b • β) (ν 1) + (a • α + b • β) (ν 3) := by
    simp only [Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have h3 := (d4_root_coefficients hγ).2.2 hγ2
  exact ⟨h3, by omega⟩

theorem d4_height_five_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots, 5 ≤ l.sum →
    l = [1, 1, 2, 1] := by
  decide

theorem eq_theta_of_five_le_height
    {β : Fin TwistTag.D4.tag.rank → ℤ} (hβ : IsRoot TwistTag.D4.tag β) (h5 : 5 ≤ height β) :
    β = v4 1 1 2 1 := by
  apply List.ofFn_injective
  rw [d4_height_five_check _ (isRoot_iff_mem_artifactRoots.1 hβ)
    (by rw [List.sum_ofFn]; exact h5)]
  rfl

theorem heightSeries_five_le
    (K : Type) [Field K] :
    heightSeries TwistTag.D4.tag K 5 ≤ rootSubgroup TwistTag.D4.tag K (v4 1 1 2 1) :=
  iSup₂_le fun β hβ => by rw [eq_theta_of_five_le_height hβ.1 hβ.2.2]

open Matrix in
theorem outer_theta_orthogonal : ∀ j : Fin TwistTag.D4.tag.rank, j ≠ ν 2 →
    0 ≤ Pi.single j 1 ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ v4 1 1 2 1) ∧
    0 ≤ (-Pi.single j 1) ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ v4 1 1 2 1) ∧
    Pi.single j 1 ≠ v4 1 1 2 1 ∧ -Pi.single j 1 ≠ v4 1 1 2 1 := by
  decide

theorem commute_leviRoot_outer_heightSeries_five
    (K : Type) [Field K] {x u : ModGL TwistTag.D4.tag K} (hx : x ∈ leviRoot K outerSet)
    (hu : u ∈ heightSeries TwistTag.D4.tag K 5) : x * u = u * x := by
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 (heightSeries_five_le K hu)
  have hθ : IsRoot TwistTag.D4.tag (v4 1 1 2 1) := isRoot_v4_1121
  have hle : leviRoot K outerSet ≤
      centralizer ({pinnedX TwistTag.D4.tag K (v4 1 1 2 1) d} : Set (ModGL TwistTag.D4.tag K)) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · have hj2 : j ≠ ν 2 := by
        rw [mem_outerSet] at hj
        rcases hj with rfl | rfl | rfl <;> decide
      obtain ⟨h0, -, hne, -⟩ := outer_theta_orthogonal j hj2
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← pinnedX_single]
      exact (pinnedX_commute_of_rootForm_nonneg (Or.inl rfl) (isRoot_single _ j) hθ hne h0 c
        d).eq
    · have hj2 : j ≠ ν 2 := by
        rw [mem_outerSet] at hj
        rcases hj with rfl | rfl | rfl <;> decide
      obtain ⟨-, h0, -, hne⟩ := outer_theta_orthogonal j hj2
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← pinnedX_neg_single]
      exact (pinnedX_commute_of_rootForm_nonneg (Or.inl rfl)
        (isRoot_neg_iff.2 (isRoot_single _ j)) hθ hne h0 c d).eq
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem exists_outer_sl2
    (K : Type) [Field K] [CharP K 2]
    (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∃ f : SL2 K →* ModGL TwistTag.D4.tag K, Function.Injective f ∧
      f.range ≤ graphFixedRootGroup TwistTag.D4 K σ ∧ f.range ≤ leviRoot K outerSet := by
  obtain ⟨Ro, -, -, -, -, -, hRorange, hRoC, hRoker, -⟩ :=
    exceptional_fixed_rank_one_central_image .D4 K σ ⟨0, by decide⟩
  have hLo : ∀ c : K, c ∈ orbitField .D4 K σ ⟨0, by decide⟩ := fun c => by
    rw [mem_orbitField, show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide]
    exact hσ c
  let ιo : SL2 K →* SL2 (orbitField .D4 K σ ⟨0, by decide⟩) :=
    Matrix.SpecialLinearGroup.map ((RingHom.id K).codRestrict _ hLo)
  have hmem : ∀ k : ℕ, (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin ⟨0, by decide⟩) ∈
      outerSet := fun k => by
    have h := TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem ⟨0, by decide⟩) k
    have h3 : ∀ i : Fin TwistTag.D4.tag.rank, i ∈ TwistTag.D4.orbit ⟨0, by decide⟩ →
        i ∈ outerSet := by
      intro i hi
      rw [mem_outerSet]
      revert hi
      revert i
      decide
    exact h3 _ h
  refine ⟨Ro.comp ιo, fun A B h => CFSG.RankThree.Chevalley.SL2_map_injective _
    (CFSG.RankThree.Chevalley.injective_of_ker_scalar_of_charTwo hRoker h), ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    have h : Ro (ιo g) ∈ Ro.range := ⟨_, rfl⟩
    rw [hRorange] at h
    exact hRoC h
  · rintro _ ⟨g, rfl⟩
    have h : Ro (ιo g) ∈ Ro.range := ⟨_, rfl⟩
    rw [hRorange] at h
    refine (closure_le _).2 ?_ h
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact subset_closure ⟨_, hmem k, _, Or.inl rfl⟩
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact subset_closure ⟨_, hmem k, _, Or.inr rfl⟩

end CFSG.LargeExtraspecial.S8
