module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootParEq
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Radical


theorem orbitUnion_J0_eq :
    TwistTag.E6.orbitUnion TwE6LongRoot.J0 = {i : Fin TwistTag.E6.tag.rank | i ≠ 1} := by
  ext i
  rw [TwistTag.mem_orbitUnion, Set.mem_setOf_eq]
  simp only [TwE6LongRoot.J0, TwE6LongRoot.a2, Set.mem_setOf_eq]
  revert i
  decide

theorem mem_radicalRoots_std_iff {δ : Fin TwistTag.E6.tag.rank → ℤ} :
    δ ∈ parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion TwE6LongRoot.J0) ↔
      IsRoot TwistTag.E6.tag δ ∧ 1 ≤ δ 1 := by
  rw [orbitUnion_J0_eq, mem_parabolicRadicalRoots_iff]
  constructor
  · rintro ⟨hroot, hpos, i, hi, hδ⟩
    have hi1 : i = 1 := by simpa using hi
    subst hi1
    have := (IsRoot.height_pos_iff hroot).1 hpos 1
    exact ⟨hroot, by omega⟩
  · rintro ⟨hroot, h1⟩
    refine ⟨hroot, ?_, 1, by simp, by omega⟩
    rcases IsRoot.height_pos_or_neg hroot with h | h
    · exact h
    · have := (IsRoot.height_neg_iff hroot).1 h 1
      omega

theorem mem_rootSpan_of_baseChangeGL_mem {τ : Tag} {K : Type} [Field K] [Finite K]
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {g : ModGL τ K}
    (hg : baseChangeGL (algebraMap K (AlgebraicClosure K)) g ∈
      rootSpan τ (AlgebraicClosure K) S) :
    g ∈ rootSpan τ K S := by
  classical
  set L := AlgebraicClosure K
  set ι : K →+* L := algebraMap K L
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  let Fr : L →+* L := iterateFrobenius L (ringChar K) n
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : Fr.comp ι = ι := frobenius_comp_algebraMap Fr hFr
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset fun a ha => (hS a ha).1
  obtain ⟨m, α, hαS⟩ := hfin.fin_embedding
  have hcoll := (positive_root_collection τ L).1 S hS hclosed α α.injective hαS
  obtain ⟨c, -, hc⟩ := hcoll.surjOn hg
  have hc' : (List.ofFn fun i => pinnedX τ L (α i) (c i)).prod = baseChangeGL ι g := hc
  have hmap : ∀ (R : Type) [Field R] (f : R →+* L) (d : Fin m → R),
      baseChangeGL f (List.ofFn fun i => pinnedX τ R (α i) (d i)).prod =
        (List.ofFn fun i => pinnedX τ L (α i) (f (d i))).prod := by
    intro R _ f d
    rw [map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => baseChangeGL_pinnedX f (α i) (d i))
  have hmapL : ∀ d : Fin m → L,
      baseChangeGL Fr (List.ofFn fun i => pinnedX τ L (α i) (d i)).prod =
        (List.ofFn fun i => pinnedX τ L (α i) (Fr (d i))).prod := fun d => hmap L Fr d
  have h1 : baseChangeGL Fr (baseChangeGL ι g) = baseChangeGL ι g := by
    rw [baseChangeGL_baseChangeGL, hFrι]
  have h3 : (List.ofFn fun i => pinnedX τ L (α i) (Fr (c i))).prod =
      (List.ofFn fun i => pinnedX τ L (α i) (c i)).prod := by
    rw [← hmapL, hc', h1]
  have h4 : (fun i => Fr (c i)) = c := hcoll.injOn (Set.mem_univ _) (Set.mem_univ _) h3
  have h5 : ∀ i, ∃ d : K, ι d = c i := fun i =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact congrFun h4 i)
  choose d hd using h5
  have hg' : (List.ofFn fun i => pinnedX τ K (α i) (d i)).prod ∈ rootSpan τ K S := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    have hαi : α i ∈ S := hαS ▸ Set.mem_range_self i
    exact le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup τ K β) (α i) hαi le_rfl
      (Subgroup.subset_closure ⟨d i, rfl⟩)
  have hbc : baseChangeGL ι (List.ofFn fun i => pinnedX τ K (α i) (d i)).prod =
      baseChangeGL ι g := by
    rw [hmap K ι d, ← hc']
    congr 1
    exact List.ofFn_inj.2 (funext fun i => by rw [hd i])
  rw [← baseChangeGL_injective ι hbc]
  exact hg'

theorem mem_twE6LongRootRadical_std_iff (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (u : twistedE6RootGroup K σ) :
    u ∈ twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot) ↔
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        rootSpan TwistTag.E6.tag (AlgebraicClosure K)
          (parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion TwE6LongRoot.J0)) := by
  rw [TwE6LongRoot.radical_std_eq σ, Subgroup.mem_subgroupOf, graphFixedParabolicRadical,
    Subgroup.mem_inf]
  constructor
  · rintro ⟨hQ, -⟩
    exact CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan _ hQ
  · intro h
    refine ⟨?_, graphFixedRootGroup_le _ _ _ u.2⟩
    exact mem_rootSpan_of_baseChangeGL_mem (fun α hα => parabolicRadicalRoots_pos hα)
      (fun α hα β hβ a b ha hb hr =>
        add_mem_parabolicRadicalRoots (parabolicRadicalRoots_pos hα) hβ ha hb hr) h

end Radical

end CFSG.LieType.SeitzGeneration.ExcWideThree
