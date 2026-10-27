module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapCent
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapSpin

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le derivedSeriesOf derivedSeriesOf_le
  derivedSeriesOf_succ le_perfectCore_of_perfect perfectCore_le_derivedSeriesOf
  derivedSeriesOf_eq_map_derivedSeries)
open scoped commutatorElement Pointwise
open E7Neighbour

section GroupTheory

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_of_le_centralizer {A D : Subgroup G}
    (hAD : A ≤ centralizer (D : Set G)) {a₁ a₂ d₁ d₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) : ⁅a₁ * d₁, a₂ * d₂⁆ = ⁅a₁, a₂⁆ * ⁅d₁, d₂⁆ := by
  let φ : A × D →* G := MonoidHom.noncommCoprod A.subtype D.subtype
    (fun a d => (mem_centralizer_iff.1 (hAD a.2) d d.2).symm)
  exact (map_commutatorElement φ (⟨a₁, ha₁⟩, ⟨d₁, hd₁⟩) (⟨a₂, ha₂⟩, ⟨d₂, hd₂⟩)).symm

theorem commutator_sup_le_of_le_centralizer {A D : Subgroup G}
    (hAD : A ≤ centralizer (D : Set G)) : ⁅A ⊔ D, A ⊔ D⁆ ≤ ⁅A, A⁆ ⊔ ⁅D, D⁆ := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hAN : A ≤ normalizer (D : Set G) := hAD.trans (centralizer_le_normalizer _)
  have hg₁' : g₁ ∈ ((A ⊔ D : Subgroup G) : Set G) := hg₁
  have hg₂' : g₂ ∈ ((A ⊔ D : Subgroup G) : Set G) := hg₂
  rw [coe_mul_of_left_le_normalizer_right _ _ hAN] at hg₁' hg₂'
  obtain ⟨a₁, ha₁, d₁, hd₁, rfl⟩ := Set.mem_mul.1 hg₁'
  obtain ⟨a₂, ha₂, d₂, hd₂, rfl⟩ := Set.mem_mul.1 hg₂'
  rw [commutatorElement_mul_mul_of_le_centralizer hAD ha₁ ha₂ hd₁ hd₂]
  exact mul_mem (mem_sup_left (commutator_mem_commutator ha₁ ha₂))
    (mem_sup_right (commutator_mem_commutator hd₁ hd₂))

theorem perfectCore_sup_eq_of_isSolvable {M U : Subgroup G} (hMU : M ≤ centralizer (U : Set G))
    (hM : Group.IsSolvable M) (hU : ⁅U, U⁆ = U) : perfectCore (M ⊔ U) = U := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect le_sup_right hU)
  have hstep : ∀ n, derivedSeriesOf (M ⊔ U) n ≤ derivedSeriesOf M n ⊔ U := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [derivedSeriesOf_succ, derivedSeriesOf_succ]
      calc ⁅derivedSeriesOf (M ⊔ U) n, derivedSeriesOf (M ⊔ U) n⁆
          ≤ ⁅derivedSeriesOf M n ⊔ U, derivedSeriesOf M n ⊔ U⁆ := commutator_mono ih ih
        _ ≤ ⁅derivedSeriesOf M n, derivedSeriesOf M n⁆ ⊔ ⁅U, U⁆ :=
          commutator_sup_le_of_le_centralizer ((derivedSeriesOf_le M n).trans hMU)
        _ = ⁅derivedSeriesOf M n, derivedSeriesOf M n⁆ ⊔ U := by rw [hU]
  obtain ⟨n, hn⟩ := hM.solvable
  have hMn : derivedSeriesOf M n = ⊥ := by
    rw [derivedSeriesOf_eq_map_derivedSeries, hn, Subgroup.map_bot]
  calc perfectCore (M ⊔ U) ≤ derivedSeriesOf (M ⊔ U) n := perfectCore_le_derivedSeriesOf _ n
    _ ≤ derivedSeriesOf M n ⊔ U := hstep n
    _ = U := by rw [hMn, bot_sup_eq]

theorem inf_sup_eq_sup_inf_of_le {A B C : Subgroup G} (hAC : A ≤ C)
    (hAB : A ≤ normalizer (B : Set G)) : C ⊓ (A ⊔ B) = A ⊔ (C ⊓ B) := by
  have hABC : A ≤ normalizer ((C ⊓ B : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_iff.2 fun x => by
      rw [mem_inf, mem_inf, (mem_normalizer_iff.1 (hAB ha) x)]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨mul_mem (mul_mem (hAC ha) hx) (inv_mem (hAC ha)), hx'⟩
      · rintro ⟨hx, hx'⟩
        refine ⟨?_, hx'⟩
        have := mul_mem (mul_mem (inv_mem (hAC ha)) hx) (hAC ha)
        rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at this
  apply SetLike.coe_injective
  rw [coe_inf, coe_mul_of_left_le_normalizer_right _ _ hAB,
    coe_mul_of_left_le_normalizer_right _ _ hABC, inf_comm C B, mul_inf_assoc A B C hAC,
    Set.inter_comm]

theorem isSolvable_sup_of_le_centralizer {A B : Subgroup G} (hAB : A ≤ centralizer (B : Set G))
    (hA : Group.IsSolvable A) (hB : Group.IsSolvable B) : Group.IsSolvable (A ⊔ B : Subgroup G) := by
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hAB a.2) b b.2).symm
  let φ : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hrange : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have := Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  exact Group.isSolvable_of_surjective (f := (MulEquiv.subgroupCongr hrange).toMonoidHom)
    (MulEquiv.subgroupCongr hrange).surjective

end GroupTheory

section Transport


variable {K : Type} [Field K]

theorem map_conj_adjointGroup_of_mem {n : ModGL .E7 K} (hn : n ∈ adjointGroup .E7 K) :
    (adjointGroup .E7 K).map (MulAut.conj n).toMonoidHom = adjointGroup .E7 K :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer hn)

theorem map_conj_wordRepE7_rootPair (ω : List (Fin (Tag.rank .E7)))
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    (rootSubgroup .E7 K γ ⊔ rootSubgroup .E7 K (-γ)).map
        (MulAut.conj (wordRepE7 K ω : ModGL .E7 K)).toMonoidHom =
      rootSubgroup .E7 K ((coxeterSystem .E7).wordProd ω • γ) ⊔
        rootSubgroup .E7 K (-((coxeterSystem .E7).wordProd ω • γ)) := by
  rw [Subgroup.map_sup, coe_wordRepE7, map_conj_prod_weylElt_rootSubgroup K ω hγ,
    map_conj_prod_weylElt_rootSubgroup K ω (IsRoot.neg hγ), smul_neg]

theorem adjointGroup_inf_centralizer_rootPair_eq [CharP K 2] (ω : List (Fin (Tag.rank .E7)))
    {β : Fin (Tag.rank .E7) → ℤ} (hω : (coxeterSystem .E7).wordProd ω • highRoot .E7 = β) :
    adjointGroup .E7 K ⊓ centralizer ((rootSubgroup .E7 K β ⊔ rootSubgroup .E7 K (-β) :
        Subgroup (ModGL .E7 K)) : Set (ModGL .E7 K)) =
      rootSpan .E7 K (orthRoots β) := by
  have h := adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo (K := K) (τ := .E7)
    (Or.inr (Or.inl rfl))
  have h2 := congrArg (Subgroup.map (MulAut.conj (wordRepE7 K ω : ModGL .E7 K)).toMonoidHom) h
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    map_conj_adjointGroup_of_mem (wordRepE7 K ω).2, F4Pilot.map_centralizer_mulEquiv,
    EPilot.highRootSL2, map_conj_wordRepE7_rootPair ω (isRoot_highRoot _), hω,
    map_conj_wordRepE7_rootSpan ω (fun γ hγ => hγ.1), perpRoots_eq_orthRoots,
    image_smul_orthRoots, hω] at h2
  exact h2

theorem adjointGroup_inf_centralizer_rootPair_root_eq [CharP K 2] (N : E7Neighbour) :
    adjointGroup .E7 K ⊓ centralizer ((rootSubgroup .E7 K N.root ⊔ rootSubgroup .E7 K (-N.root) :
        Subgroup (ModGL .E7 K)) : Set (ModGL .E7 K)) =
      rootSpan .E7 K (orthRoots N.root) :=
  adjointGroup_inf_centralizer_rootPair_eq N.word N.weyl_smul_highRoot

theorem adjointGroup_inf_centralizer_rootPair_inf_centralizer_rootPair [CharP K 2]
    (hK1 : ∀ u : Kˣ, u = 1) {N N' : E7Neighbour} (h : N ≠ N') :
    adjointGroup .E7 K ⊓ centralizer ((rootSubgroup .E7 K N.root ⊔ rootSubgroup .E7 K (-N.root) :
        Subgroup (ModGL .E7 K)) : Set (ModGL .E7 K)) ⊓
      centralizer ((rootSubgroup .E7 K N'.root ⊔ rootSubgroup .E7 K (-N'.root) :
        Subgroup (ModGL .E7 K)) : Set (ModGL .E7 K)) =
      rootSpan .E7 K (orthRoots N.root ∩ orthRoots N'.root) := by
  have h1 : (coxeterSystem .E7).wordProd (overlapWord N N') • highRoot .E7 = N.root :=
    (overlapWeyl_smul h).1
  have h2 : (coxeterSystem .E7).wordProd (overlapWord N N') • d6HighRoot = N'.root :=
    (overlapWeyl_smul h).2.1
  have h3 : (fun α => (coxeterSystem .E7).wordProd (overlapWord N N') • α) ''
      parabolicRoots .E7 overlapNodes = orthRoots N.root ∩ orthRoots N'.root :=
    image_overlapWeyl_parabolicRoots h
  have h0 := adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_d6HighRootSL2 (K := K) hK1
  have h4 := congrArg (Subgroup.map (MulAut.conj
    (wordRepE7 K (overlapWord N N') : ModGL .E7 K)).toMonoidHom) h0
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    map_conj_adjointGroup_of_mem (wordRepE7 K _).2, F4Pilot.map_centralizer_mulEquiv,
    F4Pilot.map_centralizer_mulEquiv, EPilot.highRootSL2, d6HighRootSL2,
    map_conj_wordRepE7_rootPair _ (isRoot_highRoot _), map_conj_wordRepE7_rootPair _
      isRoot_d6HighRoot, h1, h2, map_conj_wordRepE7_rootSpan _ (fun γ hγ => hγ.1), h3] at h4
  exact h4

theorem levi_inf_levi_eq [CharP K 2] (hK1 : ∀ u : Kˣ, u = 1) {N N' : E7Neighbour} (h : N ≠ N') :
    N.levi K ⊓ N'.levi K =
      (rootSpan .E7 K (orthRoots N.root ∩ orthRoots N'.root)).subgroupOf (adjointGroup .E7 K) := by
  apply map_injective (adjointGroup .E7 K).subtype_injective
  rw [Subgroup.map_inf_eq _ _ _ (adjointGroup .E7 K).subtype_injective, levi, levi,
    subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _),
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _),
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _),
    ← adjointGroup_inf_centralizer_rootPair_root_eq N,
    ← adjointGroup_inf_centralizer_rootPair_root_eq N',
    ← adjointGroup_inf_centralizer_rootPair_inf_centralizer_rootPair hK1 h,
    inf_inf_inf_comm, inf_idem, inf_assoc]

end Transport

section Overlap


variable {K : Type} [Field K]

theorem subgroupOf_le_centralizer_subgroupOf {H₁ H₂ : Subgroup (ModGL .E7 K)}
    (h : H₁ ≤ centralizer (H₂ : Set (ModGL .E7 K))) :
    H₁.subgroupOf (adjointGroup .E7 K) ≤
      centralizer (H₂.subgroupOf (adjointGroup .E7 K) : Set (adjointGroup .E7 K)) :=
  fun _ hx => mem_centralizer_iff.2 fun _ hy =>
    Subtype.ext (mem_centralizer_iff.1 (h (mem_subgroupOf.1 hx)) _ (mem_subgroupOf.1 hy))

theorem centralizer_map_conj_rep_nonsplit [Finite K] [CharP K 2] (N : E7Neighbour)
    {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) :
    centralizer ((A.map (MulAut.conj (N.rep K)).toMonoidHom : Subgroup (adjointGroup .E7 K)) :
        Set (adjointGroup .E7 K)) = A.map (MulAut.conj (N.rep K)).toMonoidHom ⊔ N.levi K ∧
      A.map (MulAut.conj (N.rep K)).toMonoidHom ≤
        centralizer (N.levi K : Set (adjointGroup .E7 K)) := by
  obtain ⟨h1, -, h3⟩ := centralizer_nonsplit_E7_of_finite hAJ hA hcyc
  refine ⟨?_, ?_⟩
  · rw [← F4Pilot.map_centralizer_mulEquiv, h1, Subgroup.map_sup, map_conj_rep_perpLevi]
  · rw [← map_conj_rep_perpLevi N, ← F4Pilot.map_centralizer_mulEquiv]
    exact Subgroup.map_mono h3

theorem isSolvable_SL2_of_card_eq_two [Finite K] (hK2 : Nat.card K = 2) :
    Group.IsSolvable (SL2 K) := by
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
      (Or.inl hK2)
  exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective

theorem isSolvable_rootPair_subgroupOf [Finite K] [CharP K 2] (hK2 : Nat.card K = 2)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    Group.IsSolvable ((rootSubgroup .E7 K γ ⊔ rootSubgroup .E7 K (-γ)).subgroupOf
      (adjointGroup .E7 K)) := by
  obtain ⟨-, -, ⟨e, -⟩, -⟩ := even_Chevalley_pinned_root_SL2_maps .E7 K hγ
  have := isSolvable_SL2_of_card_eq_two hK2
  have e' := Subgroup.subgroupOfEquivOfLe (G := ModGL .E7 K)
    (sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ)))
  exact Group.isSolvable_of_surjective (f := (e'.symm.toMonoidHom.comp e.toMonoidHom))
    (e'.symm.surjective.comp e.surjective)

theorem rootSpan_union_E7 (S T : Set (Fin (Tag.rank .E7) → ℤ)) :
    rootSpan .E7 K (S ∪ T) = rootSpan .E7 K S ⊔ rootSpan .E7 K T := by
  simp only [rootSpan]
  exact iSup_union

theorem rootSpan_pair_E7 (γ : Fin (Tag.rank .E7) → ℤ) :
    rootSpan .E7 K {γ, -γ} = rootSubgroup .E7 K γ ⊔ rootSubgroup .E7 K (-γ) := by
  simp only [rootSpan]
  exact iSup_pair

theorem levi_inf_levi_eq_sup [CharP K 2] (hK1 : ∀ u : Kˣ, u = 1) {N N' : E7Neighbour}
    (h : N ≠ N') :
    N.levi K ⊓ N'.levi K =
      (rootSubgroup .E7 K (N.thirdRoot N') ⊔ rootSubgroup .E7 K (-N.thirdRoot N')).subgroupOf
          (adjointGroup .E7 K) ⊔ overlapSpanD4 K N N' := by
  have hset : orthRoots N.root ∩ orthRoots N'.root =
      {N.thirdRoot N', -N.thirdRoot N'} ∪ overlapRootsD4 N N' := by
    ext γ
    rw [mem_orthRoots_inter h]
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  rw [levi_inf_levi_eq hK1 h, hset, rootSpan_union_E7, rootSpan_pair_E7, overlapSpanD4,
    subgroupOf_sup (sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _))
      (EPilot.rootSpan_le_adjointGroup' _)]

theorem e7TwoOverlapInput (K : Type) [Field K] : E7TwoOverlapInput K := by
  intro hK2 A hAJ hA N N' h
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hK2]; rfl)
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  have hK1 : ∀ u : Kˣ, u = 1 := by
    classical
    have : Fintype K := Fintype.ofFinite K
    have h1 : Nat.card Kˣ = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK2]
    have := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun u => Subsingleton.elim u 1
  have hA3 : Nat.card A = 3 := by rw [hA, hK2]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA3
  set A' := A.map (MulAut.conj (N'.rep K)).toMonoidHom with hA'def
  obtain ⟨hcen, hA'D⟩ := centralizer_map_conj_rep_nonsplit N' hAJ hA hcyc
  have hA'N : A' ≤ N.levi K := map_conj_rep_le_levi_E7 hAJ h
  have hinter : N.levi K ⊓ centralizer (A' : Set (adjointGroup .E7 K)) =
      (A' ⊔ (rootSubgroup .E7 K (N.thirdRoot N') ⊔
        rootSubgroup .E7 K (-N.thirdRoot N')).subgroupOf (adjointGroup .E7 K)) ⊔
        overlapSpanD4 K N N' := by
    rw [hcen, inf_sup_eq_sup_inf_of_le hA'N (hA'D.trans (centralizer_le_normalizer _)),
      levi_inf_levi_eq_sup hK1 h, sup_assoc]
  have hc : N.thirdRoot N' ∈ orthRoots N'.root :=
    ⟨isRoot_thirdRoot h, (iform_root_thirdRoot h).2⟩
  have hJcN' : (rootSubgroup .E7 K (N.thirdRoot N') ⊔
      rootSubgroup .E7 K (-N.thirdRoot N')).subgroupOf (adjointGroup .E7 K) ≤ N'.levi K := by
    refine Subgroup.subgroupOf_mono _ (sup_le ?_ ?_)
    · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N'.root) => rootSubgroup .E7 K α) _ hc
    · exact le_iSup₂ (f := fun α (_ : α ∈ orthRoots N'.root) => rootSubgroup .E7 K α) _
        (neg_mem_orthRoots hc)
  have hUN' : overlapSpanD4 K N N' ≤ N'.levi K :=
    Subgroup.subgroupOf_mono _
      (rootSpan_mono_E7 (Set.inter_subset_left.trans Set.inter_subset_right))
  have hA'U : A' ≤ centralizer (overlapSpanD4 K N N' : Set (adjointGroup .E7 K)) :=
    hA'D.trans (centralizer_le hUN')
  have hJcU : (rootSubgroup .E7 K (N.thirdRoot N') ⊔
      rootSubgroup .E7 K (-N.thirdRoot N')).subgroupOf (adjointGroup .E7 K) ≤
      centralizer (overlapSpanD4 K N N' : Set (adjointGroup .E7 K)) := by
    refine subgroupOf_le_centralizer_subgroupOf ?_
    rw [le_centralizer_iff]
    exact rootSpan_le_centralizer_rootPair_E7 (isRoot_thirdRoot h) fun α hα =>
      ⟨hα.2.1, by rw [iform_comm]; exact hα.2.2⟩
  have hA'Jc : A' ≤ centralizer ((rootSubgroup .E7 K (N.thirdRoot N') ⊔
      rootSubgroup .E7 K (-N.thirdRoot N')).subgroupOf (adjointGroup .E7 K) :
        Set (adjointGroup .E7 K)) :=
    hA'D.trans (centralizer_le hJcN')
  have hA'cyc : IsCyclic A' := by
    have e : A ≃* A' := A.equivMapOfInjective _ (MulAut.conj (N'.rep K)).injective
    exact isCyclic_of_surjective e e.surjective
  have hsolv := isSolvable_sup_of_le_centralizer hA'Jc inferInstance
    (isSolvable_rootPair_subgroupOf hK2 (isRoot_thirdRoot h))
  refine ⟨?_, isSimpleGroup_overlapSpanD4 h, center_overlapSpanD4_eq_bot h⟩
  rw [hinter]
  exact perfectCore_sup_eq_of_isSolvable (sup_le hA'U hJcU) hsolv (commutator_overlapSpanD4 h)

end Overlap

end CFSG.SeitzReduction.E7Pilot
