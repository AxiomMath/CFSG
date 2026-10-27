module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance f4PilotAmalgamNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def amalgamRoots (J : Finset (Fin (Tag.rank .F4))) : Set (Fin (Tag.rank .F4) → ℤ) :=
  {γ | ∃ j ∈ J, γ = Pi.single j 1 ∨ γ = -Pi.single j 1}

@[expose] def orthRoots (θ : Fin (Tag.rank .F4) → ℤ) : Set (Fin (Tag.rank .F4) → ℤ) :=
  {γ | IsRoot .F4 γ ∧ iform θ γ = 0}

theorem isRoot_of_mem_amalgamRoots {J : Finset (Fin (Tag.rank .F4))}
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ amalgamRoots J) : IsRoot .F4 γ := by
  obtain ⟨j, -, rfl | rfl⟩ := hγ
  exacts [isRoot_single _ j, isRoot_neg_single _ j]

theorem amalgamRoots_mono {I J : Finset (Fin (Tag.rank .F4))} (h : I ⊆ J) :
    amalgamRoots I ⊆ amalgamRoots J := by
  rintro γ ⟨j, hj, hγ⟩
  exact ⟨j, h hj, hγ⟩

theorem iform_neg_right_amalgam (θ v : Fin (Tag.rank .F4) → ℤ) : iform θ (-v) = -iform θ v := by
  simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem amalgamRoots_subset_orthRoots_iff {J : Finset (Fin (Tag.rank .F4))}
    {θ : Fin (Tag.rank .F4) → ℤ} :
    amalgamRoots J ⊆ orthRoots θ ↔ ∀ j ∈ J, iform θ (Pi.single j 1) = 0 := by
  constructor
  · intro h j hj
    exact (h ⟨j, hj, Or.inl rfl⟩).2
  · rintro h γ ⟨j, hj, rfl | rfl⟩
    · exact ⟨isRoot_single _ j, h j hj⟩
    · refine ⟨isRoot_neg_single _ j, ?_⟩
      rw [iform_neg_right_amalgam, h j hj, neg_zero]

theorem iform_rootR_single_eq_zero_iff : ∀ j : Fin (Tag.rank .F4),
    iform rootR (Pi.single j 1) = 0 ↔ j ≠ 0 := by
  decide +kernel

theorem iform_rootS_single_eq_zero_iff : ∀ j : Fin (Tag.rank .F4),
    iform rootS (Pi.single j 1) = 0 ↔ j ≠ 3 := by
  decide +kernel

theorem iform_root1242_single_eq_zero_iff : ∀ j : Fin (Tag.rank .F4),
    iform root1242 (Pi.single j 1) = 0 ↔ j = 0 ∨ j = 3 := by
  decide +kernel

theorem c3LeviRoots_eq_orthRoots : c3LeviRoots = orthRoots rootR := by
  ext γ
  rw [mem_c3LeviRoots]
  change _ ↔ IsRoot .F4 γ ∧ iform rootR γ = 0
  rw [iform_rootR]
  exact and_congr_right fun _ => by
    change γ 0 = 0 ↔ 2 * γ 0 = 0
    omega

theorem b3LeviRoots_eq_orthRoots : b3LeviRoots = orthRoots rootS := by
  ext γ
  rw [mem_b3LeviRoots]
  change _ ↔ IsRoot .F4 γ ∧ iform rootS γ = 0
  rw [iform_rootS]
  rfl

theorem amalgamRoots_subset_c3LeviRoots_iff {J : Finset (Fin (Tag.rank .F4))} :
    amalgamRoots J ⊆ c3LeviRoots ↔ (0 : Fin (Tag.rank .F4)) ∉ J := by
  rw [c3LeviRoots_eq_orthRoots, amalgamRoots_subset_orthRoots_iff]
  constructor
  · intro h h0
    exact (iform_rootR_single_eq_zero_iff 0).1 (h 0 h0) rfl
  · intro h j hj
    exact (iform_rootR_single_eq_zero_iff j).2 fun hj0 => h (hj0 ▸ hj)

theorem amalgamRoots_subset_b3LeviRoots_iff {J : Finset (Fin (Tag.rank .F4))} :
    amalgamRoots J ⊆ b3LeviRoots ↔ (3 : Fin (Tag.rank .F4)) ∉ J := by
  rw [b3LeviRoots_eq_orthRoots, amalgamRoots_subset_orthRoots_iff]
  constructor
  · intro h h3
    exact (iform_rootS_single_eq_zero_iff 3).1 (h 3 h3) rfl
  · intro h j hj
    exact (iform_rootS_single_eq_zero_iff j).2 fun hj3 => h (hj3 ▸ hj)

theorem amalgamRoots_subset_orthRoots_root1242_iff {J : Finset (Fin (Tag.rank .F4))} :
    amalgamRoots J ⊆ orthRoots root1242 ↔ J ⊆ {0, 3} := by
  rw [amalgamRoots_subset_orthRoots_iff]
  refine forall₂_congr fun j _ => ?_
  rw [iform_root1242_single_eq_zero_iff, Finset.mem_insert, Finset.mem_singleton]

theorem eq_pair_zero_three {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J) : J = {0, 3} := by
  have hsub : ({0, 3} : Finset (Fin (Tag.rank .F4))) ⊆ J := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    exacts [h0, h3]
  have h2 : ({0, 3} : Finset (Fin (Tag.rank .F4))).card = 2 := by decide
  have hcard : J.card ≤ ({0, 3} : Finset (Fin (Tag.rank .F4))).card := by
    rw [h2]
    exact hJ
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

theorem amalgamRoots_subset_c3LeviRoots_or_b3LeviRoots_iff {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J.card ≤ 2) :
    amalgamRoots J ⊆ c3LeviRoots ∨ amalgamRoots J ⊆ b3LeviRoots ↔ J ≠ {0, 3} := by
  rw [amalgamRoots_subset_c3LeviRoots_iff, amalgamRoots_subset_b3LeviRoots_iff]
  constructor
  · rintro (h | h) rfl
    · exact h (by decide)
    · exact h (by decide)
  · intro hne
    by_contra! h
    exact hne (eq_pair_zero_three hJ h.1 h.2)

noncomputable abbrev w1242 : WeylGroup .F4 := simple .F4 1 * simple .F4 0

theorem w1242_smul_rootR : w1242 • rootR = root1242 := by
  rw [mul_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_eq_w1242 : (coxeterSystem .F4).wordProd [1, 0] = w1242 := by
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one]

theorem rootCertificate_root_val_eq_single :
    ∀ i : Fin (Tag.rank .F4), ∀ j : Fin (Tag.rank .F4),
      Tag.F4.rootCertificate.root (i : ℕ) j = (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) j := by
  decide +kernel

theorem wordPos_zero_one_check : ∀ i : Fin (Tag.rank .F4), ∀ j : Fin (Tag.rank .F4),
    Tag.F4.rootCertificate.root (wordPos Tag.F4.rootCertificate [0, 1] (i : ℕ)) j =
      reflect .F4 1 (reflect .F4 0 (Pi.single i 1)) j := by
  decide +kernel

section Weyl


theorem weylOfWord_eq_w1242 : weylOfWord .F4 [0, 1] = w1242 := by
  refine ext_single fun i => ?_
  have hi : (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) = Tag.F4.rootCertificate.root (i : ℕ) :=
    funext fun j => (rootCertificate_root_val_eq_single i j).symm
  have hlt : (i : ℕ) < 48 := lt_of_lt_of_le i.isLt (by decide)
  rw [hi, weylOfWord_smul_root_of_wordPos hlt rfl, ← hi, mul_smul, simple_smul,
    simple_smul]
  exact funext (wordPos_zero_one_check i)

theorem image_smul_orthRoots (w : WeylGroup .F4) (θ : Fin (Tag.rank .F4) → ℤ) :
    (fun α => w • α) '' orthRoots θ = orthRoots (w • θ) := by
  ext γ
  constructor
  · rintro ⟨α, ⟨hα, h0⟩, rfl⟩
    exact ⟨IsRoot.smul hα w, by rw [iform_smul, h0]⟩
  · rintro ⟨hγ, h0⟩
    refine ⟨w⁻¹ • γ, ⟨(isRoot_smul_iff w⁻¹).2 hγ, ?_⟩, smul_inv_smul w γ⟩
    rw [← iform_smul w, smul_inv_smul, h0]

theorem image_w1242_c3LeviRoots :
    (fun α => w1242 • α) '' c3LeviRoots = orthRoots root1242 := by
  rw [c3LeviRoots_eq_orthRoots, image_smul_orthRoots, w1242_smul_rootR]

end Weyl

section Rep


variable (K : Type) [Field K]

@[expose] noncomputable def n1242 : adjointGroup .F4 K :=
  CFSG.LieType.Chevalley.weylElement .F4 K 1 * CFSG.LieType.Chevalley.weylElement .F4 K 0

@[expose] noncomputable def C3Levi1242 : Subgroup (adjointGroup .F4 K) :=
  (rootSpan .F4 K (orthRoots root1242)).subgroupOf (adjointGroup .F4 K)

variable {K}

theorem coe_n1242 :
    (n1242 K : ModGL .F4 K) = ([1, 0].map fun i => weylElt .F4 K i 1).prod := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl


theorem map_conj_n1242_rootSubgroup {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    (rootSubgroup .F4 K γ).map (MulAut.conj (n1242 K : ModGL .F4 K)).toMonoidHom =
      rootSubgroup .F4 K (w1242 • γ) := by
  rw [coe_n1242, map_conj_prod_weylElt_rootSubgroup K [1, 0] hγ, wordProd_eq_w1242]

theorem map_conj_n1242_rootSpan {S : Set (Fin (Tag.rank .F4) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .F4 γ) :
    (rootSpan .F4 K S).map (MulAut.conj (n1242 K : ModGL .F4 K)).toMonoidHom =
      rootSpan .F4 K ((fun α => w1242 • α) '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun γ => iSup_congr fun hγ => map_conj_n1242_rootSubgroup (hS γ hγ)

theorem map_conj_n1242_map_subtype (H : Subgroup (adjointGroup .F4 K)) :
    (H.map (MulAut.conj (n1242 K)).toMonoidHom).map (adjointGroup .F4 K).subtype =
      (H.map (adjointGroup .F4 K).subtype).map
        (MulAut.conj (n1242 K : ModGL .F4 K)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem rootSpan_le_adjointGroup_F4 (S : Set (Fin (Tag.rank .F4) → ℤ)) :
    rootSpan .F4 K S ≤ adjointGroup .F4 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem map_conj_n1242_subgroupOf_rootSpan {S : Set (Fin (Tag.rank .F4) → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .F4 γ) :
    ((rootSpan .F4 K S).subgroupOf (adjointGroup .F4 K)).map (MulAut.conj (n1242 K)).toMonoidHom =
      (rootSpan .F4 K ((fun α => w1242 • α) '' S)).subgroupOf (adjointGroup .F4 K) := by
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_conj_n1242_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (rootSpan_le_adjointGroup_F4 S), inf_of_le_left (rootSpan_le_adjointGroup_F4 _),
    map_conj_n1242_rootSpan hS]

theorem map_conj_n1242_C3Levi :
    (C3Levi K).map (MulAut.conj (n1242 K)).toMonoidHom = C3Levi1242 K := by
  rw [C3Levi, map_conj_n1242_subgroupOf_rootSpan fun γ hγ => (mem_c3LeviRoots.1 hγ).1,
    image_w1242_c3LeviRoots]
  rfl

theorem map_conj_n1242_rootSubgroup_sup :
    (rootSubgroup .F4 K rootR ⊔ rootSubgroup .F4 K (-rootR)).map
        (MulAut.conj (n1242 K : ModGL .F4 K)).toMonoidHom =
      rootSubgroup .F4 K root1242 ⊔ rootSubgroup .F4 K (-root1242) := by
  rw [Subgroup.map_sup, map_conj_n1242_rootSubgroup isRoot_rootR,
    map_conj_n1242_rootSubgroup (IsRoot.neg isRoot_rootR), smul_neg, w1242_smul_rootR]

theorem map_conj_n1242_rootSL2 :
    ((rootSubgroup .F4 K rootR ⊔ rootSubgroup .F4 K (-rootR)).subgroupOf
        (adjointGroup .F4 K)).map (MulAut.conj (n1242 K)).toMonoidHom =
      (rootSubgroup .F4 K root1242 ⊔ rootSubgroup .F4 K (-root1242)).subgroupOf
        (adjointGroup .F4 K) := by
  have hle : ∀ γ : Fin (Tag.rank .F4) → ℤ,
      rootSubgroup .F4 K γ ⊔ rootSubgroup .F4 K (-γ) ≤ adjointGroup .F4 K :=
    fun γ => sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_conj_n1242_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hle _), inf_of_le_left (hle _), map_conj_n1242_rootSubgroup_sup]

end Rep

section Placement


variable {K : Type} [Field K]

theorem rootSpan_mono_F4 {S T : Set (Fin (Tag.rank .F4) → ℤ)} (h : S ⊆ T) :
    rootSpan .F4 K S ≤ rootSpan .F4 K T :=
  iSup₂_le fun α hα => le_iSup₂_of_le (f := fun α (_ : α ∈ T) => rootSubgroup .F4 K α) α (h hα)
    le_rfl

theorem rootSpan_amalgamRoots_le_orthRoots {J : Finset (Fin (Tag.rank .F4))}
    {θ : Fin (Tag.rank .F4) → ℤ} (h : ∀ j ∈ J, iform θ (Pi.single j 1) = 0) :
    rootSpan .F4 K (amalgamRoots J) ≤ rootSpan .F4 K (orthRoots θ) :=
  rootSpan_mono_F4 (amalgamRoots_subset_orthRoots_iff.2 h)

theorem rootSpan_amalgamRoots_le_c3LeviRoots {J : Finset (Fin (Tag.rank .F4))}
    (h : (0 : Fin (Tag.rank .F4)) ∉ J) :
    rootSpan .F4 K (amalgamRoots J) ≤ rootSpan .F4 K c3LeviRoots :=
  rootSpan_mono_F4 (amalgamRoots_subset_c3LeviRoots_iff.2 h)

theorem rootSpan_amalgamRoots_le_b3LeviRoots {J : Finset (Fin (Tag.rank .F4))}
    (h : (3 : Fin (Tag.rank .F4)) ∉ J) :
    rootSpan .F4 K (amalgamRoots J) ≤ rootSpan .F4 K b3LeviRoots :=
  rootSpan_mono_F4 (amalgamRoots_subset_b3LeviRoots_iff.2 h)

theorem rootSpan_amalgamRoots_le_orthRoots_root1242 {J : Finset (Fin (Tag.rank .F4))}
    (h : J ⊆ {0, 3}) :
    rootSpan .F4 K (amalgamRoots J) ≤ rootSpan .F4 K (orthRoots root1242) :=
  rootSpan_mono_F4 (amalgamRoots_subset_orthRoots_root1242_iff.2 h)


theorem map_subtype_levi_f4Datum (J : Finset (Fin (Tag.rank .F4))) :
    (CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (amalgamRoots J) := by
  have hj : ∀ j : Fin (Tag.rank .F4),
      (CFSG.LieType.CurtisTits.rankOne (f4Datum K).rootGroup j).map (adjointGroup .F4 K).subtype =
        rootSubgroup .F4 K (Pi.single j 1) ⊔ rootSubgroup .F4 K (-Pi.single j 1) := fun j => by
    rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup, map_subtype_rootGroup (isRoot_single _ j),
      map_subtype_rootGroup (isRoot_neg_single _ j)]
  rw [CFSG.LieType.CurtisTits.levi, Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup, hj]
  apply le_antisymm
  · refine iSup₂_le fun j hj => sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .F4 K α)
        (Pi.single j 1) ⟨j, hj, Or.inl rfl⟩ le_rfl
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .F4 K α)
        (-Pi.single j 1) ⟨j, hj, Or.inr rfl⟩ le_rfl
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨j, hj, rfl | rfl⟩ := hγ
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .F4 K (Pi.single j 1) ⊔ rootSubgroup .F4 K (-Pi.single j 1)) j hj le_sup_left
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .F4 K (Pi.single j 1) ⊔ rootSubgroup .F4 K (-Pi.single j 1)) j hj le_sup_right

theorem levi_f4Datum_eq (J : Finset (Fin (Tag.rank .F4))) :
    CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J =
      (rootSpan .F4 K (amalgamRoots J)).subgroupOf (adjointGroup .F4 K) := by
  rw [← map_subtype_levi_f4Datum]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup .F4 K).subtype_injective _).symm

theorem levi_le_orthRoots {J : Finset (Fin (Tag.rank .F4))} {θ : Fin (Tag.rank .F4) → ℤ}
    (h : ∀ j ∈ J, iform θ (Pi.single j 1) = 0) :
    CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J ≤
      (rootSpan .F4 K (orthRoots θ)).subgroupOf (adjointGroup .F4 K) := by
  rw [levi_f4Datum_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_amalgamRoots_le_orthRoots h)

theorem levi_le_C3Levi {J : Finset (Fin (Tag.rank .F4))} (h : (0 : Fin (Tag.rank .F4)) ∉ J) :
    CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J ≤ C3Levi K := by
  rw [levi_f4Datum_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_amalgamRoots_le_c3LeviRoots h)

theorem levi_le_B3Levi {J : Finset (Fin (Tag.rank .F4))} (h : (3 : Fin (Tag.rank .F4)) ∉ J) :
    CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J ≤ B3Levi K := by
  rw [levi_f4Datum_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_amalgamRoots_le_b3LeviRoots h)

theorem levi_le_C3Levi1242 {J : Finset (Fin (Tag.rank .F4))} (h : J ⊆ {0, 3}) :
    CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J ≤ C3Levi1242 K := by
  rw [levi_f4Datum_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_amalgamRoots_le_orthRoots_root1242 h)

theorem levi_le_map_conj_n1242_C3Levi {J : Finset (Fin (Tag.rank .F4))} (h : J ⊆ {0, 3}) :
    CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J ≤
      (C3Levi K).map (MulAut.conj (n1242 K)).toMonoidHom := by
  rw [map_conj_n1242_C3Levi]
  exact levi_le_C3Levi1242 h

theorem map_conj_n1242_rootGroup {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((f4Datum K).rootGroup γ).map (MulAut.conj (n1242 K)).toMonoidHom =
      (f4Datum K).rootGroup (w1242 • γ) := by
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [map_conj_n1242_map_subtype, map_subtype_rootGroup hγ,
    map_subtype_rootGroup (IsRoot.smul hγ w1242), map_conj_n1242_rootSubgroup hγ]

theorem map_conj_n1242_levi (J : Finset (Fin (Tag.rank .F4))) :
    (CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J).map
        (MulAut.conj (n1242 K)).toMonoidHom =
      (rootSpan .F4 K ((fun α => w1242 • α) '' amalgamRoots J)).subgroupOf (adjointGroup .F4 K) := by
  rw [levi_f4Datum_eq, map_conj_n1242_subgroupOf_rootSpan fun γ hγ => isRoot_of_mem_amalgamRoots hγ]

theorem image_w1242_amalgamRoots_one_three :
    (fun α => w1242 • α) '' amalgamRoots {1, 3} = amalgamRoots {0, 3} := by
  have h1 : w1242 • (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) = Pi.single 0 1 := by
    rw [mul_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have h3 : w1242 • (Pi.single 3 1 : Fin (Tag.rank .F4) → ℤ) = Pi.single 3 1 := by
    rw [mul_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  ext γ
  simp only [Set.mem_image, amalgamRoots, Set.mem_ofPred_eq, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨α, ⟨j, hj, rfl | rfl⟩, rfl⟩ <;> rcases hj with rfl | rfl
    · exact ⟨0, Or.inl rfl, Or.inl h1⟩
    · exact ⟨3, Or.inr rfl, Or.inl h3⟩
    · exact ⟨0, Or.inl rfl, Or.inr (by rw [smul_neg, h1])⟩
    · exact ⟨3, Or.inr rfl, Or.inr (by rw [smul_neg, h3])⟩
  · rintro ⟨j, hj, rfl | rfl⟩ <;> rcases hj with rfl | rfl
    · exact ⟨Pi.single 1 1, ⟨1, Or.inl rfl, Or.inl rfl⟩, h1⟩
    · exact ⟨Pi.single 3 1, ⟨3, Or.inr rfl, Or.inl rfl⟩, h3⟩
    · exact ⟨-Pi.single 1 1, ⟨1, Or.inl rfl, Or.inr rfl⟩, by rw [smul_neg, h1]⟩
    · exact ⟨-Pi.single 3 1, ⟨3, Or.inr rfl, Or.inr rfl⟩, by rw [smul_neg, h3]⟩

theorem map_conj_n1242_levi_one_three :
    (CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup {1, 3}).map
        (MulAut.conj (n1242 K)).toMonoidHom =
      CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup {0, 3} := by
  rw [map_conj_n1242_levi, image_w1242_amalgamRoots_one_three, levi_f4Datum_eq]

end Placement

inductive AmalgamNeighbour
  | X
  | Y
  | X'
  deriving DecidableEq

namespace AmalgamNeighbour

@[expose] def root : AmalgamNeighbour → Fin (Tag.rank .F4) → ℤ
  | X => rootR
  | Y => rootS
  | X' => root1242

@[expose] def nodes : AmalgamNeighbour → Finset (Fin (Tag.rank .F4))
  | X => {1, 2, 3}
  | Y => {0, 1, 2}
  | X' => {0, 3}


@[expose] noncomputable def levi (K : Type) [Field K] :
    AmalgamNeighbour → Subgroup (adjointGroup .F4 K)
  | X => C3Levi K
  | Y => B3Levi K
  | X' => C3Levi1242 K

theorem iform_root_single_eq_zero_iff (N : AmalgamNeighbour) (j : Fin (Tag.rank .F4)) :
    iform N.root (Pi.single j 1) = 0 ↔ j ∈ N.nodes := by
  revert j
  cases N <;> decide +kernel

theorem levi_eq (K : Type) [Field K] (N : AmalgamNeighbour) :
    N.levi K = (rootSpan .F4 K (orthRoots N.root)).subgroupOf (adjointGroup .F4 K) := by
  cases N
  · rw [levi, C3Levi, c3LeviRoots_eq_orthRoots]
    rfl
  · rw [levi, B3Levi, b3LeviRoots_eq_orthRoots]
    rfl
  · rfl

end AmalgamNeighbour

@[expose] def amalgamPlacement (J : Finset (Fin (Tag.rank .F4))) : AmalgamNeighbour :=
  if (0 : Fin (Tag.rank .F4)) ∈ J then (if (3 : Fin (Tag.rank .F4)) ∈ J then .X' else .Y) else .X

theorem amalgamPlacement_of_zero_not_mem {J : Finset (Fin (Tag.rank .F4))}
    (h0 : (0 : Fin (Tag.rank .F4)) ∉ J) : amalgamPlacement J = .X := by
  rw [amalgamPlacement, ite_eq_right h0]

theorem amalgamPlacement_of_three_not_mem {J : Finset (Fin (Tag.rank .F4))}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h3 : (3 : Fin (Tag.rank .F4)) ∉ J) :
    amalgamPlacement J = .Y := by
  rw [amalgamPlacement, ite_eq_left h0, ite_eq_right h3]

theorem amalgamPlacement_of_mem {J : Finset (Fin (Tag.rank .F4))}
    (h0 : (0 : Fin (Tag.rank .F4)) ∈ J) (h3 : (3 : Fin (Tag.rank .F4)) ∈ J) :
    amalgamPlacement J = .X' := by
  rw [amalgamPlacement, ite_eq_left h0, ite_eq_left h3]

theorem mem_nodes_X_of_ne {j : Fin (Tag.rank .F4)} (h : j ≠ 0) : j ∈ AmalgamNeighbour.X.nodes := by
  revert j
  decide

theorem mem_nodes_Y_of_ne {j : Fin (Tag.rank .F4)} (h : j ≠ 3) : j ∈ AmalgamNeighbour.Y.nodes := by
  revert j
  decide

theorem subset_nodes_amalgamPlacement {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) :
    J ⊆ (amalgamPlacement J).nodes := by
  by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J
  · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J
    · rw [amalgamPlacement_of_mem h0 h3, eq_pair_zero_three hJ h0 h3]
      exact subset_rfl
    · rw [amalgamPlacement_of_three_not_mem h0 h3]
      exact fun j hj => mem_nodes_Y_of_ne fun h => h3 (h ▸ hj)
  · rw [amalgamPlacement_of_zero_not_mem h0]
    exact fun j hj => mem_nodes_X_of_ne fun h => h0 (h ▸ hj)

theorem amalgamRoots_subset_orthRoots_placement {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J.card ≤ 2) : amalgamRoots J ⊆ orthRoots (amalgamPlacement J).root :=
  amalgamRoots_subset_orthRoots_iff.2 fun j hj =>
    ((amalgamPlacement J).iform_root_single_eq_zero_iff j).2 (subset_nodes_amalgamPlacement hJ hj)

section PlacementLevi


variable {K : Type} [Field K]

theorem levi_le_neighbourLevi {J : Finset (Fin (Tag.rank .F4))} {N : AmalgamNeighbour}
    (h : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (f4Datum K).rootGroup J ≤ N.levi K := by
  rw [AmalgamNeighbour.levi_eq]
  exact levi_le_orthRoots fun j hj => (N.iform_root_single_eq_zero_iff j).2 (h hj)

theorem leviAmalgam_le_placementLevi (J : {J : Finset (Fin (f4Datum K).rank) // J.card ≤ 2}) :
    (f4Datum K).leviAmalgam J ≤ (amalgamPlacement J.1).levi K :=
  levi_le_neighbourLevi (subset_nodes_amalgamPlacement J.2)

theorem leviAmalgam_le_C3Levi_or_B3Levi_or_conj
    (J : {J : Finset (Fin (f4Datum K).rank) // J.card ≤ 2}) :
    ((0 : Fin (Tag.rank .F4)) ∉ J.1 → (f4Datum K).leviAmalgam J ≤ C3Levi K) ∧
    ((3 : Fin (Tag.rank .F4)) ∉ J.1 → (f4Datum K).leviAmalgam J ≤ B3Levi K) ∧
    (J.1 = {0, 3} →
      (f4Datum K).leviAmalgam J ≤ (C3Levi K).map (MulAut.conj (n1242 K)).toMonoidHom) ∧
    ((f4Datum K).leviAmalgam J ≤ C3Levi K ∨ (f4Datum K).leviAmalgam J ≤ B3Levi K ∨
      (f4Datum K).leviAmalgam J ≤ (C3Levi K).map (MulAut.conj (n1242 K)).toMonoidHom) := by
  refine ⟨levi_le_C3Levi, levi_le_B3Levi, fun h => levi_le_map_conj_n1242_C3Levi h.le, ?_⟩
  have h := leviAmalgam_le_placementLevi J
  by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
  · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
    · rw [amalgamPlacement_of_mem h0 h3] at h
      rw [map_conj_n1242_C3Levi]
      exact Or.inr (Or.inr h)
    · rw [amalgamPlacement_of_three_not_mem h0 h3] at h
      exact Or.inr (Or.inl h)
  · rw [amalgamPlacement_of_zero_not_mem h0] at h
    exact Or.inl h

end PlacementLevi

section Universal


theorem lieUniversal_leviAmalgam_le_placementLevi (n p f : ℕ) (hp : p.Prime) [Fact p.Prime]
    (J : {J : Finset (Fin (CFSG.LieType.Universal.lieUniversal .F4 n p f hp).D.rank) //
      J.card ≤ 2}) :
    (CFSG.LieType.Universal.lieUniversal .F4 n p f hp).D.leviAmalgam J ≤
      (amalgamPlacement J.1).levi (GaloisField p f) :=
  leviAmalgam_le_placementLevi (K := GaloisField p f) J

end Universal

end CFSG.SeitzReduction.F4Pilot
