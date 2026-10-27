module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviTori
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RootSpace
open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect)

local instance e6PilotAlignLeviNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def corootTupleSet (A : Subgroup Kˣ) (J : Finset (Fin (Tag.rank .E6))) :
    Set (Fin (Tag.rank .E6) → Kˣ) :=
  {a | ∃ δ, IsRoot .E6 δ ∧ (∀ j ∈ J, iform δ (Pi.single j 1) = 0) ∧ ∃ c ∈ A, corootTuple δ c = a}

theorem coroot_pair_check : ∀ m ∈ ([3, 4] : List ℤ), ∀ δ ∈ rootFinset .E6, ∀ δ' ∈ rootFinset .E6,
    (∀ i : Fin (Tag.rank .E6), m ∣ ∑ j, (δ' j - δ j) * Tag.cartan .E6 j i) → δ' = δ := by
  decide +kernel

theorem iform_sub_single_E6 (δ δ' : Fin (Tag.rank .E6) → ℤ) (i : Fin (Tag.rank .E6)) :
    iform δ' (Pi.single i 1) - iform δ (Pi.single i 1) =
      ∑ j, (δ' j - δ j) * Tag.cartan .E6 j i := by
  rw [iform_single_right_E6, iform_single_right_E6, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_inner_ofLattice_eq_iform_E6 :
    ∃ c : ℝ, 0 < c ∧ ∀ u v : Fin (Tag.rank .E6) → ℤ,
      inner ℝ (ofLattice u) (ofLattice v) = c * (iform u v : ℝ) := by
  obtain ⟨c, hc, h⟩ := exists_inner_eq_smul .E6
  refine ⟨c, hc, fun u v => ?_⟩
  rw [h]
  congr 1
  simp only [ofLattice_apply, iform, Int.cast_sum, Int.cast_mul]

section Pair

theorem eq_of_dvd_iform_sub {m : ℕ} (hm : 3 ≤ m) {δ δ' : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (hδ' : IsRoot .E6 δ')
    (h : ∀ i, (m : ℤ) ∣ iform δ' (Pi.single i 1) - iform δ (Pi.single i 1)) : δ' = δ := by
  by_cases hm5 : 5 ≤ m
  · have h0 : ∀ i, iform δ' (Pi.single i 1) - iform δ (Pi.single i 1) = 0 := by
      intro i
      refine Int.eq_zero_of_abs_lt_dvd (h i) ?_
      have h1 := abs_le.1 (abs_iform_le_two hδ' (isRoot_single _ i))
      have h2 := abs_le.1 (abs_iform_le_two hδ (isRoot_single _ i))
      have : (5 : ℤ) ≤ m := by exact_mod_cast hm5
      rw [abs_lt]
      constructor <;> omega
    refine coroot_pair_check 3 (by simp) δ (mem_rootFinset.2 hδ) δ' (mem_rootFinset.2 hδ')
      fun i => ?_
    rw [← iform_sub_single_E6, h0 i]
    exact dvd_zero _
  · have hmem : (m : ℤ) ∈ ([3, 4] : List ℤ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    refine coroot_pair_check _ hmem δ (mem_rootFinset.2 hδ) δ' (mem_rootFinset.2 hδ') fun i => ?_
    rw [← iform_sub_single_E6]
    exact h i

end Pair

section KernelWeyl

theorem coeff_eq_zero_of_mem_toralSetKernel_corootTupleSet {A : Subgroup Kˣ}
    (hA : 3 ≤ Nat.card A) {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ F4Pilot.toralSetKernel (corootTupleSet A J)) :
    ∀ i ∉ J, γ i = 0 := by
  obtain ⟨c, hcA, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  refine coeff_eq_zero_of_forall_iform_eq_zero hJ hγ.1 fun δ hδ hδJ => ?_
  have h1 := hγ.2 _ ⟨δ, hδ, hδJ, c, hcA, rfl⟩
  rw [rootChar_corootTuple, ← orderOf_dvd_iff_zpow_eq_one, hc] at h1
  rw [iform_comm]
  refine Int.eq_zero_of_abs_lt_dvd h1 ?_
  have := abs_le.1 (abs_iform_le_two hδ hγ.1)
  have h3 : (3 : ℤ) ≤ ((Nat.card A : ℕ) : ℤ) := by exact_mod_cast hA
  rw [abs_lt]
  constructor <;> omega

theorem smul_eq_of_mem_rootCharStabilizer_corootTuple {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) {c : Kˣ} (hc : 3 ≤ orderOf c) {w : WeylGroup .E6}
    (hw : w ∈ rootCharStabilizer (corootTuple δ c)) : w • δ = δ := by
  have hdvd : ∀ i, ((orderOf c : ℕ) : ℤ) ∣
      iform δ (Pi.single i 1) - iform (w • δ) (Pi.single i 1) := by
    intro i
    have h1 := hw (w⁻¹ • Pi.single i 1)
    rw [smul_inv_smul, rootChar_corootTuple, rootChar_corootTuple] at h1
    have h2 : iform δ (w⁻¹ • Pi.single i 1) = iform (w • δ) (Pi.single i 1) := by
      rw [← iform_smul w, smul_inv_smul]
    rw [h2] at h1
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1, mul_inv_cancel]
  exact (eq_of_dvd_iform_sub hc (IsRoot.smul hδ w) hδ hdvd).symm

theorem smul_apply_eq_of_forall_smul_eq {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {w : WeylGroup .E6}
    (hw : ∀ δ, IsRoot .E6 δ → (∀ j ∈ J, iform δ (Pi.single j 1) = 0) → w • δ = δ) :
    ∀ v : Fin (Tag.rank .E6) → ℤ, ∀ i ∉ J, (w • v) i = v i := by
  have hfix : w • perpVec J = perpVec J := by
    rw [perpVec, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hδ, hδJ⟩ := isRoot_of_mem_perpPositions hk
    rw [smul_comm, hw _ hδ hδJ]
  have hstab : w ∈ weylStabilizer .E6 (ofLattice (perpVec J)) := by
    rw [mem_weylStabilizer, weylAct_apply, weylLinear_ofLattice, hfix]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E6).2.2.2.2.2] at hstab
  obtain ⟨c0, hc0, hinner⟩ := exists_inner_ofLattice_eq_iform_E6
  have hle : Subgroup.closure {s | ∃ α, IsRoot .E6 α ∧
      inner ℝ (ofLattice α) (ofLattice (perpVec J)) = 0 ∧ s = rootReflection α} ≤
      parabolicWeylGroup .E6 (J : Set (Fin (Tag.rank .E6))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨α, hα, h0, rfl⟩
    have hα0 : iform α (perpVec J) = 0 := by
      rw [hinner] at h0
      exact_mod_cast (mul_eq_zero.1 h0).resolve_left hc0.ne'
    have hαJ := perpVec_check J hJ α (mem_rootFinset.2 hα) hα0
    rw [(parabolic_Weyl_coordinate_stabilizer .E6 _).1]
    intro v i hi
    rw [rootReflection_smul hα, Pi.sub_apply, Pi.smul_apply, hαJ i hi, smul_zero, sub_zero]
  have hwJ := hle hstab
  rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer .E6 _).1] at hwJ
  exact fun v i hi => hwJ v i hi

theorem smul_apply_eq_of_mem_rootCharStabilizer_corootTupleSet {A : Subgroup Kˣ}
    (hA : 3 ≤ Nat.card A) {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {w : WeylGroup .E6} (hw : ∀ a ∈ corootTupleSet A J, w ∈ rootCharStabilizer a) :
    ∀ v : Fin (Tag.rank .E6) → ℤ, ∀ i ∉ J, (w • v) i = v i := by
  obtain ⟨c, hcA, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  refine smul_apply_eq_of_forall_smul_eq hJ fun δ hδ hδJ => ?_
  exact smul_eq_of_mem_rootCharStabilizer_corootTuple hδ (hc ▸ hA)
    (hw _ ⟨δ, hδ, hδJ, c, hcA, rfl⟩)

end KernelWeyl

section Points

theorem rootSpan_amalgamRoots_le_inf_centralizer {J : Finset (Fin (Tag.rank .E6))}
    {T : Subgroup (ModGL .E6 K)} (hT : T ≤ leviTorus K J) :
    rootSpan .E6 K (amalgamRoots J) ≤
      adjointGroup .E6 K ⊓ centralizer (T : Set (ModGL .E6 K)) :=
  le_inf (rootSpan_le_adjointGroup_E6 _)
    ((rootSpan_amalgamRoots_le_centralizer_leviTorus J).trans
      (centralizer_le (SetLike.coe_subset_coe.2 hT)))

theorem commutator_rootSpan_amalgamRoots_eq_E6 {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    (J : Finset (Fin (Tag.rank .E6))) :
    ⁅rootSpan .E6 K (amalgamRoots J), rootSpan .E6 K (amalgamRoots J)⁆ =
      rootSpan .E6 K (amalgamRoots J) := by
  obtain ⟨c, -, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  exact F4Pilot.commutator_rootSpan_signedSimpleRoots_eq
    (F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf (hc ▸ hA)).2 _

end Points

section Coroot

theorem rootDiagUnit_mem_leviTorus_inf_of_mem_corootTupleSet {A : Subgroup Kˣ}
    {J : Finset (Fin (Tag.rank .E6))} {a : Fin (Tag.rank .E6) → Kˣ}
    (ha : a ∈ corootTupleSet A J) :
    rootDiagUnit .E6 a ∈ leviTorus K J ⊓ adjointGroup .E6 K := by
  obtain ⟨δ, -, hδJ, c, -, rfl⟩ := ha
  exact ⟨rootDiagUnit_corootTuple_mem_leviTorus hδJ c,
    rootDiagUnit_corootTuple_mem_adjointGroup δ c⟩

end Coroot

section Main

theorem perfectCore_le_rootSpan_amalgamRoots_of_forall_conj_eq {A : Subgroup Kˣ}
    (hA : 3 ≤ Nat.card A) {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {H : Subgroup (ModGL .E6 K)}
    (hH : ∀ g ∈ H, g ∈ adjointGroup .E6 K ∧
      ∀ a ∈ corootTupleSet A J, rootDiagUnit .E6 a * g * (rootDiagUnit .E6 a)⁻¹ = g) :
    perfectCore H ≤ rootSpan .E6 K (amalgamRoots J) :=
  F4Pilot.perfectCore_le_rootSpan_of_forall_conj_eq (corootTupleSet A J)
    (J : Set (Fin (Tag.rank .E6)))
    (fun _ hγ _ => coeff_eq_zero_of_mem_toralSetKernel_corootTupleSet hA hJ hγ)
    (fun _ hw => smul_apply_eq_of_mem_rootCharStabilizer_corootTupleSet hA hJ hw) hH

theorem perfectCore_inf_centralizer_eq_of_le {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) {T : Subgroup (ModGL .E6 K)}
    (hT : T ≤ leviTorus K J) (hTA : ∀ a ∈ corootTupleSet A J, rootDiagUnit .E6 a ∈ T) :
    perfectCore (adjointGroup .E6 K ⊓ centralizer (T : Set (ModGL .E6 K))) =
      rootSpan .E6 K (amalgamRoots J) := by
  refine le_antisymm (perfectCore_le_rootSpan_amalgamRoots_of_forall_conj_eq hA hJ
    fun g hg => ⟨(mem_inf.1 hg).1, fun a ha => ?_⟩)
    (le_perfectCore_of_perfect (rootSpan_amalgamRoots_le_inf_centralizer hT)
      (commutator_rootSpan_amalgamRoots_eq_E6 hA J))
  have h := mem_centralizer_iff.1 (mem_inf.1 hg).2 _ (hTA a ha)
  rw [h, mul_inv_cancel_right]

theorem perfectCore_levi_inf_centralizer_eq_of_le {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) (N : E6Neighbour) (hJN : J ⊆ N.nodes)
    {T : Subgroup (ModGL .E6 K)} (hT : T ≤ leviTorus K J)
    (hTA : ∀ a ∈ corootTupleSet A J, rootDiagUnit .E6 a ∈ T) :
    perfectCore ((N.levi K).map (adjointGroup .E6 K).subtype ⊓
        centralizer (T : Set (ModGL .E6 K))) =
      rootSpan .E6 K (amalgamRoots J) := by
  refine le_antisymm (perfectCore_le_rootSpan_amalgamRoots_of_forall_conj_eq hA hJ
    fun g hg => ⟨map_subtype_le _ (mem_inf.1 hg).1, fun a ha => ?_⟩)
    (le_perfectCore_of_perfect (le_inf ?_
      ((rootSpan_amalgamRoots_le_inf_centralizer hT).trans inf_le_right))
      (commutator_rootSpan_amalgamRoots_eq_E6 hA J))
  · have h := mem_centralizer_iff.1 (mem_inf.1 hg).2 _ (hTA a ha)
    rw [h, mul_inv_cancel_right]
  · rw [← map_subtype_levi_adjDatumE6 J]
    exact map_mono (levi_le_neighbourLevi hJN)

theorem perfectCore_inf_centralizer_leviTorus_inf [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) :
    perfectCore (adjointGroup .E6 K ⊓
        centralizer ((leviTorus K J ⊓ adjointGroup .E6 K : Subgroup (ModGL .E6 K)) :
          Set (ModGL .E6 K))) =
      rootSpan .E6 K (amalgamRoots J) :=
  perfectCore_inf_centralizer_eq_of_le (F4Pilot.three_le_natCard_top_units hq) hJ inf_le_left
    fun _ ha => rootDiagUnit_mem_leviTorus_inf_of_mem_corootTupleSet ha

end Main

section Subfield

variable {k : Type} [Field k]

theorem corootTuple_unitsMap (f : k →+* K) (δ : Fin (Tag.rank .E6) → ℤ) (c : kˣ) :
    corootTuple δ (Units.map f.toMonoidHom c) =
      fun i => Units.map f.toMonoidHom (corootTuple δ c i) := by
  funext i
  simp only [corootTuple, map_zpow]

section BaseChange

theorem map_baseChangeGL_leviTorus_le (f : k →+* K) (J : Finset (Fin (Tag.rank .E6))) :
    (leviTorus k J).map (baseChangeGL f) ≤ leviTorus K J := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hx
  rw [F4Pilot.baseChangeGL_rootDiagUnit_eq_map]
  refine rootDiagUnit_mem_leviTorus fun j hj => ?_
  rw [hb j hj, map_one]

theorem rootDiagUnit_mem_map_leviTorus_inf_of_mem_corootTupleSet (f : k →+* K)
    {J : Finset (Fin (Tag.rank .E6))} {a : Fin (Tag.rank .E6) → Kˣ}
    (ha : a ∈ corootTupleSet (Units.map f.toMonoidHom).range J) :
    rootDiagUnit .E6 a ∈ (leviTorus k J ⊓ adjointGroup .E6 k).map (baseChangeGL f) := by
  obtain ⟨δ, -, hδJ, c', hc', rfl⟩ := ha
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hc'
  refine ⟨rootDiagUnit .E6 (corootTuple δ c), ⟨rootDiagUnit_corootTuple_mem_leviTorus hδJ c,
    rootDiagUnit_corootTuple_mem_adjointGroup δ c⟩, ?_⟩
  rw [F4Pilot.baseChangeGL_rootDiagUnit_eq_map, corootTuple_unitsMap]

theorem map_baseChangeGL_leviTorus_inf_le (f : k →+* K) (J : Finset (Fin (Tag.rank .E6))) :
    (leviTorus k J ⊓ adjointGroup .E6 k).map (baseChangeGL f) ≤ leviTorus K J :=
  (map_mono inf_le_left).trans (map_baseChangeGL_leviTorus_le f J)

end BaseChange

theorem perfectCore_inf_centralizer_map_leviTorus_inf [Finite k] (f : k →+* K)
    (hq : 4 ≤ Nat.card k) {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) :
    perfectCore (adjointGroup .E6 K ⊓
        centralizer (((leviTorus k J ⊓ adjointGroup .E6 k).map (baseChangeGL f) :
          Subgroup (ModGL .E6 K)) : Set (ModGL .E6 K))) =
      rootSpan .E6 K (amalgamRoots J) :=
  perfectCore_inf_centralizer_eq_of_le (F4Pilot.three_le_natCard_range_unitsMap f hq) hJ
    (map_baseChangeGL_leviTorus_inf_le f J)
    fun _ ha => rootDiagUnit_mem_map_leviTorus_inf_of_mem_corootTupleSet f ha

theorem perfectCore_levi_inf_centralizer_map_leviTorus_inf [Finite k] (f : k →+* K)
    (hq : 4 ≤ Nat.card k) {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    (N : E6Neighbour) (hJN : J ⊆ N.nodes) :
    perfectCore ((N.levi K).map (adjointGroup .E6 K).subtype ⊓
        centralizer (((leviTorus k J ⊓ adjointGroup .E6 k).map (baseChangeGL f) :
          Subgroup (ModGL .E6 K)) : Set (ModGL .E6 K))) =
      rootSpan .E6 K (amalgamRoots J) :=
  perfectCore_levi_inf_centralizer_eq_of_le (F4Pilot.three_le_natCard_range_unitsMap f hq) hJ N
    hJN (map_baseChangeGL_leviTorus_inf_le f J)
    fun _ ha => rootDiagUnit_mem_map_leviTorus_inf_of_mem_corootTupleSet f ha

end Subfield

end CFSG.SeitzReduction.E6Pilot
