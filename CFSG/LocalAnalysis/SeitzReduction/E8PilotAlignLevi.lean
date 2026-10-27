module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviTori
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect)

local instance e8PilotAlignLeviNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def corootTupleSet (A : Subgroup Kˣ) (J : Finset (Fin (Tag.rank .E8))) :
    Set (Fin (Tag.rank .E8) → Kˣ) :=
  {a | ∃ δ, IsRoot .E8 δ ∧ (∀ j ∈ J, iform δ (Pi.single j 1) = 0) ∧ ∃ c ∈ A, corootTuple δ c = a}

section Pair

theorem eq_of_dvd_iform_sub {m : ℕ} (hm : 3 ≤ m) {δ δ' : Fin (Tag.rank .E8) → ℤ}
    (hδ : IsRoot .E8 δ) (hδ' : IsRoot .E8 δ')
    (h : ∀ i, (m : ℤ) ∣ iform δ' (Pi.single i 1) - iform δ (Pi.single i 1)) : δ' = δ := by
  have hu : ∀ i, (m : ℤ) ∣ iform (δ' - δ) (Pi.single i 1) := fun i => by
    rw [iform_sub_left]
    exact h i
  choose v hv using dvd_apply_of_forall_dvd_iform_single hu
  have huv : δ' - δ = (m : ℤ) • v := funext fun j => by
    rw [hv j, Pi.smul_apply, smul_eq_mul]
  by_contra hne
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [smul_zero, sub_eq_zero] at huv
    exact hne huv
  have hpos := iform_self_pos hv0
  have huu : iform (δ' - δ) (δ' - δ) = (m : ℤ) ^ 2 * iform v v := by
    rw [huv, iform_smul_left, iform_smul_right]
    ring
  have h8 : iform (δ' - δ) (δ' - δ) ≤ 8 := by
    have h1 := abs_le.1 (abs_iform_le_two hδ' hδ)
    have hδδ := EPilot.iform_self_eq_two (Or.inr (Or.inr rfl)) hδ
    have hδ'δ' := EPilot.iform_self_eq_two (Or.inr (Or.inr rfl)) hδ'
    rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm δ δ']
    linarith [h1.1]
  have hm3 : (3 : ℤ) ≤ m := by exact_mod_cast hm
  nlinarith

end Pair

section KernelWeyl

theorem coeff_eq_zero_of_mem_toralSetKernel_corootTupleSet {A : Subgroup Kˣ}
    (hA : 3 ≤ Nat.card A) {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2)
    {γ : Fin (Tag.rank .E8) → ℤ} (hγ : γ ∈ F4Pilot.toralSetKernel (corootTupleSet A J)) :
    ∀ i ∉ J, γ i = 0 := by
  obtain ⟨c, hcA, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  refine coeff_eq_zero_of_forall_iform_eq_zero hJ fun δ hδ hδJ => ?_
  have h1 := hγ.2 _ ⟨δ, hδ, hδJ, c, hcA, rfl⟩
  rw [rootChar_corootTuple, ← orderOf_dvd_iff_zpow_eq_one, hc] at h1
  rw [iform_comm]
  refine Int.eq_zero_of_abs_lt_dvd h1 ?_
  have := abs_le.1 (abs_iform_le_two hδ hγ.1)
  have h3 : (3 : ℤ) ≤ ((Nat.card A : ℕ) : ℤ) := by exact_mod_cast hA
  rw [abs_lt]
  constructor <;> omega

theorem smul_eq_of_mem_rootCharStabilizer_corootTuple {δ : Fin (Tag.rank .E8) → ℤ}
    (hδ : IsRoot .E8 δ) {c : Kˣ} (hc : 3 ≤ orderOf c) {w : WeylGroup .E8}
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

theorem smul_fundWeight_eq_of_forall_smul_eq {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2)
    {w : WeylGroup .E8}
    (hw : ∀ δ, IsRoot .E8 δ → (∀ j ∈ J, iform δ (Pi.single j 1) = 0) → w • δ = δ)
    {i : Fin (Tag.rank .E8)} (hi : i ∉ J) : w • fundWeight i = fundWeight i := by
  obtain ⟨hne, hcas⟩ := casimir_check J hJ
  have hS : w • casimirVec J i = casimirVec J i := by
    rw [casimirVec, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hδ, hδJ⟩ := isRoot_of_mem_perpPositions hk
    rw [smul_comm, hw _ hδ hδJ]
  rw [hcas i hi, smul_comm] at hS
  exact smul_right_injective _ hne hS

theorem smul_apply_eq_of_forall_smul_eq {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2)
    {w : WeylGroup .E8}
    (hw : ∀ δ, IsRoot .E8 δ → (∀ j ∈ J, iform δ (Pi.single j 1) = 0) → w • δ = δ) :
    ∀ v : Fin (Tag.rank .E8) → ℤ, ∀ i ∉ J, (w • v) i = v i := by
  intro v i hi
  rw [← iform_fundWeight (w • v) i, ← smul_fundWeight_eq_of_forall_smul_eq hJ hw hi, iform_smul,
    iform_fundWeight]

theorem smul_apply_eq_of_mem_rootCharStabilizer_corootTupleSet {A : Subgroup Kˣ}
    (hA : 3 ≤ Nat.card A) {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2)
    {w : WeylGroup .E8} (hw : ∀ a ∈ corootTupleSet A J, w ∈ rootCharStabilizer a) :
    ∀ v : Fin (Tag.rank .E8) → ℤ, ∀ i ∉ J, (w • v) i = v i := by
  obtain ⟨c, hcA, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  refine smul_apply_eq_of_forall_smul_eq hJ fun δ hδ hδJ => ?_
  exact smul_eq_of_mem_rootCharStabilizer_corootTuple hδ (hc ▸ hA)
    (hw _ ⟨δ, hδ, hδJ, c, hcA, rfl⟩)

end KernelWeyl

section Points

theorem rootSpan_amalgamRoots_le_inf_centralizer {J : Finset (Fin (Tag.rank .E8))}
    {T : Subgroup (ModGL .E8 K)} (hT : T ≤ leviTorus K J) :
    rootSpan .E8 K (amalgamRoots J) ≤
      adjointGroup .E8 K ⊓ centralizer (T : Set (ModGL .E8 K)) :=
  le_inf (rootSpan_le_adjointGroup_E8 _)
    ((rootSpan_amalgamRoots_le_centralizer_leviTorus J).trans
      (centralizer_le (SetLike.coe_subset_coe.2 hT)))

theorem commutator_rootSpan_amalgamRoots_eq_E8 {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    (J : Finset (Fin (Tag.rank .E8))) :
    ⁅rootSpan .E8 K (amalgamRoots J), rootSpan .E8 K (amalgamRoots J)⁆ =
      rootSpan .E8 K (amalgamRoots J) := by
  obtain ⟨c, -, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  exact F4Pilot.commutator_rootSpan_signedSimpleRoots_eq
    (F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf (hc ▸ hA)).2 _

end Points

theorem rootDiagUnit_mem_leviTorus_of_mem_corootTupleSet {A : Subgroup Kˣ}
    {J : Finset (Fin (Tag.rank .E8))} {a : Fin (Tag.rank .E8) → Kˣ}
    (ha : a ∈ corootTupleSet A J) : rootDiagUnit .E8 a ∈ leviTorus K J := by
  obtain ⟨δ, -, hδJ, c, -, rfl⟩ := ha
  exact rootDiagUnit_corootTuple_mem_leviTorus hδJ c

section Main

theorem perfectCore_le_rootSpan_amalgamRoots_of_forall_conj_eq {A : Subgroup Kˣ}
    (hA : 3 ≤ Nat.card A) {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2)
    {H : Subgroup (ModGL .E8 K)}
    (hH : ∀ g ∈ H, g ∈ adjointGroup .E8 K ∧
      ∀ a ∈ corootTupleSet A J, rootDiagUnit .E8 a * g * (rootDiagUnit .E8 a)⁻¹ = g) :
    perfectCore H ≤ rootSpan .E8 K (amalgamRoots J) :=
  F4Pilot.perfectCore_le_rootSpan_of_forall_conj_eq (corootTupleSet A J)
    (J : Set (Fin (Tag.rank .E8)))
    (fun _ hγ _ => coeff_eq_zero_of_mem_toralSetKernel_corootTupleSet hA hJ hγ)
    (fun _ hw => smul_apply_eq_of_mem_rootCharStabilizer_corootTupleSet hA hJ hw) hH

theorem perfectCore_levi_inf_centralizer_eq_of_le {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2) (N : E8Neighbour) (hJN : J ⊆ N.nodes)
    {T : Subgroup (ModGL .E8 K)} (hT : T ≤ leviTorus K J)
    (hTA : ∀ a ∈ corootTupleSet A J, rootDiagUnit .E8 a ∈ T) :
    perfectCore ((N.levi K).map (adjointGroup .E8 K).subtype ⊓
        centralizer (T : Set (ModGL .E8 K))) =
      rootSpan .E8 K (amalgamRoots J) := by
  refine le_antisymm (perfectCore_le_rootSpan_amalgamRoots_of_forall_conj_eq hA hJ
    fun g hg => ⟨map_subtype_le _ (mem_inf.1 hg).1, fun a ha => ?_⟩)
    (le_perfectCore_of_perfect (le_inf ?_
      ((rootSpan_amalgamRoots_le_inf_centralizer hT).trans inf_le_right))
      (commutator_rootSpan_amalgamRoots_eq_E8 hA J))
  · have h := mem_centralizer_iff.1 (mem_inf.1 hg).2 _ (hTA a ha)
    rw [h, mul_inv_cancel_right]
  · rw [← map_subtype_levi_adjDatumE8 J]
    exact map_mono (levi_le_neighbourLevi hJN)

theorem perfectCore_levi_inf_centralizer_leviTorus [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2) (N : E8Neighbour) (hJN : J ⊆ N.nodes) :
    perfectCore ((N.levi K).map (adjointGroup .E8 K).subtype ⊓
        centralizer (leviTorus K J : Set (ModGL .E8 K))) =
      rootSpan .E8 K (amalgamRoots J) :=
  perfectCore_levi_inf_centralizer_eq_of_le (F4Pilot.three_le_natCard_top_units hq) hJ N hJN
    le_rfl fun _ ha => rootDiagUnit_mem_leviTorus_of_mem_corootTupleSet ha

end Main

section Subfield

variable {k : Type} [Field k]

theorem corootTuple_unitsMap (f : k →+* K) (δ : Fin (Tag.rank .E8) → ℤ) (c : kˣ) :
    corootTuple δ (Units.map f.toMonoidHom c) =
      fun i => Units.map f.toMonoidHom (corootTuple δ c i) := by
  funext i
  simp only [corootTuple, map_zpow]

section BaseChange

theorem map_baseChangeGL_leviTorus_le (f : k →+* K) (J : Finset (Fin (Tag.rank .E8))) :
    (leviTorus k J).map (baseChangeGL f) ≤ leviTorus K J := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨b, hb, rfl⟩ := mem_leviTorus.1 hx
  rw [F4Pilot.baseChangeGL_rootDiagUnit_eq_map]
  refine rootDiagUnit_mem_leviTorus fun j hj => ?_
  rw [hb j hj, map_one]

theorem rootDiagUnit_mem_map_leviTorus_of_mem_corootTupleSet (f : k →+* K)
    {J : Finset (Fin (Tag.rank .E8))} {a : Fin (Tag.rank .E8) → Kˣ}
    (ha : a ∈ corootTupleSet (Units.map f.toMonoidHom).range J) :
    rootDiagUnit .E8 a ∈ (leviTorus k J).map (baseChangeGL f) := by
  obtain ⟨δ, -, hδJ, c', hc', rfl⟩ := ha
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hc'
  refine ⟨rootDiagUnit .E8 (corootTuple δ c), rootDiagUnit_corootTuple_mem_leviTorus hδJ c, ?_⟩
  rw [F4Pilot.baseChangeGL_rootDiagUnit_eq_map, corootTuple_unitsMap]

end BaseChange

theorem perfectCore_levi_inf_centralizer_map_leviTorus [Finite k] (f : k →+* K)
    (hq : 4 ≤ Nat.card k) {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2)
    (N : E8Neighbour) (hJN : J ⊆ N.nodes) :
    perfectCore ((N.levi K).map (adjointGroup .E8 K).subtype ⊓
        centralizer (((leviTorus k J).map (baseChangeGL f) : Subgroup (ModGL .E8 K)) :
          Set (ModGL .E8 K))) =
      rootSpan .E8 K (amalgamRoots J) :=
  perfectCore_levi_inf_centralizer_eq_of_le (F4Pilot.three_le_natCard_range_unitsMap f hq) hJ N
    hJN (map_baseChangeGL_leviTorus_le f J)
    fun _ ha => rootDiagUnit_mem_map_leviTorus_of_mem_corootTupleSet f ha

end Subfield

end CFSG.SeitzReduction.E8Pilot
