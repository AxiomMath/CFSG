module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldTorus
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldStep3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open scoped commutatorElement

local instance e6PilotQ2FieldCoreNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩


section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

theorem fixedFieldInclusion_rep (N : E6Neighbour) :
    fixedFieldInclusion σ (N.rep (fixSubfield σ)) = N.rep K :=
  Subtype.ext (by rw [coe_fixedFieldInclusion, baseChangeGL_rep])

theorem le_a5Levi_of_perfect_of_le_centralizer (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {a : adjointGroup .E6 (fixSubfield σ)} (ha : a ∈ posJ (fixSubfield σ))
    (ha3 : orderOf a = 3) {P : Subgroup (adjointGroup .E6 K)} (hP : ⁅P, P⁆ = P)
    (hPa : P ≤ centralizer ({fixedFieldInclusion σ a} : Set (adjointGroup .E6 K))) :
    P ≤ a5Levi K := by
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have hQ : P.map (adjointGroup .E6 K).subtype ≤ rootSpan .E6 K (EPilot.perpRoots .E6) := by
    refine le_rootSpan_perpRoots_of_perfect_of_le_centralizer_E6 hk hK
      (fixSubfield σ).subtype (mem_subgroupOf.1 ha) (by rw [Subgroup.orderOf_coe, ha3])
      (by rw [← map_commutator, hP]) (map_subtype_le _) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hPa hy))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_fixedFieldInclusion] at h1
    exact h1
  intro y hy
  rw [a5Levi, mem_subgroupOf, a5LeviRoots_eq_orthRoots, ← perpRoots_eq_orthRoots]
  exact hQ ⟨y, hy, rfl⟩

theorem le_levi_of_perfect_of_le_centralizer (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {a : adjointGroup .E6 (fixSubfield σ)} (ha : a ∈ posJ (fixSubfield σ))
    (ha3 : orderOf a = 3) (N : E6Neighbour) {P : Subgroup (adjointGroup .E6 K)} (hP : ⁅P, P⁆ = P)
    (hPa : P ≤ centralizer ({fixedFieldInclusion σ (N.rep (fixSubfield σ) * a *
      (N.rep (fixSubfield σ))⁻¹)} : Set (adjointGroup .E6 K))) :
    P ≤ N.levi K := by
  set P' := P.map (MulAut.conj (N.rep K)⁻¹).toMonoidHom with hP'
  have hP'p : ⁅P', P'⁆ = P' := by rw [hP', ← map_commutator, hP]
  have hP'a : P' ≤ centralizer ({fixedFieldInclusion σ a} : Set (adjointGroup .E6 K)) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (hPa hy)
    rw [map_mul, map_mul, map_inv, fixedFieldInclusion_rep] at h1
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc (N.rep K)⁻¹ * y * N.rep K * fixedFieldInclusion σ a =
        (N.rep K)⁻¹ * (y * (N.rep K * fixedFieldInclusion σ a * (N.rep K)⁻¹)) * N.rep K := by
          group
      _ = (N.rep K)⁻¹ * ((N.rep K * fixedFieldInclusion σ a * (N.rep K)⁻¹) * y) * N.rep K := by
          rw [h1]
      _ = fixedFieldInclusion σ a * ((N.rep K)⁻¹ * y * N.rep K) := by group
  have hD := le_a5Levi_of_perfect_of_le_centralizer hk hK ha ha3 hP'p hP'a
  rw [← map_conj_rep_a5Levi N]
  intro y hy
  refine ⟨(N.rep K)⁻¹ * y * N.rep K, hD ⟨y, hy, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Torus

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev rootPairE6 (K : Type) [Field K] (δ : Fin (Tag.rank .E6) → ℤ) :
    Subgroup (adjointGroup .E6 K) :=
  (rootSubgroup .E6 K δ ⊔ rootSubgroup .E6 K (-δ)).subgroupOf (adjointGroup .E6 K)

omit [Finite K] [CharP K 2] in
theorem rootPairE6_swap (a b : Fin 6) : rootPairE6 K (a5Root b a) = rootPairE6 K (a5Root a b) := by
  rw [rootPairE6, rootPairE6, a5Root_swap_E6, neg_neg, sup_comm]

theorem slToAdjointE6_transvection_mem_rootPairE6 {a b : Fin 6} (hab : a ≠ b) (c : K) :
    slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hab c) ∈ rootPairE6 K (a5Root a b) := by
  rw [mem_subgroupOf, coe_slToAdjointE6_transvection hab c]
  exact mem_sup_left (mem_rootSubgroup.2 ⟨c, rfl⟩)

theorem map_perfectCore_comap_slToAdjointE6 {P : Subgroup (adjointGroup .E6 K)}
    (hP : ⁅P, P⁆ = P) (hPD : P ≤ a5Levi K) :
    (perfectCore (P.comap (slToAdjointE6 K))).map (slToAdjointE6 K) = P := by
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  have hle : P ≤ (slToAdjointE6 K).range := by
    rw [range_slToAdjointE6]
    exact hPD
  rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq_self hle]
  exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hP

theorem perfectCore_comap_le_blockSpecialLinear {P : Subgroup (adjointGroup .E6 K)}
    {i j : Fin 6} (hij : i ≠ j)
    (hPc : P ≤ centralizer (rootPairE6 K (a5Root i j) : Set (adjointGroup .E6 K))) :
    perfectCore (P.comap (slToAdjointE6 K)) ≤
      blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ := by
  set Q := perfectCore (P.comap (slToAdjointE6 K)) with hQdef
  have hQp : ⁅Q, Q⁆ = Q := CFSG.Quasithin.perfectCore_perfect _
  have hQP : ∀ A ∈ Q, slToAdjointE6 K A ∈ P := fun A hA =>
    (perfectCore_le (P.comap (slToAdjointE6 K))) hA
  have hJ : ∀ a ∈ ({i, j} : Finset (Fin 6)), ∀ b ∈ ({i, j} : Finset (Fin 6)), ∀ hab : a ≠ b,
      slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hab 1) ∈
        rootPairE6 K (a5Root i j) := by
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · rw [← ha, ← hb]
      exact slToAdjointE6_transvection_mem_rootPairE6 hab 1
    · rw [← ha, ← hb, ← rootPairE6_swap]
      exact slToAdjointE6_transvection_mem_rootPairE6 hab 1
    · exact absurd (ha.trans hb.symm) hab
  set T : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K) :=
    Subgroup.closure {B | ∃ (a b : Fin 6) (hab : a ≠ b), a ∈ ({i, j} : Finset (Fin 6)) ∧
      b ∈ ({i, j} : Finset (Fin 6)) ∧ Matrix.SpecialLinearGroup.transvection hab 1 = B} with hT
  have hTJ : ∀ B ∈ T, slToAdjointE6 K B ∈ rootPairE6 K (a5Root i j) := by
    intro B hB
    have h1 : T ≤ (rootPairE6 K (a5Root i j)).comap (slToAdjointE6 K) := by
      rw [hT, Subgroup.closure_le]
      rintro _ ⟨a, b, hab, ha, hb, rfl⟩
      exact hJ a ha b hb hab
    exact h1 hB
  have hQT : ⁅Q, T⁆ ≤ center (Matrix.SpecialLinearGroup (Fin 6) K) := by
    rw [Subgroup.commutator_le]
    intro A hA B hB
    rw [← ker_slToAdjointE6, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.1 (hPc (hQP A hA)) _ (hTJ B hB)).symm
  have hQC := LinearPilot.le_centralizer_of_commutator_le_center_of_perfect hQp hQT
  have hcomm : ∀ A ∈ Q, ∀ a ∈ ({i, j} : Finset (Fin 6)), ∀ b ∈ ({i, j} : Finset (Fin 6)),
      ∀ hab : a ≠ b, A * Matrix.SpecialLinearGroup.transvection hab 1 =
        Matrix.SpecialLinearGroup.transvection hab 1 * A := fun A hA a ha b hb hab =>
    (mem_centralizer_iff.1 (hQC hA) _ (Subgroup.subset_closure ⟨a, b, hab, ha, hb, rfl⟩)).symm
  have hQle := LinearPilot.le_blockSpecialLinear_sdiff_of_commute (N := Finset.univ)
    (T := ({i, j} : Finset (Fin 6))) (by rw [Finset.card_pair hij])
    (by rw [LinearPilot.blockSpecialLinear_univ]; exact le_top) hQp hcomm
  rwa [show (Finset.univ \ ({i, j} : Finset (Fin 6))) = ({i, j} : Finset (Fin 6))ᶜ from
    (Finset.compl_eq_univ_sdiff _).symm] at hQle

theorem map_blockSpecialLinear_pair_le {m n : Fin 6} (hmn : m ≠ n) :
    (blockSpecialLinear (K := K) ({m, n} : Finset (Fin 6))).map (slToAdjointE6 K) ≤
      (rootSpan .E6 K {a5Root m n, a5Root n m}).subgroupOf (adjointGroup .E6 K) := by
  rw [LinearPilot.blockSpecialLinear_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨a, b, hab, c, ha, hb, rfl⟩, rfl⟩
  change ((slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hab c) :
    adjointGroup .E6 K) : ModGL .E6 K) ∈ rootSpan .E6 K _
  rw [coe_slToAdjointE6_transvection hab c]
  have hmem : a5Root a b ∈ ({a5Root m n, a5Root n m} : Set (Fin (Tag.rank .E6) → ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab
  exact le_iSup₂ (f := fun α (_ : α ∈ ({a5Root m n, a5Root n m} :
    Set (Fin (Tag.rank .E6) → ℤ))) => rootSubgroup .E6 K α) _ hmem
    (mem_rootSubgroup.2 ⟨c, rfl⟩)

omit [Finite K] [CharP K 2] in
theorem rootPairE6_root_le_levi {M N : E6Neighbour} (h : M ≠ N) :
    rootPairE6 K M.root ≤ N.levi K := by
  refine Subgroup.subgroupOf_mono _ (sup_le ?_ ?_)
  · exact le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E6 K α) M.root
      ⟨M.isRoot_root, by rw [iform_comm, E6Neighbour.iform_root_root_eq_zero h]⟩ le_rfl
  · exact le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E6 K α) (-M.root)
      ⟨IsRoot.neg M.isRoot_root, by rw [iform_neg_right_E6, iform_comm,
        E6Neighbour.iform_root_root_eq_zero h, neg_zero]⟩ le_rfl

theorem a5Root_cover_check : E6Neighbour.six.root = a5Root 4 5 ∧
    E6Neighbour.three.root = a5Root 1 2 ∧ tripleRoot = a5Root 0 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem compl_inter_check :
    ({4, 5} : Finset (Fin 6))ᶜ ∩ ({1, 2} : Finset (Fin 6))ᶜ = {0, 3} := by
  decide

theorem le_tripleRootSL2_of_le_levi {P : Subgroup (adjointGroup .E6 K)} (hP : ⁅P, P⁆ = P)
    (hPN : ∀ M : E6Neighbour, P ≤ M.levi K) : P ≤ tripleRootSL2 K := by
  obtain ⟨h6, h3, h0⟩ := a5Root_cover_check
  have hPD : P ≤ a5Levi K := (E6Neighbour.levi_high K) ▸ hPN .high
  have hc : ∀ M : E6Neighbour, P ≤ centralizer (rootPairE6 K M.root : Set (adjointGroup .E6 K)) :=
    fun M => by
      rw [rootPairE6, centralizer_rootPair_eq_levi (K := K) M]
      exact hPN M
  have hc6 : P ≤ centralizer (rootPairE6 K (a5Root 4 5) : Set (adjointGroup .E6 K)) := by
    rw [← h6]
    exact hc .six
  have hc3 : P ≤ centralizer (rootPairE6 K (a5Root 1 2) : Set (adjointGroup .E6 K)) := by
    rw [← h3]
    exact hc .three
  have hQ6 := perfectCore_comap_le_blockSpecialLinear (by decide : (4 : Fin 6) ≠ 5) hc6
  have hQ3 := perfectCore_comap_le_blockSpecialLinear (by decide : (1 : Fin 6) ≠ 2) hc3
  have hQ : perfectCore (P.comap (slToAdjointE6 K)) ≤
      blockSpecialLinear (K := K) ({0, 3} : Finset (Fin 6)) := by
    rw [← compl_inter_check, ← LinearPilot.blockSpecialLinear_inf]
    exact le_inf hQ6 hQ3
  rw [← map_perfectCore_comap_slToAdjointE6 hP hPD]
  refine (Subgroup.map_mono hQ).trans ((map_blockSpecialLinear_pair_le (by decide)).trans ?_)
  rw [tripleRootSL2, h0, ← a5Root_swap_E6 0 3]

end Model

section Perfect

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem rootSpan_pair_E6 (a b : Fin (Tag.rank .E6) → ℤ) :
    rootSpan .E6 K {a, b} = rootSubgroup .E6 K a ⊔ rootSubgroup .E6 K b := by
  rw [rootSpan, iSup_insert, iSup_singleton]

theorem commutator_tripleRootSL2 (hK : 4 ≤ Nat.card K) :
    ⁅tripleRootSL2 K, tripleRootSL2 K⁆ = tripleRootSL2 K := by
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  obtain ⟨-, hrange, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E6 K isRoot_tripleRoot
  have hmap : (tripleRootSL2 K).map (adjointGroup .E6 K).subtype =
      (rootSL2 .E6 K tripleRoot).range := by
    rw [tripleRootSL2, subgroupOf_map_subtype, rootSpan_pair_E6, hrange]
    exact inf_of_le_left (sup_le (rootSubgroup_le_adjointGroup _)
      (rootSubgroup_le_adjointGroup _))
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [map_commutator, hmap, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    hperf.commutator_eq_top]

theorem top_commutator_tripleRootSL2 (hK : 4 ≤ Nat.card K) :
    ⁅(⊤ : Subgroup (tripleRootSL2 K)), (⊤ : Subgroup (tripleRootSL2 K))⁆ = ⊤ := by
  have : Group.IsPerfect (tripleRootSL2 K) :=
    Subgroup.isPerfect_iff.2 (commutator_tripleRootSL2 hK)
  exact Group.IsPerfect.commutator_eq_top

end Perfect

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {σ : K ≃+* K}

@[expose] noncomputable def tripleCoreG (e : L ≃* adjointGroup .E6 (fixSubfield σ))
    (A : Subgroup (adjointGroup .E6 (fixSubfield σ))) : Subgroup G :=
  perfectCore (⨅ M : E6Neighbour, centralizer (q2NeighbourGE6 e A M : Set G))

omit [Finite K] [CharP K 2] in
theorem map_conj_rep_le_levi {k : Type} [Field k] {A : Subgroup (adjointGroup .E6 k)}
    (hAJ : A ≤ posJ k) {M N : E6Neighbour} (h : M ≠ N) :
    A.map (MulAut.conj (M.rep k)).toMonoidHom ≤ N.levi k := by
  refine (Subgroup.map_mono hAJ).trans ?_
  rw [posJ, EPilot.highRootSL2, map_conj_rep_rootSL2 M]
  exact rootPairE6_root_le_levi h

omit [Finite G] [Finite K] [CharP K 2] in
theorem mem_q2NeighbourGE6 {e : L ≃* adjointGroup .E6 (fixSubfield σ)}
    {A : Subgroup (adjointGroup .E6 (fixSubfield σ))} {M : E6Neighbour} {x : G}
    (hx : x ∈ q2NeighbourGE6 e A M) :
    ∃ a ∈ A, x = ((e.symm (M.rep (fixSubfield σ) * a * (M.rep (fixSubfield σ))⁻¹) : L) : G) := by
  obtain ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩ := hx
  exact ⟨a, ha, rfl⟩

theorem map_range_section_eq_tripleCoreG (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {e : L ≃* adjointGroup .E6 (fixSubfield σ)}
    {A : Subgroup (adjointGroup .E6 (fixSubfield σ))} (hAJ : A ≤ posJ (fixSubfield σ))
    (hA : Nat.card A = 3) (N : E6Neighbour) {E : Subgroup G}
    (hE : E = centralizerPerfectCore (q2NeighbourGE6 e A N)) (h : TwoCover σ e N E)
    (s : tripleRootSL2 K →* E)
    (hs : ∀ y, ((h.p (s y) : N.levi K) : adjointGroup .E6 K) = y) :
    s.range.map E.subtype = tripleCoreG e A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  set S := s.range.map E.subtype with hSdef
  have hSp : ⁅S, S⁆ = S := by
    rw [hSdef, MonoidHom.range_eq_map, Subgroup.map_map, ← map_commutator,
      top_commutator_tripleRootSL2 hK4]
  have hSE : S ≤ E := map_subtype_le _
  have hXfix : ∀ M, M ≠ N → ∀ a ∈ A, ∃ y : E, (y : G) = ((e.symm (M.rep (fixSubfield σ) * a *
      (M.rep (fixSubfield σ))⁻¹) : L) : G) ∧ ((h.p y : N.levi K) : adjointGroup .E6 K) =
        fixedFieldInclusion σ (M.rep (fixSubfield σ) * a * (M.rep (fixSubfield σ))⁻¹) := by
    intro M hM a ha
    have hmem := map_conj_rep_le_levi hAJ hM ⟨a, ha, rfl⟩
    obtain ⟨y, hy, hpy⟩ := h.fix ⟨_, hmem⟩
    refine ⟨y, hy, ?_⟩
    rw [hpy]
    rfl
  have hSC : ∀ M, S ≤ centralizer (q2NeighbourGE6 e A M : Set G) := by
    intro M
    by_cases hM : M = N
    · subst hM
      exact hSE.trans (hE ▸ F4Pilot.centralizerPerfectCore_le_centralizer _)
    · set J : Subgroup E := (q2NeighbourGE6 e A M).subgroupOf E with hJ
      have hCJ : ⁅s.range, J⁆ ≤ center E := by
        rw [Subgroup.commutator_le]
        rintro _ ⟨y, rfl⟩ j hj
        refine h.ker_le_center ?_
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        obtain ⟨a, ha, hja⟩ := mem_q2NeighbourGE6 (mem_subgroupOf.1 hj)
        obtain ⟨z, hz, hpz⟩ := hXfix M hM a ha
        have hjz : j = z := Subtype.ext (hja.trans hz.symm)
        rw [hjz]
        apply Subtype.ext
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hs, hpz]
        have hyM : (y : adjointGroup .E6 K) ∈ M.levi K := tripleRootSL2_le_levi M y.2
        have h1 := mem_centralizer_iff.1 (levi_le_centralizer_map_fixedFieldInclusion hAJ M hyM)
          (fixedFieldInclusion σ (M.rep (fixSubfield σ) * a * (M.rep (fixSubfield σ))⁻¹))
          ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact (congrArg Subtype.val h1).symm
      have hC := LinearPilot.le_centralizer_of_commutator_le_center_of_perfect
        (by rw [MonoidHom.range_eq_map, ← map_commutator, top_commutator_tripleRootSL2 hK4]) hCJ
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      have hxE : x ∈ E := by
        obtain ⟨a, ha, rfl⟩ := mem_q2NeighbourGE6 hx
        obtain ⟨z, hz, -⟩ := hXfix M hM a ha
        rw [← hz]
        exact z.2
      have := mem_centralizer_iff.1 (hC hy) ⟨x, hxE⟩ (mem_subgroupOf.2 hx)
      exact congrArg Subtype.val this
  refine le_antisymm (le_perfectCore_of_perfect (le_iInf hSC) hSp) ?_
  set T := tripleCoreG e A with hTdef
  have hTp : ⁅T, T⁆ = T := CFSG.Quasithin.perfectCore_perfect _
  have hTE : T ≤ E := by
    rw [hE]
    exact F4Pilot.le_centralizerPerfectCore hTp ((perfectCore_le _).trans (iInf_le _ N))
  set T' := T.subgroupOf E with hT'
  have hT'map : T'.map E.subtype = T := by
    rw [hT', subgroupOf_map_subtype, inf_of_le_left hTE]
  have hT'p : ⁅T', T'⁆ = T' := by
    apply Subgroup.map_injective E.subtype_injective
    rw [map_commutator, hT'map, hTp]
  set P := (T'.map h.p).map (N.levi K).subtype with hPdef
  have hPp : ⁅P, P⁆ = P := by rw [hPdef, ← map_commutator, ← map_commutator, hT'p]
  have hPM : ∀ M : E6Neighbour, P ≤ M.levi K := by
    intro M
    by_cases hM : M = N
    · rw [hM, hPdef]
      exact map_subtype_le _
    · have : IsCyclic A := isCyclic_of_prime_card hA
      obtain ⟨⟨a, haA⟩, hgen⟩ := IsCyclic.exists_generator (α := A)
      have ha3 : orderOf a = 3 := by
        rw [← Subgroup.orderOf_mk a haA, orderOf_eq_card_of_forall_mem_zpowers hgen, hA]
      refine le_levi_of_perfect_of_le_centralizer hk hK (hAJ haA) ha3 M hPp ?_
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      obtain ⟨z, hz, hpz⟩ := hXfix M hM a haA
      have htz : (t : G) * z = z * t := by
        have hzX : (z : G) ∈ q2NeighbourGE6 e A M := by
          rw [hz]
          exact ⟨_, ⟨_, ⟨a, haA, rfl⟩, rfl⟩, rfl⟩
        exact (mem_centralizer_iff.1 ((perfectCore_le _).trans (iInf_le _ M) (mem_subgroupOf.1 ht))
          _ hzX).symm
      have h1 : t * z = z * t := Subtype.ext htz
      have h2 := congrArg (fun w : E => ((h.p w : N.levi K) : adjointGroup .E6 K)) h1
      simp only [map_mul, Subgroup.coe_mul] at h2
      rw [hpz] at h2
      exact h2
  have hPT := le_tripleRootSL2_of_le_levi hPp hPM
  have hdec : ∀ t ∈ T', ∃ y : tripleRootSL2 K, ∃ z ∈ center E, t = s y * z := by
    intro t ht
    have hpt : ((h.p t : N.levi K) : adjointGroup .E6 K) ∈ tripleRootSL2 K :=
      hPT ⟨h.p t, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨⟨_, hpt⟩, (s ⟨_, hpt⟩)⁻¹ * t, h.ker_le_center ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext (hs ⟨_, hpt⟩)
  have hT's : T' ≤ s.range := by
    rw [← hT'p, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨ya, za, hza, rfl⟩ := hdec a ha
    obtain ⟨yb, zb, hzb, rfl⟩ := hdec b hb
    rw [commutatorElement_mul_left_of_mem_center hza,
      commutatorElement_mul_right_of_mem_center hzb, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  rw [← hT'map]
  exact Subgroup.map_mono hT's

end Core

end CFSG.SeitzReduction.E6Pilot
