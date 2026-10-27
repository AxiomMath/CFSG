module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowPieces

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open E6Neighbour

local instance e6PilotQ2RowOverlapNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Generic

variable {G : Type*} [Group G]

theorem commutator_sup_le_of_le_centralizer {A D : Subgroup G} (hA : A ≤ centralizer (A : Set G))
    (hAD : A ≤ centralizer (D : Set G)) : ⁅A ⊔ D, A ⊔ D⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hAN : A ≤ normalizer (D : Set G) := hAD.trans (centralizer_le_normalizer _)
  have hg₁' : g₁ ∈ ((A ⊔ D : Subgroup G) : Set G) := hg₁
  have hg₂' : g₂ ∈ ((A ⊔ D : Subgroup G) : Set G) := hg₂
  rw [coe_mul_of_left_le_normalizer_right _ _ hAN] at hg₁' hg₂'
  obtain ⟨a₁, ha₁, d₁, hd₁, rfl⟩ := Set.mem_mul.1 hg₁'
  obtain ⟨a₂, ha₂, d₂, hd₂, rfl⟩ := Set.mem_mul.1 hg₂'
  have hc : ∀ {a d : G}, a ∈ A → d ∈ D → Commute a d := fun ha hd =>
    (mem_centralizer_iff.1 (hAD ha) _ hd).symm
  rw [F4Pilot.commutatorElement_mul_mul_eq_right_of_commute
    ((mem_centralizer_iff.1 (hA ha₁) _ ha₂).symm) (hc ha₁ hd₁) (hc ha₁ hd₂) (hc ha₂ hd₁)
    (hc ha₂ hd₂), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)

theorem center_eq_bot_of_isSimpleGroup_of_commutator {H : Type*} [Group H] [IsSimpleGroup H]
    (hp : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤) : center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) with h | h
  · exact h
  · exfalso
    have hab : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      have hb : b ∈ center H := by rw [h]; exact mem_top b
      rw [mem_bot, commutatorElement_def, mem_center_iff.1 hb a]
      group
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial H)
    have htop : (⊤ : Subgroup H) = ⊥ := hp.symm.trans hab
    have h1 : ∀ z : H, z = 1 := fun z => by
      have hz : z ∈ (⊤ : Subgroup H) := mem_top z
      rw [htop] at hz
      exact hz
    exact hxy ((h1 x).trans (h1 y).symm)

end Generic

set_option maxRecDepth 100000 in
theorem a5Root_swap_eq_neg : ∀ i j : Fin 6, a5Root j i = -a5Root i j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem iform_a5Root_eq_zero_check : ∀ i j k l : Fin 6, k ≠ i → k ≠ j → l ≠ i → l ≠ j →
    iform (a5Root i j) (a5Root k l) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem disjoint_of_iform_a5Root_check : ∀ i j k l : Fin 6, i ≠ j → k ≠ l →
    iform (a5Root i j) (a5Root k l) = 0 → k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j := by
  decide +kernel


theorem a5Root_mem_orthRoots_inter {i j k l : Fin 6} (hkl : k ≠ l)
    (hk : k ∉ ({i, j} : Finset (Fin 6))) (hl : l ∉ ({i, j} : Finset (Fin 6))) :
    a5Root k l ∈ orthRoots (highRoot .E6) ∩ orthRoots (a5Root i j) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
  refine ⟨a5LeviRoots_eq_orthRoots ▸ a5Root_mem_a5LeviRoots hkl, isRoot_a5Root hkl, ?_⟩
  exact iform_a5Root_eq_zero_check i j k l hk.1 hk.2 hl.1 hl.2

theorem exists_a5Root_eq_of_mem_orthRoots_inter {i j : Fin 6} (hij : i ≠ j)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ orthRoots (highRoot .E6) ∩ orthRoots (a5Root i j)) :
    ∃ k l : Fin 6, k ≠ l ∧ k ∉ ({i, j} : Finset (Fin 6)) ∧ l ∉ ({i, j} : Finset (Fin 6)) ∧
      a5Root k l = γ := by
  obtain ⟨k, l, hkl, rfl⟩ := exists_a5Root_eq_of_mem_a5LeviRoots (a5LeviRoots_eq_orthRoots ▸ hγ.1)
  obtain ⟨h1, h2, h3, h4⟩ := disjoint_of_iform_a5Root_check i j k l hij hkl hγ.2.2
  refine ⟨k, l, hkl, ?_, ?_, rfl⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exacts [⟨h1, h2⟩, ⟨h3, h4⟩]

section Model


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem injective_slToAdjointE6_two (hK : Nat.card K = 2) :
    Function.Injective (slToAdjointE6 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_slToAdjointE6, eq_bot_iff]
  intro z hz
  exact mem_bot.2 (LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz)

theorem map_blockSpecialLinear_eq_perpSpan {i j : Fin 6} (hij : i ≠ j) :
    (blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map (slToAdjointE6 K) =
      (rootSpan .E6 K (orthRoots (highRoot .E6) ∩ orthRoots (a5Root i j))).subgroupOf
        (adjointGroup .E6 K) := by
  apply le_antisymm
  · rw [LinearPilot.blockSpecialLinear_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, l, hkl, c, hk, hl, rfl⟩, rfl⟩
    rw [Finset.mem_compl] at hk hl
    change ((slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hkl c) :
      adjointGroup .E6 K) : ModGL .E6 K) ∈ rootSpan .E6 K _
    rw [coe_slToAdjointE6_transvection hkl c]
    exact (le_iSup₂ (f := fun α (_ : α ∈ orthRoots (highRoot .E6) ∩ orthRoots (a5Root i j)) =>
      rootSubgroup .E6 K α) _ (a5Root_mem_orthRoots_inter hkl hk hl))
      (mem_rootSubgroup.2 ⟨c, rfl⟩)
  · intro x hx
    rw [mem_subgroupOf] at hx
    have hle : rootSpan .E6 K (orthRoots (highRoot .E6) ∩ orthRoots (a5Root i j)) ≤
        ((blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map (slToAdjointE6 K)).map
          (adjointGroup .E6 K).subtype := by
      refine iSup₂_le fun γ hγ => ?_
      obtain ⟨k, l, hkl, hk, hl, rfl⟩ := exists_a5Root_eq_of_mem_orthRoots_inter hij hγ
      intro g hg
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
      exact ⟨slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hkl c),
        ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hkl (Finset.mem_compl.2 hk)
          (Finset.mem_compl.2 hl) c, rfl⟩, coe_slToAdjointE6_transvection hkl c⟩
    obtain ⟨y, hy, hyx⟩ := hle hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy

theorem le_map_blockSpecialLinear_of_perfect (hK : Nat.card K = 2) {i j : Fin 6} (hij : i ≠ j)
    {P : Subgroup (adjointGroup .E6 K)} (hPL : P ≤ a5Levi K) (hperf : ⁅P, P⁆ = P)
    (hPc : P ≤ centralizer (((rootSubgroup .E6 K (a5Root i j) ⊔
      rootSubgroup .E6 K (-a5Root i j)).subgroupOf (adjointGroup .E6 K) :
        Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) :
    P ≤ (blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map (slToAdjointE6 K) := by
  have hinj := injective_slToAdjointE6_two hK
  set Q := P.comap (slToAdjointE6 K) with hQ
  have hQP : Q.map (slToAdjointE6 K) = P :=
    Subgroup.map_comap_eq_self (by rw [range_slToAdjointE6]; exact hPL)
  have hQperf : ⁅Q, Q⁆ = Q := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hQP, hperf]
  have hT : ∀ (i' j' : Fin 6) (hij' : i' ≠ j'), i' ∈ ({i, j} : Finset (Fin 6)) →
      j' ∈ ({i, j} : Finset (Fin 6)) →
      slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hij' 1) ∈
        (rootSubgroup .E6 K (a5Root i j) ⊔ rootSubgroup .E6 K (-a5Root i j)).subgroupOf
          (adjointGroup .E6 K) := by
    intro i' j' hij' hi' hj'
    rw [mem_subgroupOf, coe_slToAdjointE6_transvection hij' 1, ← a5Root_swap_eq_neg]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact absurd rfl hij'
    · exact mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩)
    · exact mem_sup_right (mem_rootSubgroup.2 ⟨1, rfl⟩)
    · exact absurd rfl hij'
  have hcomm : ∀ A ∈ Q, ∀ i' ∈ ({i, j} : Finset (Fin 6)), ∀ j' ∈ ({i, j} : Finset (Fin 6)),
      ∀ hij' : i' ≠ j', A * Matrix.SpecialLinearGroup.transvection hij' 1 =
        Matrix.SpecialLinearGroup.transvection hij' 1 * A := by
    intro A hA i' hi' j' hj' hij'
    apply hinj
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.1 (hPc hA) _ (hT i' j' hij' hi' hj')).symm
  have hQle := LinearPilot.le_blockSpecialLinear_sdiff_of_commute (N := Finset.univ)
    (T := ({i, j} : Finset (Fin 6))) (by rw [Finset.card_pair hij])
    (by rw [LinearPilot.blockSpecialLinear_univ]; exact le_top) hQperf hcomm
  rw [show (Finset.univ \ ({i, j} : Finset (Fin 6))) = ({i, j} : Finset (Fin 6))ᶜ from
    (Finset.compl_eq_univ_sdiff _).symm] at hQle
  rw [← hQP]
  exact Subgroup.map_mono hQle

theorem isSimpleGroup_map_blockSpecialLinear_two (hK : Nat.card K = 2) {i j : Fin 6}
    (hij : i ≠ j) :
    IsSimpleGroup ((blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map
        (slToAdjointE6 K)) ∧
      center ((blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map
        (slToAdjointE6 K)) = ⊥ ∧
      ⁅(blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map (slToAdjointE6 K),
        (blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map (slToAdjointE6 K)⁆ =
        (blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map (slToAdjointE6 K) := by
  set S : Finset (Fin 6) := ({i, j} : Finset (Fin 6))ᶜ with hS
  have hcard : S.card = 4 := by
    rw [hS, Finset.card_compl, Finset.card_pair hij, Fintype.card_fin]
  set B := blockSpecialLinear (K := K) S with hB
  have hinj := injective_slToAdjointE6_two hK
  let e1 : B ≃* B.map (slToAdjointE6 K) := B.equivMapOfInjective _ hinj
  let e2 : Matrix.SpecialLinearGroup S K ≃* B :=
    (MonoidHom.ofInjective (LinearPilot.blockEmbed_injective S)).trans
      (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed S))
  let e3 : Matrix.SpecialLinearGroup S K ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
    LinearPilot.reindexSpecialLinear (S.equivFin.trans (finCongr hcard))
  have hZ : center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
    eq_bot_iff.2 fun z hz => mem_bot.2
      (LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz)
  let e4 : Matrix.SpecialLinearGroup (Fin 4) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let E : B.map (slToAdjointE6 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    ((e1.symm.trans e2.symm).trans e3).trans e4
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) K) :=
    (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 4) (by norm_num)
      (Or.inl (by norm_num))).2.1
  have hS' : IsSimpleGroup (B.map (slToAdjointE6 K)) := E.isSimpleGroup
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 4) K) :=
    LinearPilot.isPerfect_specialLinearGroup_of_three_le_card (Fin 4) (by simp)
  have hperfB : ⁅(⊤ : Subgroup (B.map (slToAdjointE6 K))),
      (⊤ : Subgroup (B.map (slToAdjointE6 K)))⁆ = ⊤ := by
    have h : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K)),
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K))⁆ = ⊤ := hperfSL.commutator_eq_top
    have h2 := congrArg (Subgroup.map (((e1.symm.trans e2.symm).trans e3).symm.toMonoidHom)) h
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (((e1.symm.trans e2.symm).trans e3).symm.surjective)] at h2
  refine ⟨hS', @center_eq_bot_of_isSimpleGroup_of_commutator _ _ hS' hperfB, ?_⟩
  rw [← Subgroup.map_subtype_commutator, commutator_def, hperfB, ← MonoidHom.range_eq_map,
    range_subtype]

end Model

@[expose] def deltaPair : E6Neighbour → E6Neighbour → Fin 6 × Fin 6
  | high, six => (4, 5)
  | high, three => (1, 2)
  | six, high => (0, 5)
  | six, three => (2, 3)
  | three, high => (0, 5)
  | three, six => (1, 2)
  | _, _ => (0, 1)

theorem deltaPair_ne (N N' : E6Neighbour) : (deltaPair N N').1 ≠ (deltaPair N N').2 := by
  cases N <;> cases N' <;> decide

section Pairs

theorem weyl_smul_deltaPair {N N' : E6Neighbour} (h : N ≠ N') :
    N.weyl • a5Root (deltaPair N N').1 (deltaPair N N').2 = N'.root := by
  cases N <;> cases N' <;> first
    | exact absurd rfl h
    | (simp only [E6Neighbour.weyl, E6Neighbour.word, CoxeterSystem.wordProd_cons,
          CoxeterSystem.wordProd_nil, mul_one, one_smul, mul_smul, simple_smul, deltaPair,
          E6Neighbour.root]
       exact List.ofFn_injective (by decide +kernel))

end Pairs

section Overlap


variable {K : Type} [Field K]

theorem map_conj_rep_perpSpan {N N' : E6Neighbour} {δ : Fin (Tag.rank .E6) → ℤ}
    (hw : N.weyl • δ = N'.root) :
    ((rootSpan .E6 K (orthRoots (highRoot .E6) ∩ orthRoots δ)).subgroupOf
        (adjointGroup .E6 K)).map (MulAut.conj (N.rep K)).toMonoidHom = overlapSpan K N N' := by
  rw [map_conj_rep_subgroupOf_rootSpan N fun γ hγ => hγ.1.1, overlapSpan, overlapRoots,
    Set.image_inter (MulAction.injective N.weyl), image_smul_orthRoots, image_smul_orthRoots,
    weyl_smul_highRoot, hw]

theorem map_conj_rep_rootPair {N N' : E6Neighbour} {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (hw : N.weyl • δ = N'.root) :
    ((rootSubgroup .E6 K δ ⊔ rootSubgroup .E6 K (-δ)).subgroupOf (adjointGroup .E6 K)).map
        (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSubgroup .E6 K N'.root ⊔ rootSubgroup .E6 K (-N'.root)).subgroupOf
        (adjointGroup .E6 K) := by
  have hle : ∀ γ : Fin (Tag.rank .E6) → ℤ,
      rootSubgroup .E6 K γ ⊔ rootSubgroup .E6 K (-γ) ≤ adjointGroup .E6 K :=
    fun γ => sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [map_conj_map_subtype_E6, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hle _), inf_of_le_left (hle _), Subgroup.map_sup,
    map_conj_rep_rootSubgroup N hδ, map_conj_rep_rootSubgroup N (IsRoot.neg hδ), smul_neg, hw]

variable [Finite K] [CharP K 2]

theorem centralizer_rootPair_eq_levi (N' : E6Neighbour) :
    centralizer (((rootSubgroup .E6 K N'.root ⊔ rootSubgroup .E6 K (-N'.root)).subgroupOf
      (adjointGroup .E6 K) : Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) =
      N'.levi K := by
  have h1 : (posJ K).map (MulAut.conj (N'.rep K)).toMonoidHom =
      (rootSubgroup .E6 K N'.root ⊔ rootSubgroup .E6 K (-N'.root)).subgroupOf
        (adjointGroup .E6 K) := map_conj_rep_rootSL2 N'
  rw [← h1, F4Pilot.centralizer_map_mulAut, centralizer_posJ_eq_a5Levi, map_conj_rep_a5Levi]

theorem perfectCore_levi_inf_centralizer_eq_of_delta (hK : Nat.card K = 2)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = Nat.card K + 1)
    {N N' : E6Neighbour} {i j : Fin 6} (hij : i ≠ j) (hw : N.weyl • a5Root i j = N'.root) :
    perfectCore (N.levi K ⊓ centralizer
        ((A.map (MulAut.conj (N'.rep K)).toMonoidHom : Subgroup (adjointGroup .E6 K)) :
          Set (adjointGroup .E6 K))) = overlapSpan K N N' ∧
      IsSimpleGroup (overlapSpan K N N') ∧ center (overlapSpan K N N') = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : Nat.card A = 3 := by rw [hA, hK]
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA3
  set α := MulAut.conj (N.rep K) with hα
  set α' := MulAut.conj (N'.rep K) with hα'
  set X' := A.map α'.toMonoidHom with hX'
  set M := (blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))ᶜ).map (slToAdjointE6 K)
    with hMdef
  obtain ⟨hMs, hMZ, hMp⟩ := isSimpleGroup_map_blockSpecialLinear_two hK hij
  have hMov : M.map α.toMonoidHom = overlapSpan K N N' := by
    rw [hMdef, map_blockSpecialLinear_eq_perpSpan hij, map_conj_rep_perpSpan hw]
  let eM : M ≃* overlapSpan K N N' :=
    (M.equivMapOfInjective _ α.injective).trans (MulEquiv.subgroupCongr hMov)
  have hOs : IsSimpleGroup (overlapSpan K N N') := eM.symm.isSimpleGroup
  have hOZ : center (overlapSpan K N N') = ⊥ := F4Pilot.center_eq_bot_congr eM hMZ
  have hOp : ⁅overlapSpan K N N', overlapSpan K N N'⁆ = overlapSpan K N N' := by
    rw [← hMov, ← Subgroup.map_commutator, hMp]
  refine ⟨le_antisymm ?_ ?_, hOs, hOZ⟩
  ·
    obtain ⟨hcent, -, hAD⟩ := centralizer_nonsplit_E6 hAJ hA hcyc
    have hCX : centralizer (X' : Set (adjointGroup .E6 K)) = X' ⊔ N'.levi K := by
      rw [hX', F4Pilot.centralizer_map_mulAut, hcent, Subgroup.map_sup, map_conj_rep_a5Levi]
    have hX'D : X' ≤ centralizer (N'.levi K : Set (adjointGroup .E6 K)) := by
      rw [← map_conj_rep_a5Levi N', F4Pilot.centralizer_map_mulAut]
      exact Subgroup.map_mono hAD
    have hX'ab : X' ≤ centralizer (X' : Set (adjointGroup .E6 K)) :=
      F4Pilot.le_centralizer_self_of_isCyclic (F4Pilot.isCyclic_map_mulAut α' hcyc)
    set P := perfectCore (N.levi K ⊓ centralizer (X' : Set (adjointGroup .E6 K))) with hP
    have hPperf : ⁅P, P⁆ = P := perfectCore_perfect _
    have hPN : P ≤ N.levi K := (perfectCore_le _).trans inf_le_left
    have hPN' : P ≤ N'.levi K := by
      calc P = ⁅P, P⁆ := hPperf.symm
        _ ≤ ⁅X' ⊔ N'.levi K, X' ⊔ N'.levi K⁆ := by
          rw [← hCX]
          exact commutator_mono ((perfectCore_le _).trans inf_le_right)
            ((perfectCore_le _).trans inf_le_right)
        _ ≤ N'.levi K := commutator_sup_le_of_le_centralizer hX'ab hX'D
    rw [← map_conj_rep_a5Levi N] at hPN
    obtain ⟨P', hP'D, hP'P⟩ := F4Pilot.exists_le_map_eq_of_le_map α hPN
    have hP'perf : ⁅P', P'⁆ = P' := by
      apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
      rw [Subgroup.map_commutator, hP'P, hPperf]
    have hδ : IsRoot .E6 (a5Root i j) := isRoot_a5Root hij
    have hP'c : P' ≤ centralizer (((rootSubgroup .E6 K (a5Root i j) ⊔
        rootSubgroup .E6 K (-a5Root i j)).subgroupOf (adjointGroup .E6 K) :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) := by
      have h1 : P'.map α.toMonoidHom ≤ (centralizer (((rootSubgroup .E6 K (a5Root i j) ⊔
          rootSubgroup .E6 K (-a5Root i j)).subgroupOf (adjointGroup .E6 K) :
            Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))).map α.toMonoidHom := by
        rw [← F4Pilot.centralizer_map_mulAut, map_conj_rep_rootPair hδ hw,
          centralizer_rootPair_eq_levi, hP'P]
        exact hPN'
      exact (Subgroup.map_le_map_iff_of_injective α.injective).1 h1
    have hP'M : P' ≤ M := le_map_blockSpecialLinear_of_perfect hK hij hP'D hP'perf hP'c
    rw [← hP'P, ← hMov]
    exact Subgroup.map_mono hP'M
  ·
    refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (overlapSpan_le_levi N N') ?_) hOp
    obtain ⟨-, -, hAD⟩ := centralizer_nonsplit_E6 hAJ hA hcyc
    have hX'D : X' ≤ centralizer (N'.levi K : Set (adjointGroup .E6 K)) := by
      rw [← map_conj_rep_a5Levi N', F4Pilot.centralizer_map_mulAut]
      exact Subgroup.map_mono hAD
    have hON' : overlapSpan K N N' ≤ N'.levi K :=
      Subgroup.subgroupOf_mono _ (rootSpan_mono_E6 Set.inter_subset_right)
    exact hON'.trans (le_centralizer_iff.1 hX'D)

omit [Finite K] [CharP K 2] in
theorem e6TwoOverlapInput_holds : E6TwoOverlapInput K := by
  intro hK A hAJ hA N N' hNN
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  exact perfectCore_levi_inf_centralizer_eq_of_delta hK hAJ hA (deltaPair_ne N N')
    (weyl_smul_deltaPair hNN)

end Overlap

end CFSG.SeitzReduction.E6Pilot
