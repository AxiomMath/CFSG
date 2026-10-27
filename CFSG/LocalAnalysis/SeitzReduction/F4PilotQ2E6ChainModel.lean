module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6AlignChain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainRoots


public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear pairEmbed)
open CFSG.SeitzReduction.SymplecticPilot (zThreeSL)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat elt mat_elt)
open CFSG.Timmesfeld.LieEmbed (a5Root c3ToF4 c3ToF4_single)
open CFSG.Quasithin (perfectCore)
open CFSG.LieType.Ree (ReeTag)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

local instance f4PilotQ2E6ChainModelNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6ChainModelNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section SL

variable {K : Type} [Field K] {n : ℕ}

theorem commutator_mem_blockCompl_of_commute [CharP K 2] (hK : Nat.card K = 2) {a b : Fin n}
    (hab : a ≠ b) {g g' : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ centralizer ({pairEmbed hab (zThreeSL (K := K))} :
      Set (SpecialLinearGroup (Fin n) K)))
    (hg' : g' ∈ centralizer ({pairEmbed hab (zThreeSL (K := K))} :
      Set (SpecialLinearGroup (Fin n) K))) :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSpecialLinear ({a, b} : Finset (Fin n))ᶜ := by
  set c := pairEmbed hab (zThreeSL (K := K)) with hc
  have hcpow : ∀ i : ℤ, c ^ i ∈ blockSpecialLinear ({a, b} : Finset (Fin n)) := by
    intro i
    rw [← LinearPilot.range_pairEmbed hab, hc, ← map_zpow]
    exact ⟨_, rfl⟩
  have hdec : ∀ x ∈ centralizer ({c} : Set (SpecialLinearGroup (Fin n) K)),
      ∃ a' ∈ zpowers c, ∃ d ∈ blockSpecialLinear ({a, b} : Finset (Fin n))ᶜ, x = a' * d := by
    intro x hx
    have hx' : x * pairEmbed hab (zThreeSL (K := K)) = pairEmbed hab (zThreeSL (K := K)) * x :=
      mem_centralizer_singleton_iff.1 hx
    obtain ⟨i, y, hy, hxy⟩ :=
      SymplecticPilot.exists_eq_zpow_mul_of_commute_pairEmbed_zThree hK hab hx'
    exact ⟨c ^ i, zpow_mem (mem_zpowers c) i, y, hy, hxy⟩
  refine SymplecticPilot.commutator_mem_of_eq_mul (A := zpowers c) ?_ ?_ (hdec g hg)
    (hdec g' hg')
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.refl c).zpow_zpow i j
  · rintro _ ⟨i, rfl⟩ d hd
    exact LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right (hcpow i) hd

theorem le_blockCompl_of_perfect [CharP K 2] (hK : Nat.card K = 2) {a b : Fin n} (hab : a ≠ b)
    {P : Subgroup (SpecialLinearGroup (Fin n) K)} (hP : ⁅P, P⁆ = P)
    (hPc : P ≤ centralizer ({pairEmbed hab (zThreeSL (K := K))} :
      Set (SpecialLinearGroup (Fin n) K))) :
    P ≤ blockSpecialLinear ({a, b} : Finset (Fin n))ᶜ := by
  rw [← hP, Subgroup.commutator_le]
  intro g hg g' hg'
  rw [commutatorElement_def]
  exact commutator_mem_blockCompl_of_commute hK hab (hPc hg) (hPc hg')

theorem commutator_blockCompl_pair {a b : Fin 6} (hab : a ≠ b) :
    ⁅blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ,
        blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ⁆ =
      blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ := by
  have hcard : 3 ≤ Fintype.card (({a, b} : Finset (Fin 6))ᶜ : Finset (Fin 6)) := by
    rw [Fintype.card_coe, Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    norm_num
  have hperf : Group.IsPerfect
      (SpecialLinearGroup (({a, b} : Finset (Fin 6))ᶜ : Finset (Fin 6)) K) :=
    LinearPilot.isPerfect_specialLinearGroup_of_three_le_card _ hcard
  rw [← LinearPilot.range_blockEmbed, MonoidHom.range_eq_map, ← map_commutator,
    ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]

theorem eq_one_of_mem_center_SL_two (hK : Nat.card K = 2) {m : ℕ} (hm : m ≠ 0)
    {g : SpecialLinearGroup (Fin m) K} (hg : g ∈ center (SpecialLinearGroup (Fin m) K)) :
    g = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  have hr1 : r = 1 := by
    rcases SymplecticPilot.eq_zero_or_eq_one_of_natCard_two hK r with h | h
    · rw [h, Fintype.card_fin, zero_pow hm] at hr
      exact absurd hr zero_ne_one
    · exact h
  apply Subtype.ext
  rw [← hrg, hr1, map_one]
  rfl

theorem a5Root_graphSwapPerm_zero_one :
    a5Root (graphSwapPerm.symm 0) (graphSwapPerm.symm 1) = Pi.single 0 1 ∧
      a5Root (graphSwapPerm.symm 1) (graphSwapPerm.symm 0) = -Pi.single 0 1 := by
  decide +kernel

end SL

section Param


@[expose] noncomputable def chainZ (K : Type) [Field K] (β : Fin (Tag.rank .F4) → ℤ) :
    adjointGroup .F4 K :=
  Adjoint.f4Par K β 1 * Adjoint.f4Par K (-β) 1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem pairEmbed_zThreeSL_eq {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    pairEmbed hab (zThreeSL (K := K)) =
      SpecialLinearGroup.transvection hab 1 * SpecialLinearGroup.transvection hab.symm 1 := by
  rw [zThreeSL_eq_sl2Upper_mul_sl2Lower, map_mul, SymplecticPilot.pairEmbed_sl2Upper,
    SymplecticPilot.pairEmbed_sl2Lower]

@[expose] noncomputable def chainSL6 (ΦA : e6ScLevi K e6A5Nodes →* G) :
    SpecialLinearGroup (Fin 6) K →* G :=
  ΦA.comp (graphParamEquiv K (RingEquiv.refl K)).toMonoidHom

theorem chainSL6_apply (ΦA : e6ScLevi K e6A5Nodes →* G) (g : SpecialLinearGroup (Fin 6) K) :
    chainSL6 ΦA g = ΦA (graphParamEquiv K (RingEquiv.refl K) g) :=
  rfl

theorem chainSL6_sp6ToSL6 {e : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hn : IsLeviNormalizedA e ΦA) (s : StatedSp 3 K) :
    chainSL6 ΦA (sp6ToSL6 s) = levi6Hom e (RingEquiv.refl K) s :=
  hn s

theorem chainSL6_sp6ToSL6_x {e : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hn : IsLeviNormalizedA e ΦA) (γ : Fin 3 → ℤ) (c : K) :
    chainSL6 ΦA (sp6ToSL6 (Sp.x 3 K γ c)) =
      ((e.symm (Adjoint.f4Par K (c3ToF4 γ) c) : L) : G) := by
  rw [chainSL6_sp6ToSL6 hn, levi6Hom_refl_x]

theorem chainSL6_injective (hK : Nat.card K = 2) {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hker : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes)) : Function.Injective (chainSL6 ΦA) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set Θ := graphParamEquiv K (RingEquiv.refl K) with hΘ
  have hc : Θ x ∈ center (e6ScLevi K e6A5Nodes) := hker (MonoidHom.mem_ker.2 hx)
  refine eq_one_of_mem_center_SL_two hK (by norm_num) ?_
  rw [mem_center_iff]
  intro y
  apply Θ.injective
  rw [map_mul, map_mul]
  exact mem_center_iff.1 hc (Θ y)

theorem chainSL6_transvection (ΦA : e6ScLevi K e6A5Nodes →* G) {i j : Fin 6} (hij : i ≠ j)
    (c : K) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : a5Root (graphSwapPerm.symm i) (graphSwapPerm.symm j) = γ)
    (hx : e6Data_valid.xm K γ c ∈ e6ScLevi K e6A5Nodes) :
    chainSL6 ΦA (SpecialLinearGroup.transvection hij c) = ΦA ⟨_, hx⟩ := by
  rw [chainSL6_apply]
  congr 1
  apply Subtype.ext
  rw [coe_graphParamEquiv, graphParamHom_transvection, hγ]
  rfl

theorem commute_of_mem_chainBlocks {ΦA : e6ScLevi K e6A5Nodes →* G} {a b : Fin 6} {x y : G}
    (hx : x ∈ (blockSpecialLinear ({a, b} : Finset (Fin 6))).map (chainSL6 ΦA))
    (hy : y ∈ (blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ).map (chainSL6 ΦA)) :
    Commute x y := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right hu hv).map _

theorem le_centralizerPerfectCore_chain {e : L ≃* adjointGroup .F4 K}
    {ΦA : e6ScLevi K e6A5Nodes →* G} {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀)) {a b : Fin 6} (hab : a ≠ b)
    {Z : Subgroup G}
    (hZ : Z ≤ (blockSpecialLinear ({a, b} : Finset (Fin 6))).map (chainSL6 ΦA)) :
    (blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ).map (chainSL6 ΦA) ≤
      centralizerPerfectCore (subgroupToG e X₀ ⊔ Z) := by
  refine le_centralizerPerfectCore_sup ?_ ?_ ?_
  · rw [← Subgroup.map_commutator, commutator_blockCompl_pair hab]
  · rintro _ ⟨x, -, rfl⟩
    have hx : chainSL6 ΦA x ∈ ΦA.range := ⟨_, rfl⟩
    rw [hr] at hx
    exact centralizerPerfectCore_le_centralizer _ hx
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hZ hz
    rw [← map_mul, ← map_mul,
      (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right hy hx).eq]

theorem centralizerPerfectCore_chain_le (hK : Nat.card K = 2) {e : L ≃* adjointGroup .F4 K}
    {ΦA : e6ScLevi K e6A5Nodes →* G} {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hinj : Function.Injective (chainSL6 ΦA)) {a b : Fin 6} (hab : a ≠ b) {Z : Subgroup G}
    (hcZ : chainSL6 ΦA (pairEmbed hab (zThreeSL (K := K))) ∈ Z) :
    centralizerPerfectCore (subgroupToG e X₀ ⊔ Z) ≤
      (blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ).map (chainSL6 ΦA) := by
  set E := centralizerPerfectCore (subgroupToG e X₀ ⊔ Z) with hE
  have hEle : E ≤ (chainSL6 ΦA).range := by
    intro y hy
    have hy' : y ∈ ΦA.range := by
      rw [hr]
      exact centralizerPerfectCore_anti le_sup_left hy
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨(graphParamEquiv K (RingEquiv.refl K)).symm x, by
      rw [chainSL6_apply, MulEquiv.apply_symm_apply]⟩
  set P := E.comap (chainSL6 ΦA) with hP
  have hPE : P.map (chainSL6 ΦA) = E := Subgroup.map_comap_eq_self hEle
  have hPP : ⁅P, P⁆ = P := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hPE]
    exact commutator_centralizerPerfectCore _
  have hPc : P ≤ centralizer ({pairEmbed hab (zThreeSL (K := K))} :
      Set (SpecialLinearGroup (Fin 6) K)) := by
    intro m hm
    rw [mem_centralizer_singleton_iff]
    apply hinj
    rw [map_mul, map_mul]
    have h1 : chainSL6 ΦA m ∈ centralizer (Z : Set G) :=
      centralizerPerfectCore_le_centralizer_of_le le_sup_right (Subgroup.mem_comap.1 hm)
    exact (mem_centralizer_iff.1 h1 _ hcZ).symm
  rw [← hPE]
  exact Subgroup.map_mono (le_blockCompl_of_perfect hK hab hPP hPc)

theorem sp_x_root221 (c : K) :
    Sp.x 3 K ![2, 2, 1] c = elt (.positiveLong 0) c :=
  Sp.x_eq (by decide) c

theorem sp_x_neg_root221 (c : K) :
    Sp.x 3 K (-![2, 2, 1]) c = elt (.negativeLong 0) c :=
  Sp.x_eq (by decide) c

theorem mat_sp_x_root221 (c : K) :
    mat 3 K (Sp.x 3 K ![2, 2, 1] c) = 1 + c • single (.inl 0) (.inr 0) 1 := by
  rw [sp_x_root221, mat_elt]
  rfl

theorem mat_sp_x_neg_root221 (c : K) :
    mat 3 K (Sp.x 3 K (-![2, 2, 1]) c) = 1 + c • single (.inr 0) (.inl 0) 1 := by
  rw [sp_x_neg_root221, mat_elt]
  rfl

theorem sp6ToSL6_x_root221 (c : K) :
    sp6ToSL6 (Sp.x 3 K ![2, 2, 1] c) =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide) c := by
  apply Subtype.ext
  rw [coe_sp6ToSL6, mat_sp_x_root221, SpecialLinearGroup.transvection_coe, map_add, map_one,
    map_smul, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv,
    smul_single, smul_eq_mul, mul_one]
  rfl

theorem sp6ToSL6_x_neg_root221 (c : K) :
    sp6ToSL6 (Sp.x 3 K (-![2, 2, 1]) c) =
      SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 0 by decide) c := by
  apply Subtype.ext
  rw [coe_sp6ToSL6, mat_sp_x_neg_root221, SpecialLinearGroup.transvection_coe, map_add, map_one,
    map_smul, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv,
    smul_single, smul_eq_mul, mul_one]
  rfl

omit [Finite K] [CharP K 2] in
theorem c3ToF4_root221 : c3ToF4 ![2, 2, 1] = rootE1mE2Align := by
  decide

theorem isRoot_rootE1mE2Align : IsRoot .F4 rootE1mE2Align :=
  isRoot_root0122

section Generic

variable {e : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G} {a b : Fin 6}
  (hab : a ≠ b) {β : Fin (Tag.rank .F4) → ℤ}

include hab in
theorem subgroupToG_rootSL2_le_chainBlock (hβ : IsRoot .F4 β)
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G)) :
    subgroupToG e (rootSL2 K β) ≤
      (blockSpecialLinear ({a, b} : Finset (Fin 6))).map (chainSL6 ΦA) := by
  rw [rootSL2_eq_sup hβ, subgroupToG, Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff hβ l).1 hl
    exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hab (by simp) (by simp) c, hx c⟩
  · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (IsRoot.neg hβ) l).1 hl
    exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hab.symm (by simp) (by simp) c,
      hx' c⟩

include hab in
theorem chainSL6_pairEmbed_eq
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G)) :
    chainSL6 ΦA (pairEmbed hab (zThreeSL (K := K))) = ((e.symm (chainZ K β) : L) : G) := by
  rw [pairEmbed_zThreeSL_eq, map_mul, hx 1, hx' 1, chainZ, map_mul, Subgroup.coe_mul]

omit [Finite K] [CharP K 2] in
theorem zpowers_chainZ_le (hβ : IsRoot .F4 β) : zpowers (chainZ K β) ≤ rootSL2 K β := by
  rw [zpowers_le, rootSL2_eq_sup hβ]
  exact mul_mem (mem_sup_left (Adjoint.xPar_mem hβ 1))
    (mem_sup_right (Adjoint.xPar_mem (IsRoot.neg hβ) 1))

include hab in
theorem card_zpowers_chainZ (hinj : Function.Injective (chainSL6 ΦA))
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G)) :
    Nat.card (zpowers (chainZ K β)) = 3 := by
  rw [Nat.card_zpowers]
  have h1 : orderOf (chainZ K β) = orderOf (((e.symm (chainZ K β) : L) : G)) :=
    (orderOf_injective (L.subtype.comp e.symm.toMonoidHom)
      (L.subtype_injective.comp e.symm.injective) _).symm
  rw [h1, ← chainSL6_pairEmbed_eq hab hx hx', orderOf_injective _ hinj,
    orderOf_injective _ (LinearPilot.pairEmbed_injective hab), SymplecticPilot.orderOf_zThreeSL]

include hab in
theorem subgroupToG_zpowers_chainZ_le (hβ : IsRoot .F4 β)
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G)) :
    subgroupToG e (zpowers (chainZ K β)) ≤
      (blockSpecialLinear ({a, b} : Finset (Fin 6))).map (chainSL6 ΦA) :=
  (Subgroup.map_mono (Subgroup.map_mono (zpowers_chainZ_le hβ))).trans
    (subgroupToG_rootSL2_le_chainBlock hab hβ hx hx')

include hab in
theorem chainSL6_pairEmbed_mem
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G)) :
    chainSL6 ΦA (pairEmbed hab (zThreeSL (K := K))) ∈ subgroupToG e (zpowers (chainZ K β)) := by
  rw [chainSL6_pairEmbed_eq hab hx hx']
  exact ⟨_, ⟨chainZ K β, mem_zpowers _, rfl⟩, rfl⟩

include hab in
theorem commute_rootSL2_centralizerPerfectCore_chain (hK : Nat.card K = 2)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hinj : Function.Injective (chainSL6 ΦA)) (hβ : IsRoot .F4 β)
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G)) :
    ∀ l ∈ rootSL2 K β, ∀ y ∈ centralizerPerfectCore
        (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))),
      Commute ((e.symm l : L) : G) y := fun l hl _ hy =>
  commute_of_mem_chainBlocks
    (subgroupToG_rootSL2_le_chainBlock hab hβ hx hx' ⟨_, ⟨l, hl, rfl⟩, rfl⟩)
    (centralizerPerfectCore_chain_le hK hr hinj hab (chainSL6_pairEmbed_mem hab hx hx') hy)

include hab in
theorem le_centralizerPerfectCore_chain_of_le {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀)) (hβ : IsRoot .F4 β)
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G))
    {S : Subgroup G}
    (hS : S ≤ (blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ).map (chainSL6 ΦA)) :
    S ≤ centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))) :=
  hS.trans (le_centralizerPerfectCore_chain hr hab (subgroupToG_zpowers_chainZ_le hab hβ hx hx'))

include hab in
theorem rootSL2_le_alignedSubgroup_of_le (hβ : IsRoot .F4 β)
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G))
    {S : Subgroup G}
    (hS : S ≤ (blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ).map (chainSL6 ΦA)) :
    rootSL2 K β ≤ alignedSubgroup e S := by
  intro l hl
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  intro y hy
  exact (commute_of_mem_chainBlocks
    (subgroupToG_rootSL2_le_chainBlock hab hβ hx hx' ⟨_, ⟨l, hl, rfl⟩, rfl⟩) (hS hy)).symm.eq

end Generic

section Instances

variable {e : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}

theorem f4RootPairAlign_eq_rootSL2 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    f4RootPairAlign K γ = rootSL2 K γ :=
  (rootSL2_eq_sup hγ).symm

theorem chainSL6_transvection_two_five (hn : IsLeviNormalizedA e ΦA) (c : K) :
    chainSL6 ΦA (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide) c) =
      ((e.symm (Adjoint.f4Par K (Pi.single 1 1) c) : L) : G) := by
  rw [← sp6ToSL6_x_single_two, chainSL6_sp6ToSL6_x hn, c3ToF4_single]
  rfl

theorem chainSL6_transvection_five_two (hn : IsLeviNormalizedA e ΦA) (c : K) :
    chainSL6 ΦA (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide).symm c) =
      ((e.symm (Adjoint.f4Par K (-Pi.single 1 1) c) : L) : G) := by
  rw [← sp6ToSL6_x_neg_single_two, chainSL6_sp6ToSL6_x hn, map_neg, c3ToF4_single]
  rfl

theorem chainSL6_transvection_zero_three (hn : IsLeviNormalizedA e ΦA) (c : K) :
    chainSL6 ΦA (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide) c) =
      ((e.symm (Adjoint.f4Par K rootE1mE2Align c) : L) : G) := by
  rw [← sp6ToSL6_x_root221, chainSL6_sp6ToSL6_x hn, c3ToF4_root221]

theorem chainSL6_transvection_three_zero (hn : IsLeviNormalizedA e ΦA) (c : K) :
    chainSL6 ΦA (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide).symm c) =
      ((e.symm (Adjoint.f4Par K (-rootE1mE2Align) c) : L) : G) := by
  rw [← sp6ToSL6_x_neg_root221, chainSL6_sp6ToSL6_x hn, map_neg, c3ToF4_root221]

theorem range_scLeviRestrict_zero_le (ΦA : e6ScLevi K e6A5Nodes →* G) :
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range ≤
      (blockSpecialLinear ({2, 5} : Finset (Fin 6))ᶜ).map (chainSL6 ΦA) := by
  rintro _ ⟨y, rfl⟩
  refine e6ScLevi_map_mem _ _ (fun j hj γ hγ c hx => ?_) y
  rw [Finset.mem_singleton] at hj
  subst hj
  rw [scLeviRestrict_apply]
  rcases hγ with rfl | rfl
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (0 : Fin 6) ≠ 1 by decide)
      (by decide) (by decide) c, chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_zero_one.1 _⟩
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (1 : Fin 6) ≠ 0 by decide)
      (by decide) (by decide) c, chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_zero_one.2 _⟩

theorem range_scLeviRestrict_two_le (ΦA : e6ScLevi K e6A5Nodes →* G) :
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range ≤
      (blockSpecialLinear ({0, 3} : Finset (Fin 6))ᶜ).map (chainSL6 ΦA) := by
  rintro _ ⟨y, rfl⟩
  refine e6ScLevi_map_mem _ _ (fun j hj γ hγ c hx => ?_) y
  rw [Finset.mem_singleton] at hj
  subst hj
  rw [scLeviRestrict_apply]
  rcases hγ with rfl | rfl
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (1 : Fin 6) ≠ 2 by decide)
      (by decide) (by decide) c,
      chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_check.2.2.1 _⟩
  · exact ⟨_, LinearPilot.transvection_mem_blockSpecialLinear (show (2 : Fin 6) ≠ 1 by decide)
      (by decide) (by decide) c,
      chainSL6_transvection ΦA _ c a5Root_graphSwapPerm_check.2.2.2.2.1 _⟩

theorem f4RootPairAlign_a2_le_aligned_zero (hn : IsLeviNormalizedA e ΦA) :
    f4RootPairAlign K (Pi.single 1 1) ≤ alignedSubgroup e
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range := by
  rw [f4RootPairAlign_eq_rootSL2 (isRoot_single _ 1)]
  exact rootSL2_le_alignedSubgroup_of_le (show (2 : Fin 6) ≠ 5 by decide) (isRoot_single _ 1)
    (chainSL6_transvection_two_five hn) (chainSL6_transvection_five_two hn)
    (range_scLeviRestrict_zero_le ΦA)

theorem f4RootPairAlign_e1e2_le_aligned_two (hn : IsLeviNormalizedA e ΦA) :
    f4RootPairAlign K rootE1mE2Align ≤ alignedSubgroup e
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range := by
  rw [f4RootPairAlign_eq_rootSL2 isRoot_rootE1mE2Align]
  exact rootSL2_le_alignedSubgroup_of_le (show (0 : Fin 6) ≠ 3 by decide) isRoot_rootE1mE2Align
    (chainSL6_transvection_zero_three hn) (chainSL6_transvection_three_zero hn)
    (range_scLeviRestrict_two_le ΦA)

end Instances

end Param

end CFSG.SeitzReduction.F4Pilot
