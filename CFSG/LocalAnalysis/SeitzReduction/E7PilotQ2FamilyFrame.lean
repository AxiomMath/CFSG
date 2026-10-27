module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FamilyTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)

local instance e7PilotQ2FamilyFrameNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

inductive PairFrame
  | hs
  | hf
  | sf
  deriving DecidableEq

namespace PairFrame

@[expose] def node : PairFrame → Fin (Tag.rank .E7)
  | hs => 2
  | hf => 5
  | sf => 0

@[expose] def nbr : PairFrame → Fin 2 → E7Neighbour
  | hs => ![.high, .seven]
  | hf => ![.high, .four]
  | sf => ![.seven, .four]

@[expose] def root : PairFrame → Fin 6 → Fin (Tag.rank .E7) → ℤ
  | hs => ![highRoot .E7, Pi.single 6 1, Pi.single 4 1, Pi.single 1 1, ![0, 1, 1, 2, 1, 0, 0],
      ![0, 1, 1, 2, 2, 2, 1]]
  | hf => ![highRoot .E7, Pi.single 3 1, ![0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1],
      ![0, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 2, 2, 1, 0]]
  | sf => ![Pi.single 6 1, Pi.single 3 1, ![0, 1, 0, 1, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0],
      ![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1]]

@[expose] def word : PairFrame → Fin 6 → List (Fin (Tag.rank .E7))
  | hs => ![E7Neighbour.high.word, E7Neighbour.seven.word,
      [5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0],
      [3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0],
      [0, 2, 3, 4, 1, 3, 2, 0]]
  | hf => ![E7Neighbour.high.word, E7Neighbour.four.word, [1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0],
      [2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0],
      [6, 5, 0, 2, 3, 4, 1, 3, 2, 0]]
  | sf => ![E7Neighbour.seven.word, E7Neighbour.four.word,
      [5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 4, 5, 3, 4, 1, 3, 2, 0], [1, 3, 2, 0],
      [4, 3, 2, 0]]

@[expose] def coverIdx (i : Fin 2) : Fin 6 := ⟨i, by omega⟩

theorem word_coverIdx (f : PairFrame) (i : Fin 2) : f.word (coverIdx i) = (f.nbr i).word := by
  cases f <;> fin_cases i <;> rfl

theorem root_coverIdx (f : PairFrame) (i : Fin 2) : f.root (coverIdx i) = (f.nbr i).root := by
  cases f <;> fin_cases i <;> rfl

theorem node_mem_nodes (f : PairFrame) (i : Fin 2) : f.node ∈ (f.nbr i).nodes := by
  cases f <;> fin_cases i <;> decide

theorem word_smul_highRoot_hs (m : Fin 6) :
    (coxeterSystem .E7).wordProd (hs.word m) • highRoot .E7 = hs.root m := by
  fin_cases m
  · exact E7Neighbour.weyl_smul_highRoot .high
  · exact E7Neighbour.weyl_smul_highRoot .seven
  all_goals
    simp only [word, root, Fin.reduceFinMk, Matrix.cons_val, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem word_smul_highRoot_hf (m : Fin 6) :
    (coxeterSystem .E7).wordProd (hf.word m) • highRoot .E7 = hf.root m := by
  fin_cases m
  · exact E7Neighbour.weyl_smul_highRoot .high
  · exact E7Neighbour.weyl_smul_highRoot .four
  all_goals
    simp only [word, root, Fin.reduceFinMk, Matrix.cons_val, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem word_smul_highRoot_sf (m : Fin 6) :
    (coxeterSystem .E7).wordProd (sf.word m) • highRoot .E7 = sf.root m := by
  fin_cases m
  · exact E7Neighbour.weyl_smul_highRoot .seven
  · exact E7Neighbour.weyl_smul_highRoot .four
  all_goals
    simp only [word, root, Fin.reduceFinMk, Matrix.cons_val, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem word_smul_highRoot (f : PairFrame) (m : Fin 6) :
    (coxeterSystem .E7).wordProd (f.word m) • highRoot .E7 = f.root m := by
  cases f
  exacts [word_smul_highRoot_hs m, word_smul_highRoot_hf m, word_smul_highRoot_sf m]

theorem isRoot_root (f : PairFrame) (m : Fin 6) :
    IsRoot .E7 (f.root m) := by
  rw [← word_smul_highRoot]
  exact IsRoot.smul (isRoot_highRoot .E7) _

theorem iform_root_single_node (f : PairFrame) (m : Fin 6) :
    iform (f.root m) (Pi.single f.node 1 : Fin (Tag.rank .E7) → ℤ) = 0 := by
  revert m
  cases f <;> decide +kernel

theorem iform_root_root (f : PairFrame) (m m' : Fin 6) :
    iform (f.root m) (f.root m') = if m = m' then 2 else 0 := by
  revert m m'
  cases f <;> decide +kernel

theorem basis_check (f : PairFrame) : ∀ i j : Fin (Tag.rank .E7),
    ∑ m : Fin 6, iform (f.root m) (Pi.single j 1) * iform (f.root m) (Pi.single i 1) =
      2 * iform (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single j 1) -
        iform (Pi.single f.node 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single j 1) *
          iform (Pi.single f.node 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single i 1) := by
  cases f <;> decide +kernel

theorem sum_iform_root
    (f : PairFrame) (v : Fin (Tag.rank .E7) → ℤ) (i : Fin (Tag.rank .E7)) :
    ∑ m : Fin 6, iform v (f.root m) * iform (f.root m) (Pi.single i 1) =
      2 * iform v (Pi.single i 1) -
        iform v (Pi.single f.node 1) *
          iform (Pi.single f.node 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single i 1) := by
  have hv : ∀ b : Fin (Tag.rank .E7) → ℤ, iform v b = ∑ j, v j * iform b (Pi.single j 1) :=
    fun b => by rw [iform_comm, F4Pilot.iform_eq_sum_mul_iform_single]
  have key : ∀ j : Fin (Tag.rank .E7), ∑ m : Fin 6, v j * iform (f.root m) (Pi.single j 1) *
      iform (f.root m) (Pi.single i 1) =
        2 * (v j * iform (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single j 1)) -
          v j * iform (Pi.single f.node 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single j 1) *
            iform (Pi.single f.node 1 : Fin (Tag.rank .E7) → ℤ) (Pi.single i 1) := by
    intro j
    have h := f.basis_check i j
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, h]
    ring
  simp only [hv]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => key j

theorem corootTuple_eq_prod
    {K : Type} [Field K] (f : PairFrame) {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : iform δ (Pi.single f.node 1) = 0) {c : Kˣ} (hc : c ^ 3 = 1) :
    corootTuple δ c = ∏ m : Fin 6, corootTuple (f.root m) (c ^ (2 * iform δ (f.root m))) := by
  funext i
  rw [Finset.prod_apply]
  simp only [corootTuple, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  have hsum : ∑ m : Fin 6, 2 * iform δ (f.root m) * iform (f.root m) (Pi.single i 1) =
      iform δ (Pi.single i 1) + 3 * iform δ (Pi.single i 1) := by
    have h := f.sum_iform_root δ i
    rw [hδ, zero_mul, sub_zero] at h
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, h]
    ring
  have hc3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc
  rw [hsum, zpow_add, zpow_mul, hc3, one_zpow, mul_one]

theorem conj_eq_of_forall_mem_centralizer
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 2)
    (f : PairFrame) {g : ModGL .E7 K}
    (hg : ∀ (m : Fin 6) (c : Kˣ),
      g ∈ centralizer ({(rootDiagUnit .E7 (corootTuple (f.root m) c))} : Set (ModGL .E7 K))) :
    ∀ a ∈ corootTupleSet (⊤ : Subgroup Kˣ) {f.node},
      rootDiagUnit .E7 a * g * (rootDiagUnit .E7 a)⁻¹ = g := by
  rintro a ⟨δ, -, hδJ, c, -, rfl⟩
  have hδ0 : iform δ (Pi.single f.node 1) = 0 := hδJ f.node (Finset.mem_singleton_self _)
  rw [f.corootTuple_eq_prod hδ0 (E8Pilot.pow_three_eq_one_of_natCard_eq_four hK c)]
  have hmem : (∏ m : Fin 6,
      corootTuple (f.root m) (c ^ (2 * iform δ (f.root m)))) ∈
        (centralizer ({g} : Set (ModGL .E7 K))).comap (rootDiagUnitHom .E7 K) := by
    refine Subgroup.prod_mem _ fun m _ => ?_
    have h := mem_centralizer_singleton_iff.1 (hg m (c ^ (2 * iform δ (f.root m))))
    exact mem_centralizer_singleton_iff.2 h.symm
  have h2 := mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hmem)
  change rootDiagUnitHom .E7 K _ * g * (rootDiagUnitHom .E7 K _)⁻¹ = g
  rw [h2, mul_inv_cancel_right]

end PairFrame

section Levi


variable {k : Type} [Field k] {K : Type} [Field K]

theorem rootSubgroup_le_centralizer_of_iform_eq_zero_E7 {F : Type} [Field F]
    {γ δ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (hδ : IsRoot .E7 δ) (h0 : iform γ δ = 0) :
    rootSubgroup .E7 F γ ≤ centralizer (rootSubgroup .E7 F δ : Set (ModGL .E7 F)) :=
  fun _ hx => mem_centralizer_iff.2 fun _ hy =>
    (EPilot.commute_of_iform_eq_zero (Or.inr (Or.inl rfl)) hγ hδ h0 hx hy).eq.symm

theorem PairFrame.rootSpan_amalgamRoots_node_le_centralizer_rootSL2 {F : Type} [Field F]
    (f : PairFrame) (m : Fin 6) :
    rootSpan .E7 F (amalgamRoots {f.node}) ≤ centralizer
      ((rootSubgroup .E7 F (f.root m) ⊔ rootSubgroup .E7 F (-f.root m) :
        Subgroup (ModGL .E7 F)) : Set (ModGL .E7 F)) := by
  refine iSup₂_le fun γ hγ => ?_
  have hγr := isRoot_of_mem_amalgamRoots hγ
  have h1 : iform (f.root m) γ = 0 := by
    obtain ⟨j, hj, rfl | rfl⟩ := hγ <;> rw [Finset.mem_singleton] at hj <;> subst hj
    · exact f.iform_root_single_node m
    · rw [iform_neg_right_E7, f.iform_root_single_node, neg_zero]
  have h2 : iform (-f.root m) γ = 0 := by
    rw [iform_comm, iform_neg_right_E7, iform_comm, h1, neg_zero]
  rw [le_centralizer_iff]
  exact sup_le (rootSubgroup_le_centralizer_of_iform_eq_zero_E7 (f.isRoot_root m) hγr h1)
    (rootSubgroup_le_centralizer_of_iform_eq_zero_E7 (IsRoot.neg (f.isRoot_root m)) hγr h2)

theorem perfectCore_levi_inf_frame_eq [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) {x : ModGL .E7 k}
    (hxJ : x ∈ EPilot.highRootSL2 .E7 k) (hx : orderOf x = 3) (f : PairFrame) (i : Fin 2) :
    perfectCore (((f.nbr i).levi K).map (adjointGroup .E7 K).subtype ⊓
      ⨅ (m : Fin 6) (_ : m ≠ PairFrame.coverIdx i), centralizer
        ({baseChangeGL ι (wordElt k (f.word m) * x * (wordElt k (f.word m))⁻¹)} :
          Set (ModGL .E7 K))) =
      rootSpan .E7 K (amalgamRoots {f.node}) := by
  have : Finite (ModGL .E7 K) := finite_modGL
  have hA3 : 3 ≤ Nat.card (⊤ : Subgroup Kˣ) :=
    F4Pilot.three_le_natCard_top_units (by rw [hK]; norm_num)
  refine le_antisymm ?_ ?_
  · set H := ((f.nbr i).levi K).map (adjointGroup .E7 K).subtype ⊓
      ⨅ (m : Fin 6) (_ : m ≠ PairFrame.coverIdx i), centralizer
        ({baseChangeGL ι (wordElt k (f.word m) * x * (wordElt k (f.word m))⁻¹)} :
          Set (ModGL .E7 K)) with hH
    set P := perfectCore H with hPdef
    have hPperf : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect H
    have hPH : P ≤ H := perfectCore_le H
    have hPlevi : P ≤ rootSpan .E7 K (orthRoots (f.nbr i).root) := by
      rw [← map_subtype_levi]
      exact hPH.trans inf_le_left
    have hPC : P ≤ adjointGroup .E7 K := hPlevi.trans (EPilot.rootSpan_le_adjointGroup' _)
    have hcent : ∀ g ∈ P, ∀ (m : Fin 6) (c : Kˣ), g ∈ centralizer
        ({(rootDiagUnit .E7 (corootTuple (f.root m) c))} : Set (ModGL .E7 K)) := by
      intro g hg m c
      by_cases hm : m = PairFrame.coverIdx i
      · subst hm
        rw [f.root_coverIdx]
        refine rootSpan_le_centralizer (corootTuple (f.nbr i).root c)
          (fun γ hγ => ⟨hγ.1, ?_⟩) (hPlevi hg)
        rw [rootChar_corootTuple, hγ.2, zpow_zero]
      · have hPk : P ≤ centralizer
            ({baseChangeGL ι (wordElt k (f.word m) * x * (wordElt k (f.word m))⁻¹)} :
              Set (ModGL .E7 K)) :=
          hPH.trans (inf_le_right.trans (iInf₂_le m hm))
        have h := mem_centralizer_corootTuple_of_perfect_of_le_centralizer_word_E7 hk hK ι hxJ hx
          (f.word m) hPperf hPC hPk hg c
        rwa [f.word_smul_highRoot] at h
    have h := perfectCore_le_rootSpan_amalgamRoots_of_forall_conj_eq hA3 (J := {f.node})
      (by simp) (H := P) fun g hg =>
        ⟨hPC hg, PairFrame.conj_eq_of_forall_mem_centralizer hK f (hcent g hg)⟩
    rwa [CFSG.Quasithin.perfectCore_eq_self_of_perfect hPperf] at h
  · refine le_perfectCore_of_perfect (le_inf ?_ (le_iInf₂ fun m _ => ?_))
      (commutator_rootSpan_amalgamRoots_eq_E7 hA3 {f.node})
    · rw [map_subtype_levi]
      exact rootSpan_mono_E7 (amalgamRoots_subset_orthRoots_iff_subset_nodes.2
        (Finset.singleton_subset_iff.2 (f.node_mem_nodes i)))
    · intro u hu
      rw [mem_centralizer_singleton_iff]
      have hy : baseChangeGL ι (wordElt k (f.word m) * x * (wordElt k (f.word m))⁻¹) ∈
          rootSubgroup .E7 K (f.root m) ⊔ rootSubgroup .E7 K (-f.root m) := by
        rw [map_mul, map_mul, map_inv, baseChangeGL_wordElt, ← f.word_smul_highRoot]
        exact conj_wordElt_mem_rootSL2_E7 (f.word m) (baseChangeGL_mem_highRootSL2_of_E7 ι hxJ)
      exact (mem_centralizer_iff.1
        (f.rootSpan_amalgamRoots_node_le_centralizer_rootSL2 m hu) _ hy).symm

end Levi

end CFSG.SeitzReduction.E7Pilot
